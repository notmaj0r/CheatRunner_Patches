#!/usr/bin/env python3
"""Build the CheatRunner patch for the Japanese PS5 release of Baldur's Gate 3.

The game asks the system for userDefinedParam1 through sceAppContentAppParamGetInt(1, &v).
The Japanese edition has 3 there, and every Japanese-edition check in the game is built on
that value. Newer builds inline those checks in dozens of places, so patching one compare
no longer works. This script hooks the import instead:

  * finds the import stub for sceAppContentAppParamGetInt by its NID (99b82IKXpH4),
  * puts a 17-byte routine in an int3 padding gap: for param 1 it returns an error, as if
    the key were missing; every other param goes to the real function,
  * points the stub at that routine.

Nothing here depends on code layout, so the same script works across game versions. The
addresses it writes are still fixed per build: PS5 game code is execute-only, so CheatRunner
cannot pattern-scan it on the console. Run this again for each game version.

Usage:
    python3 make_bg3_jp_patch.py path/to/eboot.bin path/to/sce_sys/param.json [-o PPSA18463.xml]

Needs only the Python standard library.
"""
import argparse, base64, hashlib, json, re, struct, sys

IMAGE_BASE = 0x400000
SELF_MAGIC = b"\x4f\x15\x3d\x1d"
GETINT_NAME = "sceAppContentAppParamGetInt"
NID_SUFFIX = bytes.fromhex("518D64A635DED8C1E6B039B1C3E55230")
FAKE_ERROR = 0x80D90002           # any non-zero value; callers only test for != 0
DT_STRTAB, DT_SYMTAB, DT_PLTRELSZ, DT_JMPREL = 5, 6, 2, 0x17


def nid(name):
    h = hashlib.sha1(name.encode() + NID_SUFFIX).digest()
    return base64.b64encode(struct.pack(">Q", struct.unpack("<Q", h[:8])[0])).decode()[:11].replace("/", "-")


class Image:
    """Maps virtual addresses to file offsets for a decrypted SELF or plain ELF."""

    def __init__(self, d):
        self.d = d
        if d[:4] == SELF_MAGIC:
            n = struct.unpack_from("<H", d, 0x18)[0]
            entries = [struct.unpack_from("<4Q", d, 0x20 + i * 32) for i in range(n)]
            elf = 0x20 + n * 32
        elif d[:4] == b"\x7fELF":
            entries, elf = None, 0
        else:
            sys.exit("Not a decrypted eboot.bin (no SELF or ELF header). Use the decrypted/fake-signed file.")
        if d[elf:elf + 4] != b"\x7fELF":
            sys.exit("No ELF header inside the SELF. Is this file still encrypted?")
        phoff = struct.unpack_from("<Q", d, elf + 0x20)[0]
        phnum = struct.unpack_from("<H", d, elf + 0x38)[0]
        self.loads, self.dynamic = [], None     # loads: (file_off, va, size, elf_off, executable)
        phs = [struct.unpack_from("<IIQQQQQQ", d, elf + phoff + i * 56) for i in range(phnum)]
        for i, (p_type, p_flags, p_off, p_va, _, p_filesz, _, _) in enumerate(phs):
            if p_type == 2:
                self.dynamic = (p_va, p_filesz)
            if p_type != 1 or not p_filesz:
                continue
            if entries is None:
                self.loads.append((p_off, p_va, p_filesz, p_off, bool(p_flags & 1)))
                continue
            for props, off, filesz, _ in entries:   # SELF: the block holding segment i
                if (props >> 20) & 0xFFF == i and (props >> 11) & 1:
                    if (props >> 1) & 1 or (props >> 3) & 1:
                        sys.exit("Segment %d is encrypted or compressed. Use a decrypted eboot.bin." % i)
                    self.loads.append((off, p_va, filesz, p_off, bool(p_flags & 1)))
        if not self.dynamic:
            sys.exit("No PT_DYNAMIC segment; cannot resolve imports.")
        text = [s for s in self.loads if s[4]]
        if len(text) != 1:
            sys.exit("Expected one executable segment, found %d." % len(text))
        self.text_off, self.text_va, self.text_size = text[0][:3]

    def off(self, va):
        for f_off, s_va, size, _, _ in self.loads:
            if s_va <= va < s_va + size:
                return f_off + va - s_va
        sys.exit("Address %#x is not in any loaded segment." % va)

    def text(self):
        return self.d[self.text_off:self.text_off + self.text_size]


def find_got_slot(img, name):
    d = img.d
    tags = {}
    dyn = img.off(img.dynamic[0])
    for i in range(img.dynamic[1] // 16):
        t, v = struct.unpack_from("<qQ", d, dyn + i * 16)
        if t == 0:
            break
        tags.setdefault(t, v)
    try:
        jmprel, relsz, symtab, strtab = (tags[t] for t in (DT_JMPREL, DT_PLTRELSZ, DT_SYMTAB, DT_STRTAB))
    except KeyError:
        sys.exit("Dynamic section is missing JMPREL/SYMTAB/STRTAB.")
    want = nid(name).encode() + b"#"
    rel, sym, stb = img.off(jmprel), img.off(symtab), img.off(strtab)
    slots = []
    for i in range(relsz // 24):
        r_off, info, _ = struct.unpack_from("<QQq", d, rel + i * 24)
        st_name = struct.unpack_from("<I", d, sym + (info >> 32) * 24)[0]
        if d[stb + st_name:stb + st_name + len(want)] == want:
            slots.append(r_off)
    if len(slots) != 1:
        sys.exit("Expected one import of %s, found %d." % (name, len(slots)))
    return slots[0]


def find_stub(img, got):
    t, base = img.text(), img.text_va
    stubs = [m.start() for m in re.finditer(b"\xff\x25", t)
             if base + m.start() + 6 + struct.unpack_from("<i", t, m.start() + 2)[0] == got]
    if len(stubs) != 1:
        sys.exit("Expected one import stub for the GOT slot %#x, found %d." % (got, len(stubs)))
    return base + stubs[0]


def count_callers(img, stub):
    t, base = img.text(), img.text_va
    n = 0
    for m in re.finditer(b"\xe8", t):
        p = m.start()
        if p + 5 <= len(t) and base + p + 5 + struct.unpack_from("<i", t, p + 1)[0] == stub:
            n += 1
    return n


def find_cave(img, size, near):
    """An int3 padding run after a ret / ud2 / jmp, nearest to `near`, with room for `size` bytes."""
    t, base = img.text(), img.text_va
    best = None
    for m in re.finditer(rb"\xcc{24,}", t):
        s, e = m.start(), m.end()
        if not (t[s - 1] == 0xC3 or t[s - 2:s] == b"\x0f\x0b" or t[s - 5] == 0xE9 or t[s - 2] == 0xEB):
            continue
        c = (s + 1 + 15) & ~15          # keep at least one int3 before the routine
        if c + size <= e:
            va = base + c
            if best is None or abs(va - near) < abs(best - near):
                best = va
    if best is None:
        sys.exit("No int3 padding gap big enough for the hook routine.")
    return best


def build(img):
    got = find_got_slot(img, GETINT_NAME)
    stub = find_stub(img, got)
    callers = count_callers(img, stub)
    cave = find_cave(img, 17, stub)
    # cave:     cmp edi, 1 / je +6 / jmp [rip+GOT] / mov eax, FAKE_ERROR / ret
    routine = (b"\x83\xff\x01" + b"\x74\x06"
               + b"\xff\x25" + struct.pack("<i", got - (cave + 11))
               + b"\xb8" + struct.pack("<I", FAKE_ERROR) + b"\xc3")
    # stub:     jmp rel32 cave / nop   (replaces the 6-byte jmp [rip+GOT])
    hook = b"\xe9" + struct.pack("<i", cave - (stub + 5)) + b"\x90"
    old_stub = img.d[img.off(stub):img.off(stub) + 6]
    return dict(got=got, stub=stub, cave=cave, callers=callers, routine=routine, hook=hook, old_stub=old_stub)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("eboot")
    ap.add_argument("param_json", help="sce_sys/param.json from the same install (gives TitleID and AppVer)")
    ap.add_argument("-o", "--output", default="PPSA18463.xml")
    a = ap.parse_args()

    img = Image(open(a.eboot, "rb").read())
    p = build(img)

    pj = json.load(open(a.param_json, encoding="utf-8"))
    title_id = pj.get("titleId", "PPSA18463")
    app_ver = pj.get("contentVersion", "")
    if not app_ver:
        sys.exit("param.json has no contentVersion.")
    udp1 = pj.get("userDefinedParam1")
    if udp1 != 3:
        print("Note: userDefinedParam1 is %r, not 3. The Japanese-edition checks only fire on 3, "
              "so this install may not need the patch." % udp1)

    xml = f"""<?xml version="1.0" encoding="utf-8"?>
<Patch>
    <TitleID>
        <ID>{title_id}</ID>
    </TitleID>
    <!--
      Generated by make_bg3_jp_patch.py for contentVersion {app_ver}.
      Hooks {GETINT_NAME} (NID {nid(GETINT_NAME)}, import stub at module offset {p['stub']:#x},
      {p['callers']} call sites). For param 1 (userDefinedParam1) the hook returns an error, as if the
      key were missing, so no Japanese-edition check fires. Other params go to the real function.
      Module offsets + ImageBase {IMAGE_BASE:#x} = addresses below.
    -->
    <Metadata Title="Baldur's Gate 3"
              Name="Disable Japanese content restrictions"
              Note="Built for contentVersion {app_ver}. Turn nudity and explicit scenes on in Options after enabling."
              Author="cevenkadir"
              PatchVer="2.0"
              AppVer="{app_ver}"
              AppElf="eboot.bin"
              ImageBase="{IMAGE_BASE:#x}">
        <PatchList>
            <!-- module offset {p['cave']:#x}: int3 padding -> hook routine (cmp edi,1 / je / jmp [GOT] / mov eax,err / ret) -->
            <Line Type="bytes" Address="{IMAGE_BASE + p['cave']:#010x}" Value="{p['routine'].hex()}"/>
            <!-- module offset {p['stub']:#x}: {p['old_stub'].hex()} (jmp [GOT]) -> jmp hook routine -->
            <Line Type="bytes" Address="{IMAGE_BASE + p['stub']:#010x}" Value="{p['hook'].hex()}"/>
        </PatchList>
    </Metadata>
</Patch>
"""
    open(a.output, "w", encoding="utf-8").write(xml)
    print(f"{GETINT_NAME}: GOT {p['got']:#x}, stub {p['stub']:#x} ({p['callers']} callers), hook routine at {p['cave']:#x}.")
    print(f"Wrote {a.output} (AppVer {app_ver}).")


if __name__ == "__main__":
    main()
