#!/usr/bin/env python3
"""Differential tests for the Proven Commons WebSocket first slice.

Compares the Lean implementation against an independent Python
implementation of RFC 6455 section 5, written from the RFC text, and
against the worked examples in section 5.7. Run from anywhere:

    python3 tests/run_tests.py

It builds the Lean project if the executable is missing, runs all
cases through one batch call, writes `tests/TEST-RESULTS.md`, and
exits non-zero if any case fails.
"""

import os
import random
import subprocess
import sys
from pathlib import Path

PROJECT_DIR = Path(__file__).resolve().parent.parent
EXE = PROJECT_DIR / ".lake" / "build" / "bin" / "websocket"
RESULTS = PROJECT_DIR / "tests" / "TEST-RESULTS.md"
SEED = 20261025

checks = 0
failures = []


def check(name, ok, detail=""):
    global checks
    checks += 1
    if not ok:
        failures.append(f"{name}: {detail}")
        print(f"FAIL {name}: {detail}")


def hex_or_dash(bs):
    return bs.hex() if bs else "-"


def py_enc(fin, opcode, masked, key, payload):
    """Encode one frame, minimal length form, as RFC 6455 section 5."""
    b0 = (0x80 if fin else 0) | opcode
    n = len(payload)
    if n < 126:
        ind, ext = n, b""
    elif n < 65536:
        ind, ext = 126, n.to_bytes(2, "big")
    else:
        ind, ext = 127, n.to_bytes(8, "big")
    b1 = (0x80 if masked else 0) | ind
    out = bytes([b0, b1]) + ext
    if masked:
        out += key
        out += bytes(b ^ key[i % 4] for i, b in enumerate(payload))
    else:
        out += payload
    return out


def py_dec(data):
    """Decode one frame, or None when the shape breaks a rule."""
    if len(data) < 2:
        return None
    b0, b1 = data[0], data[1]
    fin = 1 if b0 & 0x80 else 0
    if b0 & 0x70:
        return None
    opcode = b0 & 0x0F
    if opcode not in (0, 1, 2, 8, 9, 10):
        return None
    masked = 1 if b1 & 0x80 else 0
    ind = b1 & 0x7F
    pos = 2
    if ind < 126:
        n = ind
    elif ind == 126:
        if len(data) < pos + 2:
            return None
        n = int.from_bytes(data[pos:pos + 2], "big")
        pos += 2
        if n < 126:
            return None
    else:
        if len(data) < pos + 8:
            return None
        n = int.from_bytes(data[pos:pos + 8], "big")
        pos += 8
        if n < 65536 or n >= 2**63:
            return None
    if opcode in (8, 9, 10) and (not fin or n > 125):
        return None
    key = b""
    if masked:
        if len(data) < pos + 4:
            return None
        key = data[pos:pos + 4]
        pos += 4
    if len(data) != pos + n:
        return None
    raw = data[pos:pos + n]
    if masked:
        payload = bytes(b ^ key[i % 4] for i, b in enumerate(raw))
    else:
        payload = raw
    return (fin, opcode, masked, key, payload)


def frame_fields(fin, opcode, masked, key, payload):
    return f"{fin} {opcode} {masked} {hex_or_dash(key)} {hex_or_dash(payload)}"


def main():
    if not EXE.exists():
        env = dict(os.environ)
        elan = Path.home() / ".elan" / "bin"
        if elan.exists():
            env["PATH"] = str(elan) + os.pathsep + env["PATH"]
        subprocess.run(["lake", "build"], cwd=PROJECT_DIR, env=env, check=True)
    if not EXE.exists():
        print("Lean executable missing after build")
        return 1

    rng = random.Random(SEED)
    enc_cases = []  # (name, lean_line, expected_output)
    dec_cases = []  # (name, lean_line, expected_output)

    def add_valid(name, fin, opcode, masked, key, payload):
        data = py_enc(fin, opcode, masked, key, payload)
        enc_cases.append((f"{name} enc",
                          f"enc {fin} {opcode} {masked} "
                          f"{hex_or_dash(key)} {hex_or_dash(payload)}",
                          data.hex() if data else "-"))
        dec_cases.append((f"{name} dec",
                          f"dec {data.hex() if data else '-'}",
                          frame_fields(fin, opcode, masked, key, payload)))
        # Python decode of the Lean encoding is checked by comparing
        # the Lean encoding to the Python encoding above, and the
        # Lean decoding to the original fields.

    # RFC 6455 section 5.7 worked examples.
    add_valid("rfc-unmasked-hello", 1, 1, 0, b"", b"Hello")
    add_valid("rfc-masked-hello", 1, 1, 1, bytes.fromhex("37fa213d"), b"Hello")
    add_valid("rfc-fragment-1", 0, 1, 0, b"", b"Hel")
    add_valid("rfc-fragment-2", 1, 0, 0, b"", b"lo")
    add_valid("rfc-ping", 1, 9, 0, b"", b"Hello")
    add_valid("rfc-close", 1, 8, 0, b"", b"")

    # Random valid frames, with lengths at every length-form boundary.
    lengths = [0, 1, 2, 5, 124, 125, 126, 127, 128, 255, 256,
               1000, 65535, 65536, 65537]
    for i, n in enumerate(lengths):
        for masked in (0, 1):
            opcode = rng.choice([0, 1, 2])
            key = rng.randbytes(4) if masked else b""
            add_valid(f"boundary-{n}-{masked}", rng.choice([0, 1]),
                      opcode, masked, key, rng.randbytes(n))
    for i in range(300):
        opcode = rng.choice([0, 1, 2, 8, 9, 10])
        if opcode in (8, 9, 10):
            fin, n = 1, rng.randrange(0, 126)
        else:
            fin, n = rng.choice([0, 1]), rng.randrange(0, 2001)
        masked = rng.choice([0, 1])
        key = rng.randbytes(4) if masked else b""
        add_valid(f"random-{i}", fin, opcode, masked, key, rng.randbytes(n))

    # Forbidden shapes: Lean and Python must both turn them away.
    def add_reject(name, data):
        dec_cases.append((f"{name} reject",
                          f"dec {data.hex() if data else '-'}", "error"))
        check(f"{name} python-rejects", py_dec(data) is None,
              f"python accepted {data.hex()[:80]}")

    good = py_enc(1, 1, 0, b"", b"Hello")
    add_reject("rsv-bit", bytes([good[0] | 0x40]) + good[1:])
    add_reject("rsv-bit-2", bytes([good[0] | 0x20]) + good[1:])
    add_reject("rsv-bit-3", bytes([good[0] | 0x10]) + good[1:])
    for op in (3, 7, 11, 15):
        add_reject(f"reserved-opcode-{op}", py_enc(1, 1, 0, b"", b"Hi")[:0] +
                   bytes([0x80 | op, 0x02]) + b"Hi")
    add_reject("control-fragmented", py_enc(0, 9, 0, b"", b"Hi"))
    add_reject("control-payload-126",
               py_enc(1, 9, 0, b"", bytes(126)))
    add_reject("nonminimal-126-form",
               bytes([0x81, 0x7E, 0x00, 0x05]) + b"Hello")
    add_reject("nonminimal-127-form-100",
               bytes([0x81, 0x7F]) + (100).to_bytes(8, "big") + bytes(100))
    add_reject("nonminimal-127-form-126",
               bytes([0x81, 0x7F]) + (126).to_bytes(8, "big") + bytes(126))
    add_reject("length-over-2^63",
               bytes([0x81, 0xFF]) + (2**63).to_bytes(8, "big"))
    add_reject("truncated-payload", good[:-1])
    add_reject("truncated-key", py_enc(1, 1, 1, bytes.fromhex("37fa213d"),
                                       b"Hello")[:-3])
    add_reject("truncated-length", bytes([0x81, 0x7E, 0x00]))
    add_reject("trailing-bytes", good + b"\x00")
    add_reject("empty", b"")
    add_reject("one-byte", bytes([0x81]))
    add_reject("masked-short-key",
               bytes([0x81, 0x85, 0x37, 0xFA]) + b"Hello")

    # Invalid CLI encode requests.
    for name, line in [
        ("enc-reserved-opcode", "enc 1 3 0 - -"),
        ("enc-control-fragmented", "enc 0 9 0 - 4869"),
        ("enc-control-long", "enc 1 9 0 - " + "00" * 126),
        ("enc-short-key", "enc 1 1 1 37fa -"),
        ("enc-key-unmasked", "enc 1 1 0 37fa213d -"),
        ("enc-odd-hex", "enc 1 1 0 - 486"),
        ("enc-bad-hex", "enc 1 1 0 - zz"),
        ("enc-bad-fin", "enc 2 1 0 - -"),
    ]:
        enc_cases.append((name, line, "error"))

    # Run everything through one batch call.
    lines = [line for _, line, _ in enc_cases + dec_cases]
    import tempfile
    with tempfile.NamedTemporaryFile("w", suffix=".txt", delete=False) as f:
        f.write("\n".join(lines) + "\n")
        cases_file = f.name
    try:
        proc = subprocess.run([str(EXE), "batch", cases_file],
                              capture_output=True, text=True)
    finally:
        os.unlink(cases_file)
    outputs = proc.stdout.splitlines()
    if len(outputs) != len(lines):
        check("batch-line-count", False,
              f"got {len(outputs)} outputs for {len(lines)} cases")
        outputs += ["<missing>"] * (len(lines) - len(outputs))
    for (name, _line, expected), got in zip(enc_cases + dec_cases, outputs):
        check(name, got == expected, f"expected {expected[:80]}, got {got[:80]}")

    RESULTS.write_text(
        "# TEST-RESULTS\n\n"
        f"Checks: {checks}, passed: {checks - len(failures)}, "
        f"failed: {len(failures)}.\n\n"
        f"Seed: {SEED}.\n"
        f"Valid frames: {len(enc_cases) - 8} encode cases and "
        f"{len(dec_cases)} decode cases, covering RFC 5.7 examples, "
        "length-form boundaries 0, 1, 124, 125, 126, 127, 255, 256, "
        "65535, 65536 and 65537, 300 random frames, and the "
        "forbidden shapes in the plan (reserved bits, reserved "
        "opcodes, fragmented and overlong control frames, "
        "non-minimal length forms, a length at 2^63, truncation, "
        "trailing bytes, and malformed CLI requests).\n\n"
        + ("Failures:\n" + "\n".join(failures) + "\n" if failures
           else "No failures.\n")
    )
    print(f"{checks - len(failures)}/{checks} checks passed")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
