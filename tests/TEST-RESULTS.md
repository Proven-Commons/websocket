# TEST-RESULTS

Checks: 720, passed: 720, failed: 0.

Seed: 20261025.
Valid frames: 336 encode cases and 356 decode cases, covering RFC 5.7 examples, length-form boundaries 0, 1, 124, 125, 126, 127, 255, 256, 65535, 65536 and 65537, 300 random frames, and the forbidden shapes in the plan (reserved bits, reserved opcodes, fragmented and overlong control frames, non-minimal length forms, a length at 2^63, truncation, trailing bytes, and malformed CLI requests).

No failures.
