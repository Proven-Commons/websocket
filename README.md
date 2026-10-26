# websocket

A WebSocket frame parser and printer, written in Lean. It reads and
writes one WebSocket frame, as RFC 6455 section 5 sets it out. It is
a Proven Commons project: verified libraries built in the open, and
training material for new verifiers.

## What is in it

- `WebSocket/Frame.lean`: the frame type, the printer, and the parser.
- `WebSocket/Verify.lean`: the proved round trip.
- `Main.lean`: a command line tool for the parser and the printer.
- `tests/run_tests.py`: differential tests against an independent
  Python implementation of the same RFC section.

## What is proved

`parse_encode` in `WebSocket/Verify.lean` states that parsing what the
printer wrote returns the same frame, for every valid frame. It uses
only the standard three axioms (`propext`, `Classical.choice`,
`Quot.sound`). There is no `sorry` anywhere in the project.

A valid frame means: an accepted opcode (0, 1, 2, 8, 9, 10), a
control frame that is not fragmented and whose payload is at most
125 bytes, a masking key of 4 bytes when masked and no key when
unmasked, and a payload under 2^63 bytes, which is the RFC limit for
the length field.

## What is tested, not proved

The parser turns a bad frame away, and the command line tool turns a
bad request away. Those rejections are tested, not proved. The test
run covers the RFC 5.7 worked examples, every length-form boundary,
300 random frames, and the forbidden shapes: reserved bits, reserved
opcodes, fragmented and overlong control frames, non-minimal length
forms, a length at 2^63, truncation, and trailing bytes. The full run
is 720 checks, 0 failures, seed 20261025. See `tests/TEST-RESULTS.md`.

## One strictness decision

A frame that uses a longer length form than its payload needs is
turned away. The plan proposes that, and this slice follows it. The
specification writer settles it. If the decision goes the other way,
the change is one check in `parseLen`.

## What is outside this slice

Putting fragments back together into a message, protocol extensions,
handling a connection, and writing frames to a socket. Payloads of
2^63 bytes or more have no legal length form, so the parser turns
them away.

## Build and test

    lake build
    python3 tests/run_tests.py

## Command line

    websocket enc <fin> <opcode> <masked> <keyhex|-> <payloadhex|->
    websocket dec <framehex|->
    websocket batch <file>

`fin` and `masked` are 0 or 1. A `-` stands for an empty byte list.
A bad request prints `error`. For example, the RFC masked "Hello"
frame:

    websocket enc 1 1 1 37fa213d 48656c6c6f
    websocket dec 818537fa213d7f9f4d5158

## Status

In progress. This is the first slice from
[Proven-Commons/websocket#1](https://github.com/Proven-Commons/websocket/issues/1).
