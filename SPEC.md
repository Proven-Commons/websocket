# SPEC

What counts as a valid frame, and what the command line tool turns
away. This is the record the parser is checked against.

## A frame

A frame is a FIN bit, an opcode, a mask bit, a masking key, and a
payload, in that order on the wire. The first byte holds FIN, three
reserved bits, and the opcode. The second byte holds the mask bit and
the length marker. The length marker is the payload length when under
126, the marker 126 with two length bytes, or the marker 127 with
eight length bytes, all big-endian.

Accepted opcodes are 0, 1, 2, 8, 9, and 10. A control frame (8, 9, 10)
must have FIN set and a payload of at most 125 bytes. The masking key
holds 4 bytes when the mask bit is set, and no bytes otherwise. The
payload length must be under 2^63.

## What the parser turns away

- A reserved bit set in the first byte.
- An opcode outside the accepted list.
- A control frame with FIN clear, or with a payload over 125 bytes.
- A two-byte length form holding under 126, or an eight-byte form
  holding under 65536. The shortest form must be used.
- An eight-byte length at or over 2^63.
- A byte list that ends before the frame ends.
- Extra bytes after the payload.
- A masked frame with fewer than 4 key bytes.

## What the command line tool turns away

- A `fin` or `masked` value other than 0 or 1.
- An opcode outside the accepted list, or a control frame that
  breaks the control rule above.
- A masking key that is not 4 bytes when masked, or not empty when
  unmasked.
- A payload of 2^63 bytes or more.
- Hex text of odd length, or with a character outside 0-9, a-f, A-F.
- A command with the wrong number of arguments.
