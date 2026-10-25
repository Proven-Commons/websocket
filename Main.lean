/-
  Command line front end for the WebSocket first slice.

    websocket enc <fin> <opcode> <masked> <keyhex|-> <payloadhex|->
      Print the frame as lowercase hex, or `error`.

    websocket dec <framehex|->
      Print `fin opcode masked keyhex payloadhex`, or `error`.
      `fin` and `masked` print as 0 or 1. A `-` stands for an empty
      byte list, so batch lines stay tokenisable.

    websocket batch <file>
      Read one command per line from the file, print one result
      per line. Used by the differential test harness.
-/

import WebSocket

open WebSocket

def hexVal (c : Char) : Option Nat :=
  let n := c.toNat
  if 48 ≤ n ∧ n ≤ 57 then some (n - 48)
  else if 97 ≤ n ∧ n ≤ 102 then some (10 + n - 97)
  else if 65 ≤ n ∧ n ≤ 70 then some (10 + n - 65)
  else none

def hexToBytes : List Char → Option (List Nat)
  | [] => some []
  | a :: b :: rest => do
    let hi ← hexVal a
    let lo ← hexVal b
    let tail ← hexToBytes rest
    some ((hi * 16 + lo) :: tail)
  | _ => none

def hexDigit (n : Nat) : Char :=
  "0123456789abcdef".toList.getD n '?'

def byteToHex (b : Nat) : String :=
  String.mk [hexDigit (b / 16), hexDigit (b % 16)]

def bytesToHex (bs : List Nat) : String :=
  bs.foldl (fun s b => s ++ byteToHex b) ""

def hexOrDash (bs : List Nat) : String :=
  if bs.isEmpty then "-" else bytesToHex bs

def bytesOrDash (s : String) : Option (List Nat) :=
  if s = "-" then some [] else hexToBytes s.toList

def decToNat (s : String) : Option Nat := s.toNat?

def validBool (f : Frame) : Bool :=
  opcodeOk f.opcode &&
  (if f.opcode = 8 ∨ f.opcode = 9 ∨ f.opcode = 10 then
    f.fin && decide (f.payload.length ≤ 125)
   else true) &&
  (if f.masked then f.key.length == 4 else f.key.isEmpty) &&
  decide (f.payload.length < 2 ^ 63)

def runEnc (args : List String) : String :=
  match args with
  | [finS, opS, maskedS, keyS, payloadS] =>
    match decToNat opS, bytesOrDash keyS, bytesOrDash payloadS with
    | some op, some key, some payload =>
      let fin := finS = "1"
      let masked := maskedS = "1"
      if (finS ≠ "0" ∧ finS ≠ "1") ∨ (maskedS ≠ "0" ∧ maskedS ≠ "1") then "error"
      else
        let frame : Frame := Frame.mk fin op masked key payload
        if !validBool frame then "error"
        else
          let bytes := encode frame
          if bytes.any (fun b => 256 ≤ b) then "error" else bytesToHex bytes
    | _, _, _ => "error"
  | _ => "error"

def runDec (args : List String) : String :=
  match args with
  | [frameS] =>
    match bytesOrDash frameS with
    | none => "error"
    | some bytes =>
      match parse bytes with
      | none => "error"
      | some f =>
        let finS := if f.fin then "1" else "0"
        let maskedS := if f.masked then "1" else "0"
        s!"{finS} {f.opcode} {maskedS} {hexOrDash f.key} {hexOrDash f.payload}"
  | _ => "error"

def runToks (toks : List String) : String :=
  match toks with
  | "enc" :: args => runEnc args
  | "dec" :: args => runDec args
  | _ => "error"

def runBatch (file : String) : IO UInt32 := do
  let content ← IO.FS.readFile file
  for line in content.splitOn "\n" do
    let toks := (line.splitOn " ").filter (fun t => t ≠ "" ∧ t ≠ "\r")
    if !toks.isEmpty then IO.println (runToks toks)
  return 0

def usage : IO UInt32 := do
  IO.eprintln "usage: websocket enc <fin> <opcode> <masked> <keyhex|-> <payloadhex|->"
  IO.eprintln "       websocket dec <framehex|->"
  IO.eprintln "       websocket batch <file>"
  return 2

def main (args : List String) : IO UInt32 := do
  match args with
  | "enc" :: rest =>
    let out := runEnc rest
    IO.println out
    return (if out = "error" then 1 else 0)
  | "dec" :: rest =>
    let out := runDec rest
    IO.println out
    return (if out = "error" then 1 else 0)
  | ["batch", file] => runBatch file
  | _ => usage
