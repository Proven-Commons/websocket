/-
  One WebSocket frame, as RFC 6455 section 5 sets it out.

  This file holds the frame type, the printer (encode) and the parser
  (parse). A frame is a FIN bit, an opcode, a mask bit, a masking key
  and a payload. Bytes are natural numbers. The printer and the parser
  are total functions. The parser turns a byte list away, returning
  none, when the shape breaks any rule in the plan: a reserved bit
  set, a reserved opcode, a control frame split into fragments, a
  control frame with a payload over 125 bytes, a length form longer
  than the payload needs, a length at or over 2^63, a short or
  overlong byte list, or trailing bytes after the payload.

  Fragment reassembly sits one layer up and stays out of this slice.
  A continuation frame (opcode 0) is one frame here, not a message.
-/

namespace WebSocket

/-- A single frame. `key` holds 4 bytes when `masked` is true, else none. -/
structure Frame where
  fin : Bool
  opcode : Nat
  masked : Bool
  key : List Nat
  payload : List Nat
deriving DecidableEq, Repr, Inhabited

/-- Opcodes 8, 9 and 10 are the control frames: close, ping, pong. -/
def IsControl (op : Nat) : Prop := op = 8 ∨ op = 9 ∨ op = 10

/-- The opcodes this slice accepts: 0, 1, 2 and the three control opcodes. -/
def IsOpcode (op : Nat) : Prop :=
  op = 0 ∨ op = 1 ∨ op = 2 ∨ IsControl op

/-- A frame the printer accepts. The last bound is the RFC limit: the
    length field holds 63 bits, so a payload of 2^63 bytes or more has
    no legal length form. -/
def Valid (f : Frame) : Prop :=
  IsOpcode f.opcode ∧
  (IsControl f.opcode → f.fin = true ∧ f.payload.length ≤ 125) ∧
  (f.masked = true → f.key.length = 4) ∧
  (f.masked = false → f.key = []) ∧
  f.payload.length < 2 ^ 63

/-- The same opcode check, as a boolean, for the parser and the CLI. -/
def opcodeOk (op : Nat) : Bool :=
  op == 0 || op == 1 || op == 2 || op == 8 || op == 9 || op == 10

theorem opcodeOk_of_IsOpcode {op : Nat} (h : IsOpcode op) : opcodeOk op = true := by
  unfold IsOpcode IsControl at h
  unfold opcodeOk
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Byte at position `i` of a repeating key, cycling every key length. -/
def keyAt (key : List Nat) (i : Nat) : Nat := key.getD (i % key.length) 0

/-- Indexed map, written out so the masking proof can generalise the index. -/
def mapIdxAux : Nat → (Nat → Nat → Nat) → List Nat → List Nat
  | _, _, [] => []
  | i, f, x :: xs => f i x :: mapIdxAux (i + 1) f xs

/-- Masking a payload: each byte is xored with the key byte at its
    position, cycling through the key. Unmasking is the same function. -/
def maskWith (key : List Nat) (payload : List Nat) : List Nat :=
  mapIdxAux 0 (fun i b => b ^^^ keyAt key i) payload

theorem mapIdxAux_length (i : Nat) (f : Nat → Nat → Nat) (xs : List Nat) :
    (mapIdxAux i f xs).length = xs.length := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih => simp [mapIdxAux, ih]

theorem maskWith_length (key payload : List Nat) :
    (maskWith key payload).length = payload.length :=
  mapIdxAux_length 0 _ _

theorem mapIdxAux_mapIdxAux (i : Nat) (f g : Nat → Nat → Nat) (xs : List Nat)
    (h : ∀ j b, g j (f j b) = b) :
    mapIdxAux i g (mapIdxAux i f xs) = xs := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih =>
    simp only [mapIdxAux, h, ih]

theorem maskWith_involutive (key payload : List Nat) :
    maskWith key (maskWith key payload) = payload := by
  unfold maskWith
  apply mapIdxAux_mapIdxAux
  intro j b
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

/-- Big-endian bytes, most significant first. `be k n` holds `k` bytes
    and, when `n < 256 ^ k`, reads back as `n`. -/
def be : Nat → Nat → List Nat
  | 0, _ => []
  | k + 1, n => be k (n / 256) ++ [n % 256]

theorem be_length (k n : Nat) : (be k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [be, ih, List.length_append]

theorem be_decode (k n : Nat) (h : n < 256 ^ k) :
    (be k n).foldl (fun a b => a * 256 + b) 0 = n := by
  induction k generalizing n with
  | zero =>
    have hn : n = 0 := by
      simp at h
      omega
    subst hn
    rfl
  | succ k ih =>
    have hpow : 256 ^ (k + 1) = 256 ^ k * 256 := Nat.pow_succ 256 k
    have hdiv : n / 256 < 256 ^ k := by omega
    simp only [be, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [ih (n / 256) hdiv]
    omega

/-- The two-byte length form reads back, for payloads under 65536. -/
theorem be_two (n : Nat) (h : n < 65536) : be 2 n = [n / 256, n % 256] := by
  have hdiv : n / 256 < 256 := by omega
  have hmod : (n / 256) % 256 = n / 256 := Nat.mod_eq_of_lt hdiv
  simp [be, hmod]

/-- The length form a payload length takes: the length itself when
    under 126, the marker 126 with two bytes, or the marker 127 with
    eight bytes. -/
def lenForm (len : Nat) : Nat × List Nat :=
  if len < 126 then (len, [])
  else if len < 65536 then (126, be 2 len)
  else (127, be 8 len)

theorem lenForm_indicator_lt (len : Nat) : (lenForm len).1 < 128 := by
  unfold lenForm
  by_cases h1 : len < 126
  · rw [if_pos h1]
    simp
    omega
  · rw [if_neg h1]
    by_cases h2 : len < 65536
    · rw [if_pos h2]
      simp
    · rw [if_neg h2]
      simp

/-- The printer. The mask bit and the length marker share the second
    byte, as the RFC sets out. -/
def encode (f : Frame) : List Nat :=
  let b0 := (if f.fin then 128 else 0) + f.opcode
  let form := lenForm f.payload.length
  let b1 := (if f.masked then 128 else 0) + form.1
  let body := if f.masked then maskWith f.key f.payload else f.payload
  [b0, b1] ++ form.2 ++ (if f.masked then f.key else []) ++ body

/-- Take `n` bytes, or fail when fewer are left. -/
def takeBytes (n : Nat) (xs : List Nat) : Option (List Nat × List Nat) :=
  if xs.length < n then none else some (xs.take n, xs.drop n)

theorem takeBytes_append (xs tail : List Nat) :
    takeBytes xs.length (xs ++ tail) = some (xs, tail) := by
  unfold takeBytes
  rw [if_neg (by simp)]
  simp

theorem takeBytes_of_length (n : Nat) (xs tail : List Nat) (h : xs.length = n) :
    takeBytes n (xs ++ tail) = some (xs, tail) := by
  rw [← h]
  exact takeBytes_append xs tail

theorem takeBytes_self (xs : List Nat) : takeBytes xs.length xs = some (xs, []) := by
  have h := takeBytes_append xs []
  simp at h
  exact h

theorem takeBytes_mask (key payload : List Nat) :
    takeBytes payload.length (maskWith key payload) =
      some (maskWith key payload, []) := by
  have h := takeBytes_self (maskWith key payload)
  rw [maskWith_length] at h
  exact h

/-- Read a length from its marker and the bytes that follow it. The
    minimal-form rule is enforced here: the two-byte form must hold a
    length of at least 126, the eight-byte form at least 65536. -/
def parseLen (indicator : Nat) (rest : List Nat) : Option (Nat × List Nat) :=
  if indicator < 126 then some (indicator, rest)
  else if indicator = 126 then
    match takeBytes 2 rest with
    | none => none
    | some ([a, b], rest') =>
      let n := a * 256 + b
      if 126 ≤ n then some (n, rest') else none
    | some _ => none
  else if indicator = 127 then
    match takeBytes 8 rest with
    | none => none
    | some (bytes, rest') =>
      let n := bytes.foldl (fun a b => a * 256 + b) 0
      if 65536 ≤ n ∧ n < 2 ^ 63 then some (n, rest') else none
  else none

theorem parseLen_lenForm (len : Nat) (tail : List Nat) (h : len < 2 ^ 63) :
    parseLen (lenForm len).1 ((lenForm len).2 ++ tail) = some (len, tail) := by
  by_cases h1 : len < 126
  · have hform : lenForm len = (len, []) := by simp [lenForm, h1]
    rw [hform]
    simp [parseLen, h1]
  · by_cases h2 : len < 65536
    · have hform : lenForm len = (126, be 2 len) := by simp [lenForm, h1, h2]
      rw [hform, be_two len h2]
      unfold parseLen
      rw [takeBytes_of_length 2 [len / 256, len % 256] tail rfl]
      have hdec : (len / 256) * 256 + len % 256 = len := by omega
      simp [hdec]
      omega
    · have hform : lenForm len = (127, be 8 len) := by simp [lenForm, h1, h2]
      rw [hform]
      unfold parseLen
      rw [takeBytes_of_length 8 (be 8 len) tail (be_length 8 len)]
      have hdec : (be 8 len).foldl (fun a b => a * 256 + b) 0 = len := by
        apply be_decode
        have h8 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
        rw [h8]
        omega
      simp only [hdec]
      simp
      omega

/-- The parser. One frame, no trailing bytes. -/
def parse (bs : List Nat) : Option Frame :=
  match bs with
  | b0 :: b1 :: rest =>
    if (b0 / 16) % 8 ≠ 0 then none
    else if !opcodeOk (b0 % 16) then none
    else match parseLen (b1 % 128) rest with
    | none => none
    | some (len, rest1) =>
      match (if decide (128 ≤ b1) then takeBytes 4 rest1 else some ([], rest1)) with
      | none => none
      | some (key, rest2) =>
        match takeBytes len rest2 with
        | none => none
        | some (maskedPayload, rest3) =>
          if rest3 ≠ [] then none
          else
            let payload := if decide (128 ≤ b1) then maskWith key maskedPayload
              else maskedPayload
            if (b0 % 16 = 8 ∨ b0 % 16 = 9 ∨ b0 % 16 = 10) ∧
              (decide (128 ≤ b0) = false ∨ len > 125)
            then none
            else some (Frame.mk (decide (128 ≤ b0)) (b0 % 16)
              (decide (128 ≤ b1)) key payload)
  | _ => none

end WebSocket
