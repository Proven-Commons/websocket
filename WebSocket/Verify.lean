/-
  The proved claim for the first slice: parsing what the printer wrote
  returns the same frame, for every valid frame. Parsing and the CLI
  validity check are tested, not proved. See README.md for the split.
-/

import WebSocket.Frame

namespace WebSocket

theorem parse_encode (f : Frame) (h : Valid f) : parse (encode f) = some f := by
  obtain ⟨hop, hctrl, hmaskT, hmaskF, hlen63⟩ := h
  obtain ⟨fin, opcode, masked, key, payload⟩ := f
  -- The projections of the anonymous constructor reduce to the
  -- components, but only definitionally, so restate them plainly.
  have hop2 : IsOpcode opcode := hop
  have hctrl2 : IsControl opcode → fin = true ∧ payload.length ≤ 125 := hctrl
  have hmaskT2 : masked = true → key.length = 4 := hmaskT
  have hmaskF2 : masked = false → key = [] := hmaskF
  have hlen632 : payload.length < 2 ^ 63 := hlen63
  have hop_le : opcode ≤ 10 := by
    unfold IsOpcode IsControl at hop2
    rcases hop2 with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have hopok : opcodeOk opcode = true := opcodeOk_of_IsOpcode hop2
  have hopmod2 : opcode % 16 = opcode := by omega
  have hind_lt : (lenForm payload.length).1 < 128 := lenForm_indicator_lt _
  cases fin <;> cases masked
  · -- fin false, masked false
    have hkey : key = [] := hmaskF2 rfl
    have hnotctrl : ¬ (opcode = 8 ∨ opcode = 9 ∨ opcode = 10) := by
      intro hc
      have hctrl' : ¬ ((opcode = 8 ∨ opcode = 9 ∨ opcode = 10) ∧
          (false = false ∨ payload.length > 125)) := by
        intro hc2
        obtain ⟨hcop, hbad⟩ := hc2
        obtain ⟨hfin, hle⟩ := hctrl2 hcop
        rcases hbad with hfin' | hlen'
        · simp at hfin
        · omega
      exact hctrl' ⟨hc, Or.inl rfl⟩
    have hfin2 : decide (128 ≤ opcode) = false := by
      rw [decide_eq_false_iff_not]
      omega
    have hrsv : (0 + opcode) / 16 % 8 = 0 := by omega
    have hopmod : (0 + opcode) % 16 = opcode := by omega
    have hfin : decide (128 ≤ 0 + opcode) = false := by
      rw [decide_eq_false_iff_not]
      omega
    have hmask : decide (128 ≤ 0 + (lenForm payload.length).1) = false := by
      rw [decide_eq_false_iff_not]
      omega
    have hind : (0 + (lenForm payload.length).1) % 128 =
        (lenForm payload.length).1 := by omega
    have hrsv2 : opcode / 16 % 8 = 0 := by omega
    have hind2 : (lenForm payload.length).1 % 128 =
        (lenForm payload.length).1 := by omega
    have hmask2 : ¬ (128 ≤ (lenForm payload.length).1) := by omega
    have henc : encode ⟨false, opcode, false, key, payload⟩ =
      (0 + opcode) :: (0 + (lenForm payload.length).1) ::
      ((lenForm payload.length).2 ++ [] ++ payload) := by simp [encode]
    rw [henc]
    unfold parse
    simp [hrsv, hrsv2, hopmod, hopmod2, hfin, hfin2, hmask, hmask2, hind, hind2,
      hopok, hnotctrl, hkey, parseLen_lenForm, takeBytes_self, hlen632]
  · -- fin false, masked true
    have hkeylen : key.length = 4 := hmaskT2 rfl
    have hnotctrl : ¬ (opcode = 8 ∨ opcode = 9 ∨ opcode = 10) := by
      intro hc
      have hctrl' : ¬ ((opcode = 8 ∨ opcode = 9 ∨ opcode = 10) ∧
          (false = false ∨ payload.length > 125)) := by
        intro hc2
        obtain ⟨hcop, hbad⟩ := hc2
        obtain ⟨hfin, hle⟩ := hctrl2 hcop
        rcases hbad with hfin' | hlen'
        · simp at hfin
        · omega
      exact hctrl' ⟨hc, Or.inl rfl⟩
    have hfin2 : decide (128 ≤ opcode) = false := by
      rw [decide_eq_false_iff_not]
      omega
    have hrsv : (0 + opcode) / 16 % 8 = 0 := by omega
    have hopmod : (0 + opcode) % 16 = opcode := by omega
    have hfin : decide (128 ≤ 0 + opcode) = false := by
      rw [decide_eq_false_iff_not]
      omega
    have hmask : decide (128 ≤ 128 + (lenForm payload.length).1) = true := by
      rw [decide_eq_true_eq]
      omega
    have hind : (128 + (lenForm payload.length).1) % 128 =
        (lenForm payload.length).1 := by omega
    have hrsv2 : opcode / 16 % 8 = 0 := by omega
    have henc : encode ⟨false, opcode, true, key, payload⟩ =
      (0 + opcode) :: (128 + (lenForm payload.length).1) ::
      ((lenForm payload.length).2 ++ key ++ maskWith key payload) := by simp [encode]
    rw [henc]
    unfold parse
    simp [hrsv, hrsv2, hopmod, hopmod2, hfin, hfin2, hmask, hind, hopok, hnotctrl,
      hkeylen, parseLen_lenForm, takeBytes_self, takeBytes_of_length,
      takeBytes_mask, maskWith_length, maskWith_involutive, hlen632]
  · -- fin true, masked false
    have hkey : key = [] := hmaskF2 rfl
    have hguard : ¬ ((opcode = 8 ∨ opcode = 9 ∨ opcode = 10) ∧
        payload.length > 125) := by
      intro hc
      obtain ⟨hcop, hlen⟩ := hc
      obtain ⟨_, hle⟩ := hctrl2 hcop
      omega
    have hrsv : (128 + opcode) / 16 % 8 = 0 := by omega
    have hopmod : (128 + opcode) % 16 = opcode := by omega
    have hfin : decide (128 ≤ 128 + opcode) = true := by
      rw [decide_eq_true_eq]
      omega
    have hmask : decide (128 ≤ 0 + (lenForm payload.length).1) = false := by
      rw [decide_eq_false_iff_not]
      omega
    have hind : (0 + (lenForm payload.length).1) % 128 =
        (lenForm payload.length).1 := by omega
    have hrsv2 : (128 + opcode) / 16 % 8 = 0 := by omega
    have hind2 : (lenForm payload.length).1 % 128 =
        (lenForm payload.length).1 := by omega
    have hmask2 : ¬ (128 ≤ (lenForm payload.length).1) := by omega
    have henc : encode ⟨true, opcode, false, key, payload⟩ =
      (128 + opcode) :: (0 + (lenForm payload.length).1) ::
      ((lenForm payload.length).2 ++ [] ++ payload) := by simp [encode]
    rw [henc]
    unfold parse
    simp [hrsv, hrsv2, hopmod, hopmod2, hfin, hmask, hmask2, hind, hind2, hopok,
      hguard, hkey, parseLen_lenForm, takeBytes_self, hlen632]
  · -- fin true, masked true
    have hkeylen : key.length = 4 := hmaskT2 rfl
    have hguard : ¬ ((opcode = 8 ∨ opcode = 9 ∨ opcode = 10) ∧
        payload.length > 125) := by
      intro hc
      obtain ⟨hcop, hlen⟩ := hc
      obtain ⟨_, hle⟩ := hctrl2 hcop
      omega
    have hrsv : (128 + opcode) / 16 % 8 = 0 := by omega
    have hopmod : (128 + opcode) % 16 = opcode := by omega
    have hfin : decide (128 ≤ 128 + opcode) = true := by
      rw [decide_eq_true_eq]
      omega
    have hmask : decide (128 ≤ 128 + (lenForm payload.length).1) = true := by
      rw [decide_eq_true_eq]
      omega
    have hind : (128 + (lenForm payload.length).1) % 128 =
        (lenForm payload.length).1 := by omega
    have hrsv2 : (128 + opcode) / 16 % 8 = 0 := by omega
    have henc : encode ⟨true, opcode, true, key, payload⟩ =
      (128 + opcode) :: (128 + (lenForm payload.length).1) ::
      ((lenForm payload.length).2 ++ key ++ maskWith key payload) := by simp [encode]
    rw [henc]
    unfold parse
    simp [hrsv, hrsv2, hopmod, hopmod2, hfin, hmask, hind, hopok, hguard,
      hkeylen, parseLen_lenForm, takeBytes_self, takeBytes_of_length,
      takeBytes_mask, maskWith_length, maskWith_involutive, hlen632]

#print axioms parse_encode

end WebSocket
