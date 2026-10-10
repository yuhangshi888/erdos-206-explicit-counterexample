module
/-
Copyright (c) 2026 Yuhang Shi.
SPDX-License-Identifier: AGPL-3.0-only
Released under the GNU Affero General Public License, version 3 only.
-/
public import Egyptian.PrefixInterval

@[expose] public section

/-! A two-candidate executable replacement for the least bad-pair index.
The output is proved equal to the original unbounded `Nat.find` search, so
using this routine preserves every rational interval in the manuscript. -/

namespace Egyptian.FastSearch

/-- Least index at least 3 and greater than M whose single reciprocal is
strictly smaller than ε. This is a rational floor calculation. -/
def baseIndexQ (M : ℕ) (ε : ℚ) : ℕ := greedyDenomQ ε 0 (max 2 M)

theorem baseIndexQ_formula (M : ℕ) (ε : ℚ) :
    baseIndexQ M ε = max 3 (max (M + 1) (Nat.floor ε⁻¹ + 1)) := by
  unfold baseIndexQ greedyDenomQ
  simp only [sub_zero]
  omega

/-- Only the base index and its successor can be the least bad-pair index. -/
def fastBadIndexQ (M : ℕ) (ε : ℚ) (_hε : 0 < ε) : ℕ :=
  let i := baseIndexQ M ε
  if BadPair.uRat i < ε then i else i + 1

theorem baseIndexQ_spec (M : ℕ) (ε : ℚ) (hε : 0 < ε) :
    3 ≤ baseIndexQ M ε ∧ M < baseIndexQ M ε ∧ unitQ (baseIndexQ M ε) < ε := by
  have h := greedyDenomQ_least hε (max 2 M)
  have hbound : max 2 M < baseIndexQ M ε := h.1.1
  have hsmall : unitQ (baseIndexQ M ε) < ε := by simpa only [baseIndexQ, zero_add] using h.1.2
  refine ⟨?_, ?_, hsmall⟩
  · have h2 : 2 ≤ max 2 M := le_max_left _ _
    omega
  · exact lt_of_le_of_lt (le_max_right _ _) hbound

theorem unitQ_lt_uRat (i : ℕ) : unitQ i < BadPair.uRat i := by
  have hD : 0 < BadPair.D i := by unfold BadPair.D; omega
  have hpos : (0 : ℚ) < 1 / (BadPair.D i : ℚ) :=
    div_pos (by norm_num) (Nat.cast_pos.mpr hD)
  unfold BadPair.uRat unitQ
  simpa only [one_div] using lt_add_of_pos_right (i : ℚ)⁻¹ hpos

theorem baseIndexQ_le_of_bad (M i : ℕ) (ε : ℚ) (hε : 0 < ε)
    (hi : 3 ≤ i) (hM : M < i) (hu : BadPair.uRat i < ε) : baseIndexQ M ε ≤ i := by
  have hleast := greedyDenomQ_least hε (max 2 M)
  apply hleast.2 i
  refine ⟨?_, ?_⟩
  · exact max_lt_iff.mpr ⟨by omega, hM⟩
  · simpa only [zero_add] using lt_trans (unitQ_lt_uRat i) hu

theorem successor_bad (M : ℕ) (ε : ℚ) (hε : 0 < ε) :
    BadPair.uRat (baseIndexQ M ε + 1) < ε := by
  have hb := baseIndexQ_spec M ε hε
  have hi : 3 ≤ baseIndexQ M ε + 1 := by omega
  have hu := (BadPair.bounds_rat (baseIndexQ M ε + 1) hi).2.2
  have hlt : BadPair.uRat (baseIndexQ M ε + 1) < unitQ (baseIndexQ M ε) := by
    simpa only [Nat.add_sub_cancel, one_div, unitQ] using hu
  exact lt_trans hlt hb.2.2

theorem fastBadIndexQ_cases (M : ℕ) (ε : ℚ) (hε : 0 < ε) :
    fastBadIndexQ M ε hε = baseIndexQ M ε ∨
    fastBadIndexQ M ε hε = baseIndexQ M ε + 1 := by
  dsimp only [fastBadIndexQ]
  split_ifs <;> simp

theorem fastBadIndexQ_spec (M : ℕ) (ε : ℚ) (hε : 0 < ε) :
    3 ≤ fastBadIndexQ M ε hε ∧ M < fastBadIndexQ M ε hε ∧
      BadPair.uRat (fastBadIndexQ M ε hε) < ε := by
  have hb := baseIndexQ_spec M ε hε
  dsimp only [fastBadIndexQ]
  split_ifs with h
  · exact ⟨hb.1, hb.2.1, h⟩
  · exact ⟨by omega, by omega, successor_bad M ε hε⟩

/-- Semantic equality to the exact least-index routine, not just feasibility. -/
theorem fastBadIndexQ_eq (M : ℕ) (ε : ℚ) (hε : 0 < ε) :
    fastBadIndexQ M ε hε = PrefixInterval.badIndexQ M ε hε := by
  have hf := fastBadIndexQ_spec M ε hε
  have hs := PrefixInterval.badIndexQ_spec M ε hε
  have hslowle : PrefixInterval.badIndexQ M ε hε ≤ fastBadIndexQ M ε hε :=
    PrefixInterval.badIndexQ_min M ε hε _ hf.1 hf.2.1 hf.2.2
  have hbasele := baseIndexQ_le_of_bad M (PrefixInterval.badIndexQ M ε hε) ε hε
    hs.1 hs.2.1 hs.2.2
  apply Nat.le_antisymm ?_ hslowle
  dsimp only [fastBadIndexQ]
  split_ifs with h
  · exact hbasele
  · have hne : baseIndexQ M ε ≠ PrefixInterval.badIndexQ M ε hε := by
      intro heq
      apply h
      rw [heq]
      exact hs.2.2
    omega

def intervalOfCutFastQ {a b : ℚ} {S : Prefix} (C : PrefixInterval.CutData a b S) : ℚ × ℚ :=
  let i := fastBadIndexQ C.extended.last (C.cap - C.extended.sumQ) C.gap_pos
  (C.extended.sumQ + BadPair.rRat i, C.extended.sumQ + BadPair.uRat i)

theorem intervalOfCutFastQ_eq {a b : ℚ} {S : Prefix} (C : PrefixInterval.CutData a b S) :
    intervalOfCutFastQ C = PrefixInterval.intervalOfCutQ C := by
  simp only [intervalOfCutFastQ, PrefixInterval.intervalOfCutQ, fastBadIndexQ_eq]

def defeatFastQ (a b : ℚ) (S : Prefix) (_h0 : 0 < a) (hab : a < b) (_hb1 : b < 1) :
    ℚ × ℚ :=
  if h : a < S.sumQ then (a, min b S.sumQ)
  else intervalOfCutFastQ (PrefixInterval.makeCutQ a b S hab (le_of_not_gt h))

theorem defeatFastQ_eq (a b : ℚ) (S : Prefix) (h0 : 0 < a) (hab : a < b) (hb1 : b < 1) :
    defeatFastQ a b S h0 hab hb1 = PrefixInterval.defeatQ a b S h0 hab hb1 := by
  unfold defeatFastQ PrefixInterval.defeatQ
  split_ifs <;> simp only [intervalOfCutFastQ_eq]

theorem defeatFastQ_spec (a b : ℚ) (S : Prefix) (h0 : 0 < a) (hab : a < b) (hb1 : b < 1) :
    a ≤ (defeatFastQ a b S h0 hab hb1).1 ∧
    (defeatFastQ a b S h0 hab hb1).1 < (defeatFastQ a b S h0 hab hb1).2 ∧
    (defeatFastQ a b S h0 hab hb1).2 ≤ b ∧
    ∀ x : ℝ, x ∈ Set.Ioo ((defeatFastQ a b S h0 hab hb1).1 : ℝ)
      ((defeatFastQ a b S h0 hab hb1).2 : ℝ) → ¬ HasBestExtension x S := by
  rw [defeatFastQ_eq]
  exact PrefixInterval.defeatQ_spec a b S h0 hab hb1

end Egyptian.FastSearch
