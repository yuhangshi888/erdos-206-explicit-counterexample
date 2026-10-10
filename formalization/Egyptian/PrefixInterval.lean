module
/-
Copyright (c) 2026 Yuhang Shi.
SPDX-License-Identifier: AGPL-3.0-only
Released under the GNU Affero General Public License, version 3 only.
-/
public import Egyptian.Greedy
public import Egyptian.Defeat

@[expose] public section

/-!
The manuscript's rational prefix-defeat routine. The upper bound starts at b
and records a predecessor cap only when a greedy step skips a denominator.
-/

namespace Egyptian.PrefixInterval

def stepDenomQ (c : ℚ) (S : Prefix) (n : ℕ) : ℕ :=
  greedyDenomQ c (greedyIterQ c S n).sumQ (greedyIterQ c S n).last

def skippedQ (c : ℚ) (S : Prefix) (n : ℕ) : Prop :=
  (greedyIterQ c S n).last + 1 < stepDenomQ c S n

instance (c : ℚ) (S : Prefix) (n : ℕ) : Decidable (skippedQ c S n) :=
  inferInstanceAs (Decidable ((greedyIterQ c S n).last + 1 < stepDenomQ c S n))

def stepCapQ (c : ℚ) (S : Prefix) (n : ℕ) : ℚ :=
  (greedyIterQ c S n).sumQ + unitQ (stepDenomQ c S n - 1)

def capsFoldQ (b c : ℚ) (S : Prefix) : ℕ → ℚ
  | 0 => b
  | n + 1 =>
    if skippedQ c S n then min (capsFoldQ b c S n) (stepCapQ c S n)
    else capsFoldQ b c S n

@[simp] theorem next_last (c : ℚ) (S : Prefix) (n : ℕ) :
    (greedyIterQ c S (n + 1)).last = stepDenomQ c S n := by
  simp [stepDenomQ]

theorem stepCapQ_ge_target {c : ℚ} (S : Prefix) (hq : S.sumQ < c)
    (n : ℕ) (hs : skippedQ c S n) : c ≤ stepCapQ c S n := by
  have hl : IsLeastAllowed (c : ℝ) (greedyIterQ c S n).sum
      (greedyIterQ c S n).last (stepDenomQ c S n) := by
    simpa only [next_last] using greedyIterQ_least S hq n
  have hr := least_allowed_cap hl hs
  apply (Rat.cast_le (K := ℝ)).mp
  simpa only [stepCapQ, Rat.cast_add, Prefix.cast_sumQ, cast_unitQ] using hr

theorem capsFoldQ_ge_target {b c : ℚ} (S : Prefix) (hq : S.sumQ < c)
    (hcb : c ≤ b) (N : ℕ) : c ≤ capsFoldQ b c S N := by
  induction N with
  | zero => exact hcb
  | succ n ih =>
    rw [capsFoldQ]
    split_ifs with hs
    · exact le_min ih (stepCapQ_ge_target S hq n hs)
    · exact ih

theorem capsFoldQ_antitone (b c : ℚ) (S : Prefix) : Antitone (capsFoldQ b c S) := by
  apply antitone_nat_of_succ_le
  intro n
  rw [capsFoldQ]
  split_ifs
  · exact min_le_left _ _
  · exact le_rfl

theorem capsFoldQ_le_initial (b c : ℚ) (S : Prefix) (N : ℕ) :
    capsFoldQ b c S N ≤ b := by
  simpa only [capsFoldQ] using capsFoldQ_antitone b c S (Nat.zero_le N)

theorem capsFoldQ_le_recorded (b c : ℚ) (S : Prefix) (N n : ℕ)
    (hn : n < N) (hs : skippedQ c S n) :
    capsFoldQ b c S N ≤ stepCapQ c S n := by
  have hstep : capsFoldQ b c S (n + 1) ≤ stepCapQ c S n := by
    rw [capsFoldQ, ite_eq_left hs]
    exact min_le_right _ _
  exact le_trans (capsFoldQ_antitone b c S (by omega : n + 1 ≤ N)) hstep

theorem greedyIterQ_stable_caps {c : ℚ} (b : ℚ) (S : Prefix) (hq : S.sumQ < c)
    (N n : ℕ) (hn : n < N) {x : ℝ}
    (hx : (greedyIterQ c S N).sum < x) (hu : x < (capsFoldQ b c S N : ℝ)) :
    IsLeastAllowed x (greedyIterQ c S n).sum (greedyIterQ c S n).last
      (greedyIterQ c S (n + 1)).last := by
  apply least_allowed_stable_cap (greedyIterQ_least S hq n)
  · rw [← greedyIterQ_sum_succ]
    exact lt_of_le_of_lt (greedyIterQ_sum_mono c S (by omega : n + 1 ≤ N)) hx
  · intro hs
    have hs' : skippedQ c S n := by simpa only [next_last, skippedQ] using hs
    have hbound := capsFoldQ_le_recorded b c S N n hn hs'
    have hboundr : (capsFoldQ b c S N : ℝ) ≤
        (greedyIterQ c S n).sum + unit (stepDenomQ c S n - 1) := by
      have hr := (Rat.cast_le (K := ℝ)).mpr hbound
      simpa only [stepCapQ, Rat.cast_add, Prefix.cast_sumQ, cast_unitQ] using hr
    simpa only [next_last] using lt_of_lt_of_le hu hboundr

/-- Executable finite greedy block, together with the already-proved bounds
and the transport property of every optimal extension across that block. -/
structure CutData (a b : ℚ) (S : Prefix) where
  count : ℕ
  extended : Prefix
  cap : ℚ
  extended_eq : extended = greedyIterQ ((a + b) / 2) S count
  cap_eq : cap = capsFoldQ b ((a + b) / 2) S count
  q_above : a < extended.sumQ
  q_below : extended.sumQ < (a + b) / 2
  cap_ge_mid : (a + b) / 2 ≤ cap
  cap_le_b : cap ≤ b
  extension : ∀ x : ℝ, extended.sum < x → x < (cap : ℝ) →
    HasBestExtension x S → HasBestExtension x extended

def makeCutQ (a b : ℚ) (S : Prefix) (hab : a < b) (hq : S.sumQ ≤ a) :
    CutData a b S := by
  let c : ℚ := (a + b) / 2
  have hac : a < c := by dsimp [c]; linarith
  have hcb : c ≤ b := by dsimp [c]; linarith
  have hqc : S.sumQ < c := lt_of_le_of_lt hq hac
  let N := crossingTimeQ c a S hqc hac
  let T := greedyIterQ c S N
  let B := capsFoldQ b c S N
  have hcross := crossingTimeQ_spec c a S hqc hac
  refine ⟨N, T, B, rfl, rfl, hcross.1, hcross.2,
    capsFoldQ_ge_target S hqc hcb N, capsFoldQ_le_initial b c S N, ?_⟩
  intro x hx hu hext
  exact hasBestExtension_greedyIterQ hext N
    (fun n hn => greedyIterQ_stable_caps b S hqc N n hn hx hu)

def badIndexQ (M : ℕ) (ε : ℚ) (hε : 0 < ε) : ℕ :=
  Nat.find (BadPair.exists_large_rat_index M ε hε)

theorem badIndexQ_spec (M : ℕ) (ε : ℚ) (hε : 0 < ε) :
    3 ≤ badIndexQ M ε hε ∧ M < badIndexQ M ε hε ∧
      BadPair.uRat (badIndexQ M ε hε) < ε :=
  Nat.find_spec (BadPair.exists_large_rat_index M ε hε)

theorem badIndexQ_min (M : ℕ) (ε : ℚ) (hε : 0 < ε) (i : ℕ)
    (hi : 3 ≤ i) (hM : M < i) (hu : BadPair.uRat i < ε) :
    badIndexQ M ε hε ≤ i :=
  Nat.find_min' (BadPair.exists_large_rat_index M ε hε) ⟨hi, hM, hu⟩

theorem CutData.gap_pos {a b : ℚ} {S : Prefix} (C : CutData a b S) :
    0 < C.cap - C.extended.sumQ := by
  linarith [C.q_below, C.cap_ge_mid]

def intervalOfCutQ {a b : ℚ} {S : Prefix} (C : CutData a b S) : ℚ × ℚ :=
  let i := badIndexQ C.extended.last (C.cap - C.extended.sumQ) C.gap_pos
  (C.extended.sumQ + BadPair.rRat i, C.extended.sumQ + BadPair.uRat i)

theorem intervalOfCutQ_spec {a b : ℚ} {S : Prefix} (C : CutData a b S) :
    a ≤ (intervalOfCutQ C).1 ∧
    (intervalOfCutQ C).1 < (intervalOfCutQ C).2 ∧
    (intervalOfCutQ C).2 ≤ b ∧
    ∀ x : ℝ, x ∈ Set.Ioo ((intervalOfCutQ C).1 : ℝ) ((intervalOfCutQ C).2 : ℝ) →
      ¬ HasBestExtension x S := by
  let i := badIndexQ C.extended.last (C.cap - C.extended.sumQ) C.gap_pos
  have hi := badIndexQ_spec C.extended.last (C.cap - C.extended.sumQ) C.gap_pos
  have hi3 : 3 ≤ i := hi.1
  have hMi : C.extended.last < i := hi.2.1
  have hui : BadPair.uRat i < C.cap - C.extended.sumQ := hi.2.2
  have hr0r : (0 : ℝ) < (BadPair.rRat i : ℝ) := by
    simpa using BadPair.r_pos i hi3
  have hr0 : (0 : ℚ) < BadPair.rRat i := Rat.cast_pos.mp hr0r
  have hru := (BadPair.bounds_rat i hi3).2.1
  change a ≤ C.extended.sumQ + BadPair.rRat i ∧
    C.extended.sumQ + BadPair.rRat i < C.extended.sumQ + BadPair.uRat i ∧
    C.extended.sumQ + BadPair.uRat i ≤ b ∧ _
  refine ⟨by linarith [C.q_above], by linarith, by linarith [C.cap_le_b], ?_⟩
  intro x hx hext
  have hlo : C.extended.sum + BadPair.r i < x := by
    have h := hx.1
    change ((C.extended.sumQ + BadPair.rRat i : ℚ) : ℝ) < x at h
    simpa only [Rat.cast_add, Prefix.cast_sumQ, BadPair.cast_rRat] using h
  have hhi : x < C.extended.sum + BadPair.u i := by
    have h := hx.2
    change x < ((C.extended.sumQ + BadPair.uRat i : ℚ) : ℝ) at h
    simpa only [Rat.cast_add, Prefix.cast_sumQ, BadPair.cast_uRat] using h
  have hq : C.extended.sum < x := by linarith [BadPair.r_pos i hi3]
  have hcap : x < (C.cap : ℝ) := by
    have huq : C.extended.sumQ + BadPair.uRat i < C.cap := by linarith
    have hur := (Rat.cast_lt (K := ℝ)).mpr huq
    have hu' : C.extended.sum + BadPair.u i < (C.cap : ℝ) := by
      simpa only [Rat.cast_add, Prefix.cast_sumQ, BadPair.cast_uRat] using hur
    exact lt_trans hhi hu'
  exact not_hasBestExtension_bad_pair C.extended i hi3 hMi x
    (by linarith) (by linarith) (C.extension x hq hcap hext)

/-- The exact manuscript routine, including its infeasible-prefix branch.
The outer positivity bounds are accepted to fit the global interval interface. -/
def defeatQ (a b : ℚ) (S : Prefix) (_h0 : 0 < a) (hab : a < b) (_hb1 : b < 1) :
    ℚ × ℚ :=
  if h : a < S.sumQ then (a, min b S.sumQ)
  else intervalOfCutQ (makeCutQ a b S hab (le_of_not_gt h))

theorem defeatQ_spec (a b : ℚ) (S : Prefix) (h0 : 0 < a) (hab : a < b) (hb1 : b < 1) :
    a ≤ (defeatQ a b S h0 hab hb1).1 ∧
    (defeatQ a b S h0 hab hb1).1 < (defeatQ a b S h0 hab hb1).2 ∧
    (defeatQ a b S h0 hab hb1).2 ≤ b ∧
    ∀ x : ℝ, x ∈ Set.Ioo ((defeatQ a b S h0 hab hb1).1 : ℝ)
      ((defeatQ a b S h0 hab hb1).2 : ℝ) → ¬ HasBestExtension x S := by
  by_cases h : a < S.sumQ
  · simp only [defeatQ, dite_eq_left h]
    refine ⟨le_rfl, lt_min hab h, min_le_left _ _, ?_⟩
    intro x hx hext
    have hxq : x < S.sum := by
      have hqr := (Rat.cast_le (K := ℝ)).mpr (min_le_right b S.sumQ)
      have hqr' : ((min b S.sumQ : ℚ) : ℝ) ≤ S.sum := by
        simpa only [Prefix.cast_sumQ] using hqr
      exact lt_of_lt_of_le hx.2 hqr'
    obtain ⟨F, hF0, _, hbest⟩ := hext
    have hb : BestUnder x S := by simpa only [hF0] using hbest 0
    linarith [hb.1]
  · simpa only [defeatQ, dite_eq_right h] using
      intervalOfCutQ_spec (makeCutQ a b S hab (le_of_not_gt h))

end Egyptian.PrefixInterval
