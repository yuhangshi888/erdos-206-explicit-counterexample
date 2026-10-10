module
/-
Copyright (c) 2026 Yuhang Shi.
SPDX-License-Identifier: AGPL-3.0-only
Released under the GNU Affero General Public License, version 3 only.
-/
public import Egyptian.PrefixInterval
public import Egyptian.FastSearch
public import Egyptian.PrefixEnumeration
public import Egyptian.Intervals
public import Egyptian.PolynomialGrid
public import Egyptian.Chains

@[expose] public section

/-! The full rational recursion, its unique real limit, and the two universal
avoidance conclusions. The polynomial stream is a parameter here; Main.lean
instantiates it with the manuscript's executable height/degree/lex stream. -/

namespace Egyptian.Construction

open Set
open Egyptian.Intervals

structure RationalInterval where
  lower : ℚ
  upper : ℚ
  lower_pos : 0 < lower
  proper : lower < upper
  upper_lt_one : upper < 1

def RationalInterval.pair (I : RationalInterval) : ℚ × ℚ := (I.lower, I.upper)

def initial : RationalInterval := ⟨1/4, 1/3, by norm_num, by norm_num, by norm_num⟩

def refinePair (I : RationalInterval) (S : Prefix) (p : Polynomial ℚ)
    (hp : p ≠ 0) (j : ℕ) : ℚ × ℚ :=
  let J := FastSearch.defeatFastQ I.lower I.upper S
    I.lower_pos I.proper I.upper_lt_one
  let hJ := FastSearch.defeatFastQ_spec I.lower I.upper S
    I.lower_pos I.proper I.upper_lt_one
  let z := PolynomialGrid.sample p hp J.1 J.2 hJ.2.1
  narrowQ J.1 J.2 z p j

theorem refinePair_spec (I : RationalInterval) (S : Prefix) (p : Polynomial ℚ)
    (hp : p ≠ 0) (j : ℕ) :
    I.lower < (refinePair I S p hp j).1 ∧
    (refinePair I S p hp j).1 < (refinePair I S p hp j).2 ∧
    (refinePair I S p hp j).2 < I.upper ∧
    (refinePair I S p hp j).2 - (refinePair I S p hp j).1 ≤ (1/2 : ℚ)^j ∧
    ∀ x : ℝ, x ∈ carrier (refinePair I S p hp j) →
      ¬ HasBestExtension x S ∧ (p.map (Rat.castHom ℝ)).eval x ≠ 0 := by
  let J := FastSearch.defeatFastQ I.lower I.upper S
    I.lower_pos I.proper I.upper_lt_one
  have hJ := FastSearch.defeatFastQ_spec I.lower I.upper S
    I.lower_pos I.proper I.upper_lt_one
  change I.lower ≤ J.1 ∧ J.1 < J.2 ∧ J.2 ≤ I.upper ∧
    (∀ x : ℝ, x ∈ Ioo (J.1 : ℝ) (J.2 : ℝ) → ¬ HasBestExtension x S) at hJ
  let z := PolynomialGrid.sample p hp J.1 J.2 hJ.2.1
  have hz := PolynomialGrid.sample_inside p hp J.1 J.2 hJ.2.1
  have hroot := PolynomialGrid.sample_nonroot p hp J.1 J.2 hJ.2.1
  change J.1 < z ∧ z < J.2 at hz
  change p.eval z ≠ 0 at hroot
  have hn := narrowQ_properties p j hz.1 hz.2 hroot
  change I.lower < (narrowQ J.1 J.2 z p j).1 ∧
    (narrowQ J.1 J.2 z p j).1 < (narrowQ J.1 J.2 z p j).2 ∧
    (narrowQ J.1 J.2 z p j).2 < I.upper ∧
    (narrowQ J.1 J.2 z p j).2 - (narrowQ J.1 J.2 z p j).1 ≤ (1/2 : ℚ)^j ∧
    _
  refine ⟨lt_of_le_of_lt hJ.1 hn.1, hn.2.1,
    lt_of_lt_of_le hn.2.2.1 hJ.2.2.1, hn.2.2.2, ?_⟩
  intro x hx
  have hxJ : x ∈ Ioo (J.1 : ℝ) (J.2 : ℝ) := by
    have hlo : (J.1 : ℝ) < ((narrowQ J.1 J.2 z p j).1 : ℝ) :=
      Rat.cast_lt.mpr hn.1
    have hhi : ((narrowQ J.1 J.2 z p j).2 : ℝ) < (J.2 : ℝ) :=
      Rat.cast_lt.mpr hn.2.2.1
    exact ⟨hlo.trans_le hx.1, hx.2.trans_lt hhi⟩
  refine ⟨hJ.2.2.2 x hxJ, ?_⟩
  exact narrowQ_polynomial_avoidance p j
    (lt_of_lt_of_le I.lower_pos hJ.1)
    (lt_of_le_of_lt hJ.2.2.1 I.upper_lt_one) hz.1 hz.2 hroot hx

def refine (I : RationalInterval) (S : Prefix) (p : Polynomial ℚ)
    (hp : p ≠ 0) (j : ℕ) : RationalInterval :=
  let J := refinePair I S p hp j
  let hJ := refinePair_spec I S p hp j
  ⟨J.1, J.2, I.lower_pos.trans hJ.1, hJ.2.1, hJ.2.2.1.trans I.upper_lt_one⟩

@[simp] theorem refine_pair (I : RationalInterval) (S : Prefix) (p : Polynomial ℚ)
    (hp : p ≠ 0) (j : ℕ) : (refine I S p hp j).pair = refinePair I S p hp j := rfl

def interval (P : ℕ → Polynomial ℚ) (hne : ∀ n, P n ≠ 0) : ℕ → RationalInterval
  | 0 => initial
  | n + 1 => refine (interval P hne n) (prefixAt n) (P n) (hne n) (n + 1)

def intervals (P : ℕ → Polynomial ℚ) (hne : ∀ n, P n ≠ 0) (n : ℕ) : ℚ × ℚ :=
  (interval P hne n).pair

theorem interval_succ (P : ℕ → Polynomial ℚ) (hne : ∀ n, P n ≠ 0) (n : ℕ) :
    intervals P hne (n+1) =
      refinePair (interval P hne n) (prefixAt n) (P n) (hne n) (n+1) := rfl

theorem intervals_proper (P : ℕ → Polynomial ℚ) (hne : ∀ n, P n ≠ 0) (n : ℕ) :
    (intervals P hne n).1 < (intervals P hne n).2 := (interval P hne n).proper

theorem intervals_nested (P : ℕ → Polynomial ℚ) (hne : ∀ n, P n ≠ 0) (n : ℕ) :
    carrier (intervals P hne (n+1)) ⊆ carrier (intervals P hne n) := by
  have h := refinePair_spec (interval P hne n) (prefixAt n) (P n) (hne n) (n+1)
  rw [← interval_succ] at h
  intro x hx
  have hlo : ((intervals P hne n).1 : ℝ) < ((intervals P hne (n+1)).1 : ℝ) :=
    Rat.cast_lt.mpr h.1
  have hhi : ((intervals P hne (n+1)).2 : ℝ) < ((intervals P hne n).2 : ℝ) :=
    Rat.cast_lt.mpr h.2.2.1
  exact ⟨hlo.le.trans hx.1, hx.2.trans hhi.le⟩

theorem intervals_widthQ (P : ℕ → Polynomial ℚ) (hne : ∀ n, P n ≠ 0) (n : ℕ) :
    (intervals P hne n).2 - (intervals P hne n).1 ≤ (1/2 : ℚ)^n := by
  cases n with
  | zero => norm_num [intervals, interval, RationalInterval.pair, initial]
  | succ n =>
    have h := refinePair_spec (interval P hne n) (prefixAt n) (P n) (hne n) (n+1)
    rw [← interval_succ] at h
    exact h.2.2.2.1

theorem intervals_width (P : ℕ → Polynomial ℚ) (hne : ∀ n, P n ≠ 0) (n : ℕ) :
    ((intervals P hne n).2 : ℝ) - ((intervals P hne n).1 : ℝ) ≤ (1/2 : ℝ)^n := by
  have h := (Rat.cast_le (K := ℝ)).mpr (intervals_widthQ P hne n)
  simpa only [Rat.cast_sub, Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h

theorem unique_limit (P : ℕ → Polynomial ℚ) (hne : ∀ n, P n ≠ 0) :
    ∃! x : ℝ, ∀ n, x ∈ carrier (intervals P hne n) :=
  exists_unique_nested (intervals P hne) (intervals_proper P hne)
    (intervals_nested P hne) (intervals_width P hne)

noncomputable def limit (P : ℕ → Polynomial ℚ) (hne : ∀ n, P n ≠ 0) : ℝ :=
  Classical.choose (unique_limit P hne)

theorem limit_mem (P : ℕ → Polynomial ℚ) (hne : ∀ n, P n ≠ 0) (n : ℕ) :
    limit P hne ∈ carrier (intervals P hne n) :=
  (Classical.choose_spec (unique_limit P hne)).1 n

theorem limit_range (P : ℕ → Polynomial ℚ) (hne : ∀ n, P n ≠ 0) :
    (1/4 : ℝ) < limit P hne ∧ limit P hne < (1/3 : ℝ) := by
  have hx := limit_mem P hne 1
  have h := refinePair_spec initial (prefixAt 0) (P 0) (hne 0) 1
  have hlo : (1/4 : ℝ) < ((intervals P hne 1).1 : ℝ) := by
    have hq : (1/4 : ℚ) < (intervals P hne 1).1 := h.1
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using (Rat.cast_lt (K := ℝ)).mpr hq
  have hhi : ((intervals P hne 1).2 : ℝ) < (1/3 : ℝ) := by
    have hq : (intervals P hne 1).2 < (1/3 : ℚ) := h.2.2.1
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using (Rat.cast_lt (K := ℝ)).mpr hq
  exact ⟨hlo.trans_le hx.1, hx.2.trans_lt hhi⟩

theorem limit_no_best_extension (P : ℕ → Polynomial ℚ) (hne : ∀ n, P n ≠ 0)
    (S : Prefix) : ¬ HasBestExtension (limit P hne) S := by
  obtain ⟨n, rfl⟩ := prefixAt_surjective S
  have h := refinePair_spec (interval P hne n) (prefixAt n) (P n) (hne n) (n+1)
  rw [← interval_succ] at h
  exact (h.2.2.2.2 _ (limit_mem P hne (n+1))).1

theorem limit_not_eventuallyGreedy (P : ℕ → Polynomial ℚ) (hne : ∀ n, P n ≠ 0) :
    ¬ EventuallyGreedy (limit P hne) :=
  not_eventuallyGreedy_of_no_best_extension (limit_no_best_extension P hne)

theorem limit_avoids_stream (P : ℕ → Polynomial ℚ) (hne : ∀ n, P n ≠ 0) (n : ℕ) :
    ((P n).map (Rat.castHom ℝ)).eval (limit P hne) ≠ 0 := by
  have h := refinePair_spec (interval P hne n) (prefixAt n) (P n) (hne n) (n+1)
  rw [← interval_succ] at h
  exact (h.2.2.2.2 _ (limit_mem P hne (n+1))).2

theorem limit_transcendental (P : ℕ → Polynomial ℚ) (hne : ∀ n, P n ≠ 0)
    (hcover : ∀ p : Polynomial ℤ, p ≠ 0 → ∃ n, P n = p.map (Int.castRingHom ℚ)) :
    Transcendental ℤ (limit P hne) := by
  apply transcendental_of_integer_polynomial_avoidance
  intro p hp
  obtain ⟨n, hn⟩ := hcover p hp
  have h := limit_avoids_stream P hne n
  rw [hn, Polynomial.map_map] at h
  have hf : (Rat.castHom ℝ).comp (Int.castRingHom ℚ) = Int.castRingHom ℝ := by
    ext a
    simp
  simpa only [hf] using h

def midpoint (P : ℕ → Polynomial ℚ) (hne : ∀ n, P n ≠ 0) (n : ℕ) : ℚ :=
  ((intervals P hne n).1 + (intervals P hne n).2) / 2

theorem midpoint_error_bound (P : ℕ → Polynomial ℚ) (hne : ∀ n, P n ≠ 0)
    (n : ℕ) : |limit P hne - (midpoint P hne n : ℝ)| ≤ (1/2 : ℝ)^n / 2 := by
  have h := midpoint_error_geometric (intervals P hne) (limit_mem P hne)
    (intervals_width P hne) n
  simpa only [midpoint, Rat.cast_div, Rat.cast_add, Rat.cast_ofNat] using h

end Egyptian.Construction
