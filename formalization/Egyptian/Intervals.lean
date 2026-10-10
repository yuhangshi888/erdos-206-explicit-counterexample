module
/-
Copyright (c) 2026 Yuhang Shi.
SPDX-License-Identifier: AGPL-3.0-only
Released under the GNU Affero General Public License, version 3 only.
-/
public import Mathlib

@[expose] public section

open Filter Set
open scoped BigOperators Topology

namespace Egyptian.Intervals

/-- Closed interval with rational endpoints, interpreted in the reals. -/
def carrier (I : ℚ × ℚ) : Set ℝ := Icc (I.1 : ℝ) (I.2 : ℝ)

/-- The exact coefficient bound used in the manuscript. -/
noncomputable def coefficientBound (p : Polynomial ℝ) : ℝ :=
  ∑ k ∈ p.support, (k : ℝ) * |p.coeff k|

theorem coefficientBound_nonneg (p : Polynomial ℝ) : 0 ≤ coefficientBound p := by
  unfold coefficientBound
  exact Finset.sum_nonneg fun k _ => mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)

theorem pow_lipschitz_unit {x z : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (hz : z ∈ Icc (0 : ℝ) 1) (k : ℕ) :
    |x ^ k - z ^ k| ≤ (k : ℝ) * |x - z| := by
  have hmax0 : 0 ≤ max |x| |z| := le_trans (abs_nonneg x) (le_max_left _ _)
  have hmax1 : max |x| |z| ≤ 1 := by
    rw [max_le_iff, abs_of_nonneg hx.1, abs_of_nonneg hz.1]
    exact ⟨hx.2, hz.2⟩
  calc
    |x ^ k - z ^ k| ≤ |x - z| * (k : ℝ) * max |x| |z| ^ (k - 1) :=
      abs_pow_sub_pow_le x z k
    _ ≤ |x - z| * (k : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left (pow_le_one₀ hmax0 hmax1)
        (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
    _ = (k : ℝ) * |x - z| := by ring

theorem polynomial_lipschitz_unit (p : Polynomial ℝ) {x z : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    |p.eval x - p.eval z| ≤ coefficientBound p * |x - z| := by
  simp only [Polynomial.eval_eq_sum, Polynomial.sum_def]
  calc
    |(∑ k ∈ p.support, p.coeff k * x ^ k) -
       (∑ k ∈ p.support, p.coeff k * z ^ k)| =
      |∑ k ∈ p.support, p.coeff k * (x ^ k - z ^ k)| := by
        rw [← Finset.sum_sub_distrib]
        congr 1
        apply Finset.sum_congr rfl
        intro k hk
        ring
    _ ≤ ∑ k ∈ p.support, |p.coeff k * (x ^ k - z ^ k)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ p.support, |p.coeff k| * ((k : ℝ) * |x - z|) := by
      apply Finset.sum_le_sum
      intro k hk
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (pow_lipschitz_unit hx hz k) (abs_nonneg _)
    _ = coefficientBound p * |x - z| := by
      unfold coefficientBound
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      ring

theorem polynomial_avoids_closed_ball (p : Polynomial ℝ) {z δ : ℝ}
    (hz : z ∈ Icc (0 : ℝ) 1) (hpz : p.eval z ≠ 0)
    (hsmall : δ ≤ |p.eval z| / (2 * (coefficientBound p + 1)))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hball : |t - z| ≤ δ) :
    p.eval t ≠ 0 := by
  have hK := coefficientBound_nonneg p
  have hden : 0 < 2 * (coefficientBound p + 1) := by positivity
  have hval : 0 < |p.eval z| := abs_pos.mpr hpz
  have hmul : δ * (2 * (coefficientBound p + 1)) ≤ |p.eval z| :=
    (le_div_iff₀ hden).mp hsmall
  have hstrict : coefficientBound p * δ < |p.eval z| / 2 := by nlinarith
  have hdiff : |p.eval t - p.eval z| < |p.eval z| / 2 :=
    lt_of_le_of_lt ((polynomial_lipschitz_unit p ht hz).trans
      (mul_le_mul_of_nonneg_left hball hK)) hstrict
  intro hzero
  rw [hzero, zero_sub, abs_neg] at hdiff
  linarith

theorem abs_sub_le_width {I : ℚ × ℚ} {x y : ℝ}
    (hx : x ∈ carrier I) (hy : y ∈ carrier I) :
    |x - y| ≤ (I.2 : ℝ) - (I.1 : ℝ) := by
  rcases hx with ⟨hxlo, hxhi⟩
  rcases hy with ⟨hylo, hyhi⟩
  rw [abs_sub_le_iff]
  constructor <;> linarith

theorem midpoint_error {I : ℚ × ℚ} {x : ℝ} (hx : x ∈ carrier I) :
    |x - (((I.1 + I.2) / 2 : ℚ) : ℝ)| ≤
      ((I.2 : ℝ) - (I.1 : ℝ)) / 2 := by
  rcases hx with ⟨hxlo, hxhi⟩
  push_cast
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- Compact nested rational intervals of shrinking width have one unique real limit. -/
theorem exists_unique_nested (I : ℕ → ℚ × ℚ)
    (hproper : ∀ n, (I n).1 < (I n).2)
    (hnested : ∀ n, carrier (I (n + 1)) ⊆ carrier (I n))
    (hwidth : ∀ n, ((I n).2 : ℝ) - ((I n).1 : ℝ) ≤ (1 / 2 : ℝ) ^ n) :
    ∃! x : ℝ, ∀ n, x ∈ carrier (I n) := by
  have hne : ∀ n, (carrier (I n)).Nonempty := by
    intro n
    exact ⟨((I n).1 : ℝ), le_rfl, (Rat.cast_lt.mpr (hproper n)).le⟩
  obtain ⟨x, hx⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      (fun n => carrier (I n)) hnested hne isCompact_Icc (fun _ => isClosed_Icc)
  have hxall : ∀ n, x ∈ carrier (I n) := mem_iInter.mp hx
  refine ⟨x, hxall, ?_⟩
  intro y hy
  have hab : ∀ n, |y - x| ≤ (1 / 2 : ℝ) ^ n := fun n =>
    (abs_sub_le_width (hy n) (hxall n)).trans (hwidth n)
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one
    (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  have hzero : |y - x| ≤ 0 := ge_of_tendsto hpow (Eventually.of_forall hab)
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hzero (abs_nonneg _)))

/-- An explicit interval stream gives the stated effective Cauchy error bound. -/
theorem midpoint_error_geometric (I : ℕ → ℚ × ℚ) {x : ℝ}
    (hx : ∀ n, x ∈ carrier (I n))
    (hwidth : ∀ n, ((I n).2 : ℝ) - ((I n).1 : ℝ) ≤ (1 / 2 : ℝ) ^ n)
    (n : ℕ) :
    |x - ((((I n).1 + (I n).2) / 2 : ℚ) : ℝ)| ≤ (1 / 2 : ℝ) ^ n / 2 := by
  exact (midpoint_error (hx n)).trans (div_le_div_of_nonneg_right (hwidth n) (by norm_num))

/-- Avoidance of all integer polynomials is the standard transcendence predicate. -/
theorem transcendental_of_integer_polynomial_avoidance {x : ℝ}
    (h : ∀ p : Polynomial ℤ, p ≠ 0 →
      (p.map (Int.castRingHom ℝ)).eval x ≠ 0) : Transcendental ℤ x := by
  rw [transcendental_iff]
  intro p hp
  by_contra hne
  apply h p hne
  simpa only [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, algebraMap_int_eq] using hp

/-- Rational version of the coefficient bound; this is executable. -/
def coefficientBoundQ (p : Polynomial ℚ) : ℚ :=
  ∑ k ∈ p.support, (k : ℚ) * |p.coeff k|

theorem coefficientBoundQ_nonneg (p : Polynomial ℚ) : 0 ≤ coefficientBoundQ p := by
  unfold coefficientBoundQ
  exact Finset.sum_nonneg fun k _ => mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)

@[simp] theorem cast_coefficientBoundQ (p : Polynomial ℚ) :
    (coefficientBoundQ p : ℝ) = coefficientBound (p.map (Rat.castHom ℝ)) := by
  unfold coefficientBoundQ coefficientBound
  rw [Polynomial.support_map_of_injective p Rat.cast_injective]
  simp only [Rat.cast_sum, Rat.cast_mul, Rat.cast_natCast, Rat.cast_abs, Polynomial.coeff_map]
  rfl

@[simp] theorem cast_evalQ (p : Polynomial ℚ) (z : ℚ) :
    (p.map (Rat.castHom ℝ)).eval (z : ℝ) = ((p.eval z : ℚ) : ℝ) := by
  simpa only [Polynomial.eval₂_eq_eval_map, Rat.coe_castHom] using
    (Polynomial.eval₂_at_apply (Rat.castHom ℝ) z (p := p))

/-- The exact four-way minimum in the construction; all data are rational. -/
def radiusQ (L U z : ℚ) (p : Polynomial ℚ) (j : ℕ) : ℚ :=
  min (min (min ((z - L) / 2) ((U - z) / 2)) ((1 / 2 : ℚ) ^ (j + 1)))
    (|p.eval z| / (2 * (coefficientBoundQ p + 1)))

def narrowQ (L U z : ℚ) (p : Polynomial ℚ) (j : ℕ) : ℚ × ℚ :=
  (z - radiusQ L U z p j, z + radiusQ L U z p j)

theorem radiusQ_properties {L U z : ℚ} (p : Polynomial ℚ) (j : ℕ)
    (hL : L < z) (hU : z < U) (hp : p.eval z ≠ 0) :
    0 < radiusQ L U z p j ∧
    radiusQ L U z p j ≤ (z - L) / 2 ∧
    radiusQ L U z p j ≤ (U - z) / 2 ∧
    radiusQ L U z p j ≤ (1 / 2 : ℚ) ^ (j + 1) ∧
    radiusQ L U z p j ≤ |p.eval z| / (2 * (coefficientBoundQ p + 1)) := by
  have hK := coefficientBoundQ_nonneg p
  have hv : 0 < |p.eval z| := abs_pos.mpr hp
  have hpos : 0 < radiusQ L U z p j := by
    unfold radiusQ
    simp only [lt_min_iff]
    refine ⟨⟨⟨by linarith, by linarith⟩, by positivity⟩, ?_⟩
    positivity
  refine ⟨hpos, ?_, ?_, ?_, ?_⟩
  · exact (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  · exact (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  · exact (min_le_left _ _).trans (min_le_right _ _)
  · exact min_le_right _ _

theorem narrowQ_properties {L U z : ℚ} (p : Polynomial ℚ) (j : ℕ)
    (hL : L < z) (hU : z < U) (hp : p.eval z ≠ 0) :
    L < (narrowQ L U z p j).1 ∧
    (narrowQ L U z p j).1 < (narrowQ L U z p j).2 ∧
    (narrowQ L U z p j).2 < U ∧
    (narrowQ L U z p j).2 - (narrowQ L U z p j).1 ≤ (1 / 2 : ℚ) ^ j := by
  have h := radiusQ_properties p j hL hU hp
  dsimp [narrowQ]
  refine ⟨by linarith [h.2.1], by linarith [h.1], by linarith [h.2.2.1], ?_⟩
  have hpow : (1 / 2 : ℚ) ^ (j + 1) = (1 / 2 : ℚ) ^ j / 2 := by
    rw [pow_succ]
    ring
  have hb := h.2.2.2.1
  rw [hpow] at hb
  linarith

theorem narrowQ_polynomial_avoidance {L U z : ℚ} (p : Polynomial ℚ) (j : ℕ)
    (hL0 : 0 < L) (hU1 : U < 1) (hL : L < z) (hU : z < U)
    (hp : p.eval z ≠ 0) {x : ℝ} (hx : x ∈ carrier (narrowQ L U z p j)) :
    (p.map (Rat.castHom ℝ)).eval x ≠ 0 := by
  have hr := radiusQ_properties p j hL hU hp
  have hn := narrowQ_properties p j hL hU hp
  have hz0 : 0 ≤ (z : ℝ) := by exact_mod_cast (lt_trans hL0 hL).le
  have hz1 : (z : ℝ) ≤ 1 := by exact_mod_cast (lt_trans hU hU1).le
  have hlo : 0 < ((narrowQ L U z p j).1 : ℝ) := by
    exact_mod_cast (lt_trans hL0 hn.1)
  have hhi : ((narrowQ L U z p j).2 : ℝ) < 1 := by
    exact_mod_cast (lt_trans hn.2.2.1 hU1)
  have hxunit : x ∈ Icc (0 : ℝ) 1 := ⟨hlo.le.trans hx.1, hx.2.trans hhi.le⟩
  have hball : |x - (z : ℝ)| ≤ (radiusQ L U z p j : ℝ) := by
    rcases hx with ⟨hxlo, hxhi⟩
    dsimp [carrier, narrowQ] at hxlo hxhi
    push_cast at hxlo hxhi
    rw [abs_sub_le_iff]
    constructor <;> linarith
  have hsmall : (radiusQ L U z p j : ℝ) ≤
      |(p.map (Rat.castHom ℝ)).eval (z : ℝ)| /
        (2 * (coefficientBound (p.map (Rat.castHom ℝ)) + 1)) := by
    have hc : (radiusQ L U z p j : ℝ) ≤
        ((|p.eval z| / (2 * (coefficientBoundQ p + 1)) : ℚ) : ℝ) :=
      Rat.cast_le.mpr hr.2.2.2.2
    push_cast at hc
    simpa using hc
  apply polynomial_avoids_closed_ball (p.map (Rat.castHom ℝ)) ⟨hz0, hz1⟩
  · simp only [cast_evalQ, ne_eq, Rat.cast_eq_zero]
    exact hp
  · exact hsmall
  · exact hxunit
  · exact hball

end Egyptian.Intervals
