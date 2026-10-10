module
/-
Copyright (c) 2026 Yuhang Shi.
SPDX-License-Identifier: AGPL-3.0-only
Released under the GNU Affero General Public License, version 3 only.
-/
public import Mathlib

@[expose] public section

/-! An exact finite rational grid always contains a nonroot of a nonzero
polynomial. The least such grid index is an executable natural-number search. -/

namespace Egyptian.PolynomialGrid

/-- The manuscript's `k`th grid sample between rational endpoints. -/
def point (d : ℕ) (L U : ℚ) (k : ℕ) : ℚ :=
  L + (k : ℚ) / ((d : ℚ) + 2) * (U - L)

theorem point_injective {d : ℕ} {L U : ℚ} (hLU : L < U) :
    Function.Injective (point d L U) := by
  intro i j hij
  have hden : (0 : ℚ) < (d : ℚ) + 2 := by positivity
  have hdiff : (0 : ℚ) < U - L := sub_pos.mpr hLU
  have heq : (i : ℚ) = (j : ℚ) := by
    unfold point at hij
    have hcancel : (i : ℚ) / ((d : ℚ) + 2) =
        (j : ℚ) / ((d : ℚ) + 2) := by nlinarith
    have hm := congrArg (fun t : ℚ => t * ((d : ℚ) + 2)) hcancel
    simpa [div_mul_cancel₀ _ (ne_of_gt hden)] using hm
  exact_mod_cast heq

theorem point_inside {d k : ℕ} {L U : ℚ} (hLU : L < U)
    (hklo : 1 ≤ k) (hkhi : k ≤ d + 1) :
    L < point d L U k ∧ point d L U k < U := by
  have hden : (0 : ℚ) < (d : ℚ) + 2 := by positivity
  have hkpos : (0 : ℚ) < k := by exact_mod_cast (show 0 < k by omega)
  have hklt : (k : ℚ) < (d : ℚ) + 2 := by
    exact_mod_cast (show k < d + 2 by omega)
  have hfracpos : (0 : ℚ) < (k : ℚ) / ((d : ℚ) + 2) := div_pos hkpos hden
  have hfraclt : (k : ℚ) / ((d : ℚ) + 2) < 1 := (div_lt_one hden).mpr hklt
  unfold point
  constructor <;> nlinarith

/-- The `d+1` distinct interior grid points cannot all be roots. -/
theorem exists_good (p : Polynomial ℚ) (hp : p ≠ 0) {L U : ℚ}
    (hLU : L < U) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ p.natDegree + 1 ∧
      p.eval (point p.natDegree L U k) ≠ 0 := by
  classical
  by_contra hnone
  have hzero : ∀ k : ℕ, 1 ≤ k → k ≤ p.natDegree + 1 →
      p.eval (point p.natDegree L U k) = 0 := by
    intro k hklo hkhi
    by_contra hne
    exact hnone ⟨k, hklo, hkhi, hne⟩
  let f : Fin (p.natDegree + 1) → ℚ :=
    fun i => point p.natDegree L U (i.val + 1)
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    have hidx := point_injective hLU hij
    omega
  have heval : ∀ i, p.eval (f i) = 0 := by
    intro i
    apply hzero (i.val + 1) (by omega)
    have hi := i.isLt
    omega
  exact hp (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero p hf heval
    (by simp))

/-- Decidable finite-grid success predicate; its arithmetic is over `ℚ`. -/
def Good (p : Polynomial ℚ) (L U : ℚ) (k : ℕ) : Prop :=
  1 ≤ k ∧ k ≤ p.natDegree + 1 ∧ p.eval (point p.natDegree L U k) ≠ 0

instance goodDecidable (p : Polynomial ℚ) (L U : ℚ) : DecidablePred (Good p L U) :=
  fun k => inferInstanceAs (Decidable (1 ≤ k ∧ k ≤ p.natDegree + 1 ∧
    p.eval (point p.natDegree L U k) ≠ 0))

/-- Least successful index, computed by `Nat.find`; no choice of roots is used. -/
def leastGood (p : Polynomial ℚ) (hp : p ≠ 0) (L U : ℚ) (hLU : L < U) : ℕ :=
  Nat.find (exists_good p hp hLU)

theorem leastGood_spec (p : Polynomial ℚ) (hp : p ≠ 0) (L U : ℚ) (hLU : L < U) :
    Good p L U (leastGood p hp L U hLU) :=
  Nat.find_spec (exists_good p hp hLU)

theorem leastGood_bounds (p : Polynomial ℚ) (hp : p ≠ 0) (L U : ℚ) (hLU : L < U) :
    1 ≤ leastGood p hp L U hLU ∧ leastGood p hp L U hLU ≤ p.natDegree + 1 :=
  ⟨(leastGood_spec p hp L U hLU).1, (leastGood_spec p hp L U hLU).2.1⟩

theorem leastGood_minimal (p : Polynomial ℚ) (hp : p ≠ 0) (L U : ℚ) (hLU : L < U)
    {k : ℕ} (hk : Good p L U k) : leastGood p hp L U hLU ≤ k :=
  Nat.find_min' (exists_good p hp hLU) hk

/-- The deterministic rational point selected by the finite-grid search. -/
def sample (p : Polynomial ℚ) (hp : p ≠ 0) (L U : ℚ) (hLU : L < U) : ℚ :=
  point p.natDegree L U (leastGood p hp L U hLU)

theorem sample_inside (p : Polynomial ℚ) (hp : p ≠ 0) (L U : ℚ) (hLU : L < U) :
    L < sample p hp L U hLU ∧ sample p hp L U hLU < U :=
  point_inside hLU (leastGood_bounds p hp L U hLU).1
    (leastGood_bounds p hp L U hLU).2

theorem sample_nonroot (p : Polynomial ℚ) (hp : p ≠ 0) (L U : ℚ) (hLU : L < U) :
    p.eval (sample p hp L U hLU) ≠ 0 :=
  (leastGood_spec p hp L U hLU).2.2

/-- Enumerated integer polynomials remain nonzero over the exact search field. -/
theorem map_int_nonzero (p : Polynomial ℤ) (hp : p ≠ 0) :
    p.map (Int.castRingHom ℚ) ≠ 0 :=
  (Polynomial.map_ne_zero_iff (f := Int.castRingHom ℚ) Int.cast_injective).mpr hp

/-- The rational evaluation certificate is also a real evaluation certificate. -/
theorem cast_eval (p : Polynomial ℚ) (z : ℚ) :
    (p.map (Rat.castHom ℝ)).eval (z : ℝ) = ((p.eval z : ℚ) : ℝ) := by
  simpa using Polynomial.eval_map_apply (Rat.castHom ℝ) (p := p) z

theorem sample_nonroot_real (p : Polynomial ℚ) (hp : p ≠ 0) (L U : ℚ)
    (hLU : L < U) :
    (p.map (Rat.castHom ℝ)).eval (sample p hp L U hLU : ℝ) ≠ 0 := by
  rw [cast_eval]
  exact_mod_cast sample_nonroot p hp L U hLU

end Egyptian.PolynomialGrid
