module
/-
Copyright (c) 2026 Yuhang Shi.
SPDX-License-Identifier: AGPL-3.0-only
Released under the GNU Affero General Public License, version 3 only.
-/
public import Mathlib

@[expose] public section

/-!
The exact two-term interval used in the constructive counterexample.
All denominators are natural numbers; the endpoints are real numbers.
-/

namespace Egyptian.BadPair

def A (i : ℕ) : ℕ := i * (i + 1)
def D (i : ℕ) : ℕ := A i + 4
def V (i : ℕ) : ℕ := A i / 2 + 1

def rRat (i : ℕ) : ℚ := 1 / ((i + 1 : ℕ) : ℚ) + 1 / (V i : ℚ)
def uRat (i : ℕ) : ℚ := 1 / (i : ℚ) + 1 / (D i : ℚ)

noncomputable def r (i : ℕ) : ℝ := 1 / ((i + 1 : ℕ) : ℝ) + 1 / (V i : ℝ)
noncomputable def u (i : ℕ) : ℝ := 1 / (i : ℝ) + 1 / (D i : ℝ)

@[simp] theorem cast_rRat (i : ℕ) : (rRat i : ℝ) = r i := by
  simp [rRat, r]

@[simp] theorem cast_uRat (i : ℕ) : (uRat i : ℝ) = u i := by
  simp [uRat, u]

@[simp] theorem cast_A (i : ℕ) : (A i : ℝ) = (i : ℝ) * ((i : ℝ) + 1) := by
  simp [A]

@[simp] theorem cast_D (i : ℕ) : (D i : ℝ) = (i : ℝ) * ((i : ℝ) + 1) + 4 := by
  simp [D]

@[simp] theorem cast_V (i : ℕ) :
    (V i : ℝ) = (i : ℝ) * ((i : ℝ) + 1) / 2 + 1 := by
  simp only [V, Nat.cast_add, Nat.cast_one]
  simp only [A]
  rw [Nat.cast_div (Nat.two_dvd_mul_add_one i) (by norm_num : (2 : ℝ) ≠ 0)]
  simp

private theorem real_pair_bounds (t : ℝ) (ht : 3 ≤ t) :
    1 / t + 1 / (t * (t + 1) + 5) <
        1 / (t + 1) + 1 / (t * (t + 1) / 2 + 1) ∧
    1 / (t + 1) + 1 / (t * (t + 1) / 2 + 1) <
        1 / t + 1 / (t * (t + 1) + 4) ∧
    1 / t + 1 / (t * (t + 1) + 4) < 1 / (t - 1) := by
  let a := t * (t + 1)
  have ht0 : 0 < t := by linarith
  have ht1 : 0 < t + 1 := by linarith
  have htm1 : 0 < t - 1 := by linarith
  have ha12 : 12 ≤ a := by
    dsimp [a]
    nlinarith [sq_nonneg (t - 3)]
  have ha0 : 0 < a := by linarith
  have ha2 : 0 < a + 2 := by linarith
  have ha4 : 0 < a + 4 := by linarith
  have ha5 : 0 < a + 5 := by linarith
  have hap : 0 < a * (a + 2) := mul_pos ha0 ha2
  have hv : 0 < a / 2 + 1 := by linarith
  have hidentity :
      1 / (t + 1) + 1 / (a / 2 + 1) =
        1 / t + (a - 2) / (a * (a + 2)) := by
    dsimp [a]
    field_simp
    nlinarith
  have hlo : 1 / (a + 5) < (a - 2) / (a * (a + 2)) := by
    apply (div_lt_div_iff₀ ha5 hap).2
    nlinarith
  have hmid : (a - 2) / (a * (a + 2)) < 1 / (a + 4) := by
    apply (div_lt_div_iff₀ hap ha4).2
    nlinarith
  have hprev : 1 / (a + 4) < 1 / (t * (t - 1)) := by
    apply one_div_lt_one_div_of_lt (mul_pos ht0 htm1)
    dsimp [a]
    nlinarith
  have hgap : 1 / (t - 1) - 1 / t = 1 / (t * (t - 1)) := by
    field_simp
    nlinarith
  change 1 / t + 1 / (a + 5) < _ ∧ _ < 1 / t + 1 / (a + 4) ∧ _
  rw [hidentity]
  exact ⟨by linarith, by linarith, by linarith⟩

theorem bounds_real (i : ℕ) (hi : 3 ≤ i) :
    1 / (i : ℝ) + 1 / ((D i + 1 : ℕ) : ℝ) < r i ∧
    r i < u i ∧
    u i < 1 / ((i : ℝ) - 1) := by
  have ht : (3 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  simpa [r, u, add_assoc, show (4 : ℝ) + 1 = 5 by norm_num] using
    real_pair_bounds (i : ℝ) ht

theorem bounds (i : ℕ) (hi : 3 ≤ i) :
    1 / (i : ℝ) + 1 / ((D i + 1 : ℕ) : ℝ) < r i ∧
    r i < u i ∧
    u i < 1 / ((i - 1 : ℕ) : ℝ) := by
  have hs : ((i - 1 : ℕ) : ℝ) = (i : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ i)]
    norm_num
  simpa [hs] using bounds_real i hi

theorem bounds_rat (i : ℕ) (hi : 3 ≤ i) :
    1 / (i : ℚ) + 1 / ((D i + 1 : ℕ) : ℚ) < rRat i ∧
    rRat i < uRat i ∧
    uRat i < 1 / ((i - 1 : ℕ) : ℚ) := by
  have h := bounds i hi
  refine ⟨?_, ?_, ?_⟩
  · apply (Rat.cast_lt (K := ℝ)).mp
    simpa using h.1
  · apply (Rat.cast_lt (K := ℝ)).mp
    simpa using h.2.1
  · apply (Rat.cast_lt (K := ℝ)).mp
    simpa using h.2.2

theorem r_pos (i : ℕ) (hi : 3 ≤ i) : 0 < r i := by
  have hip : 0 < (i : ℝ) := by exact_mod_cast (by omega : 0 < i)
  have hd : 0 < ((D i + 1 : ℕ) : ℝ) := by positivity
  have hp : 0 < 1 / (i : ℝ) + 1 / ((D i + 1 : ℕ) : ℝ) := by positivity
  exact lt_trans hp (bounds i hi).1

theorem interval_nonempty (i : ℕ) (hi : 3 ≤ i) : r i < u i :=
  (bounds i hi).2.1

theorem denominator_orders (i : ℕ) (hi : 3 ≤ i) :
    i + 1 < V i ∧ V i < D i + 1 ∧ i < D i + 1 := by
  have ht : (3 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  have hv : (((i + 1 : ℕ) : ℝ)) < (V i : ℝ) := by
    simp only [Nat.cast_add, Nat.cast_one, cast_V]
    nlinarith [sq_nonneg ((i : ℝ) - 3)]
  have hD : (V i : ℝ) < ((D i + 1 : ℕ) : ℝ) := by
    simp only [Nat.cast_add, Nat.cast_one, cast_V, cast_D]
    nlinarith [sq_nonneg ((i : ℝ) - 3)]
  have hVnat : i + 1 < V i := by exact_mod_cast hv
  have hDnat : V i < D i + 1 := by exact_mod_cast hD
  exact ⟨hVnat, hDnat, by omega⟩

theorem u_lt_two_div (i : ℕ) (hi : 3 ≤ i) : u i < 2 / (i : ℝ) := by
  have ht : (3 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  have ht0 : 0 < (i : ℝ) := by linarith
  have hlarge : (i : ℝ) < (D i : ℝ) := by
    rw [cast_D]
    nlinarith [sq_nonneg (i : ℝ)]
  have hrec : 1 / (D i : ℝ) < 1 / (i : ℝ) :=
    one_div_lt_one_div_of_lt ht0 hlarge
  unfold u
  calc
    1 / (i : ℝ) + 1 / (D i : ℝ) < 1 / (i : ℝ) + 1 / (i : ℝ) := by linarith
    _ = 2 / (i : ℝ) := by ring

theorem exists_large_index (M : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ i : ℕ, 3 ≤ i ∧ M < i ∧ u i < ε := by
  obtain ⟨i, hi⟩ := exists_nat_gt (max ((M : ℝ) + 3) (2 / ε))
  have hm : (M : ℝ) + 3 < (i : ℝ) :=
    lt_of_le_of_lt (le_max_left _ _) hi
  have hmn : M + 3 < i := by exact_mod_cast hm
  have hi3 : 3 ≤ i := by omega
  have hi0 : 0 < (i : ℝ) := by exact_mod_cast (by omega : 0 < i)
  have he : 2 / ε < (i : ℝ) :=
    lt_of_le_of_lt (le_max_right _ _) hi
  have he' : 2 < ε * (i : ℝ) := by
    have := (div_lt_iff₀ hε).1 he
    nlinarith
  have hd : 2 / (i : ℝ) < ε := (div_lt_iff₀ hi0).2 he'
  exact ⟨i, hi3, by omega, lt_trans (u_lt_two_div i hi3) hd⟩

theorem exists_large_rat_index (M : ℕ) (ε : ℚ) (hε : 0 < ε) :
    ∃ i : ℕ, 3 ≤ i ∧ M < i ∧ uRat i < ε := by
  have hεr : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  obtain ⟨i, hi, hM, hu⟩ := exists_large_index M (ε : ℝ) hεr
  rw [← cast_uRat] at hu
  have huq : uRat i < ε := by exact_mod_cast hu
  exact ⟨i, hi, hM, huq⟩

theorem greedy_cell (i : ℕ) (hi : 3 ≤ i) (x : ℝ)
    (hr : r i < x) (hu : x < u i) :
    1 / (i : ℝ) < x ∧ x < 1 / ((i - 1 : ℕ) : ℝ) ∧
    1 / ((D i + 1 : ℕ) : ℝ) < x - 1 / (i : ℝ) ∧
    x - 1 / (i : ℝ) < 1 / (D i : ℝ) := by
  have h := bounds i hi
  have hd : 0 < 1 / ((D i + 1 : ℕ) : ℝ) := by positivity
  have hu' : x < 1 / (i : ℝ) + 1 / (D i : ℝ) := hu
  exact ⟨by linarith [h.1], lt_trans hu h.2.2,
    by linarith [h.1], by linarith⟩

end Egyptian.BadPair
