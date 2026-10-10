module
/-
Copyright (c) 2026 Yuhang Shi.
SPDX-License-Identifier: AGPL-3.0-only
Released under the GNU Affero General Public License, version 3 only.
-/
public import Egyptian.Construction
public import Egyptian.PolynomialEnumeration
public import Egyptian.MaxExists

@[expose] public section

/-! No enumeration, local-defeat, or termination hypotheses remain in the
following construction theorem. It uses the manuscript's actual streams. -/

namespace Egyptian

open Construction PolynomialEnumeration

/-- The specific real determined by the original height/degree/lex construction. -/
noncomputable def explicitReal : ℝ := limit polyAtQ polyAtQ_nonzero

/-- Its rational approximation at requested precision index n. -/
def approximation (n : ℕ) : ℚ := midpoint polyAtQ polyAtQ_nonzero n

/-- The closed rational interval output at stage n. -/
def explicitInterval (n : ℕ) : ℚ × ℚ := intervals polyAtQ polyAtQ_nonzero n

theorem explicitReal_in_range : (1/4 : ℝ) < explicitReal ∧ explicitReal < (1/3 : ℝ) :=
  limit_range polyAtQ polyAtQ_nonzero

theorem explicitReal_transcendental : Transcendental ℤ explicitReal :=
  limit_transcendental polyAtQ polyAtQ_nonzero polyAtQ_complete

theorem explicitReal_not_eventuallyGreedy : ¬ EventuallyGreedy explicitReal :=
  limit_not_eventuallyGreedy polyAtQ polyAtQ_nonzero

/-- The same negative conclusion in the original maximum-value notation;
every n₀ and every strictly increasing infinite denominator sequence is covered. -/
theorem explicitReal_no_eventually_optimal_sequence :
    ¬ ∃ C : DenominatorChain, ∃ n₀ : ℕ,
      ∀ n, n₀ ≤ n → (C.prefix n).sum = Rn explicitReal n := by
  rintro ⟨C, n₀, h⟩
  apply explicitReal_not_eventuallyGreedy
  refine ⟨C, n₀, ?_⟩
  intro n hn
  have hx : 0 < explicitReal := lt_trans (by norm_num) explicitReal_in_range.1
  obtain ⟨S, hlen, hS, heq⟩ := Rn_attained hx n
  have hfeas : (C.prefix n).sum < explicitReal := by
    rw [h n hn, ← heq]
    exact hS
  apply (bestUnder_iff_sum_eq_Rn hx (C.prefix n)).mpr
  exact ⟨hfeas, by simpa using h n hn⟩

theorem approximation_certified (n : ℕ) :
    |explicitReal - (approximation n : ℝ)| ≤ (1/2 : ℝ)^n / 2 :=
  midpoint_error_bound polyAtQ polyAtQ_nonzero n

/-- Full unconditional theorem, including a total executable rational
approximation with an explicit geometric error bound. -/
theorem explicit_counterexample :
    (1/4 : ℝ) < explicitReal ∧ explicitReal < (1/3 : ℝ) ∧
    Transcendental ℤ explicitReal ∧ ¬ EventuallyGreedy explicitReal ∧
    ∀ n : ℕ, |explicitReal - (approximation n : ℝ)| ≤ (1/2 : ℝ)^n / 2 :=
  ⟨explicitReal_in_range.1, explicitReal_in_range.2,
    explicitReal_transcendental, explicitReal_not_eventuallyGreedy, approximation_certified⟩

end Egyptian
