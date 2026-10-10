module

/- Copyright © 2026 Yuhang Shi.
SPDX-License-Identifier: AGPL-3.0-only -/

public import Egyptian.Main

/-! The concrete implementation of the independent Palomar statement.
The mathematical predicate is repeated verbatim; the two value interfaces are
filled with the actual manuscript construction. -/

@[expose] public section

namespace EgyptianPalomar

noncomputable def unitSum (L : List ℕ) : ℝ :=
  (L.map (fun (d : ℕ) => (d : ℝ)⁻¹)).sum

def eventuallyOptimal (x : ℝ) : Prop :=
  ∃ m : ℕ → ℕ, (∀ k, 0 < m k) ∧ StrictMono m ∧
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      unitSum (List.ofFn (fun k : Fin n => m k)) < x ∧
      ∀ L : List ℕ, (∀ d ∈ L, 0 < d) → L.Pairwise (· < ·) →
        L.length = n → unitSum L < x →
        unitSum L ≤ unitSum (List.ofFn (fun k : Fin n => m k))

noncomputable def explicitReal : ℝ := Egyptian.explicitReal

def approximation : ℕ → ℚ := Egyptian.approximation

private theorem unitSum_eq_prefix_sum (S : Egyptian.Prefix) :
    unitSum S.denoms = S.sum := by
  rfl

private theorem not_eventuallyOptimal_of_not_eventuallyGreedy {x : ℝ}
    (hx : ¬ Egyptian.EventuallyGreedy x) : ¬ eventuallyOptimal x := by
  rintro ⟨m, hp, hm, n₀, h⟩
  apply hx
  let C : Egyptian.DenominatorChain := ⟨m, hp, hm⟩
  refine ⟨C, n₀, ?_⟩
  intro n hn
  obtain ⟨hfeas, hbest⟩ := h n hn
  constructor
  · rw [← unitSum_eq_prefix_sum]
    exact hfeas
  · intro T hlen hT
    have hlength : T.denoms.length = n := by
      exact hlen.trans (C.prefix_length n)
    have hsum : unitSum T.denoms < x := by
      rw [unitSum_eq_prefix_sum]
      exact hT
    have ht := hbest T.denoms T.positive T.increasing hlength hsum
    change unitSum T.denoms ≤ unitSum (C.prefix n).denoms at ht
    rwa [unitSum_eq_prefix_sum, unitSum_eq_prefix_sum] at ht

theorem explicit_counterexample :
    (1 / 4 : ℝ) < explicitReal ∧ explicitReal < (1 / 3 : ℝ) ∧
    Transcendental ℤ explicitReal ∧ ¬ eventuallyOptimal explicitReal ∧
    ∀ n : ℕ, |explicitReal - (approximation n : ℝ)| ≤ (1 / 2 : ℝ)^n / 2 := by
  refine ⟨Egyptian.explicitReal_in_range.1, Egyptian.explicitReal_in_range.2,
    Egyptian.explicitReal_transcendental, ?_, ?_⟩
  · exact not_eventuallyOptimal_of_not_eventuallyGreedy
      Egyptian.explicitReal_not_eventuallyGreedy
  · intro n
    exact Egyptian.approximation_certified n

end EgyptianPalomar
