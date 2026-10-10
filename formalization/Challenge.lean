module

/- Copyright © 2026 Yuhang Shi.
SPDX-License-Identifier: AGPL-3.0-only -/

public import Mathlib

/-!
# A specific non-eventually-greedy Egyptian underapproximation example

This statement imports only Mathlib. All denominators are positive integers,
strict underapproximation is required, and every competing list has distinct
denominators in increasing order. Eventual optimality quantifies over every
infinite increasing sequence and every possible starting order, including zero.

The two definition-value holes are interfaces for the particular real and the
total rational algorithm supplied by Solution. The predicate below has its
ordinary mathematical definition and contains no hole. The construction is the
height/degree/lexicographic polynomial and binary-prefix recursion in
`Egyptian.Main`, not an unspecified existential choice of a counterexample.
-/

@[expose] public section

namespace EgyptianPalomar

/-- The reciprocal sum of a finite denominator list. Positivity and strict
increase are imposed explicitly whenever the list is used as a competitor. -/
noncomputable def unitSum (L : List ℕ) : ℝ :=
  (L.map (fun (d : ℕ) => (d : ℝ)⁻¹)).sum

/-- Eventual optimality in the original distinct-denominator sense: some
positive strictly increasing sequence realizes a best strict underapproximation
at every order from some `n₀` onward. Every positive increasing competitor of
that order is considered; ties for the best value are permitted. -/
def eventuallyOptimal (x : ℝ) : Prop :=
  ∃ m : ℕ → ℕ, (∀ k, 0 < m k) ∧ StrictMono m ∧
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      unitSum (List.ofFn (fun k : Fin n => m k)) < x ∧
      ∀ L : List ℕ, (∀ d ∈ L, 0 < d) → L.Pairwise (· < ·) →
        L.length = n → unitSum L < x →
        unitSum L ≤ unitSum (List.ofFn (fun k : Fin n => m k))

/-- The unique real in the nested closed rational intervals starting from
`[1/4, 1/3]`, with binary-prefix enumeration and nonzero integer polynomials
ordered by height, degree, and coefficient lexicographic order. Each stage uses
the prescribed least successful indices and four-term radius. Solution supplies
exactly `Egyptian.explicitReal`, defined by that complete terminating recursion.
The compared theorem proves its range, transcendence, universal failure of
eventual optimality, and relation to the supplied rational algorithm. -/
noncomputable def explicitReal : ℝ := sorry

/-- At precision index `n`, the midpoint of the stage-`n` rational interval in
the same fully specified recursion. Solution supplies exactly the total
executable function `Egyptian.approximation`. The all-`n` error bound determines
the real uniquely from these outputs. A separate Turing-machine or `Partrec`
encoding and a complexity estimate are not claimed. -/
def approximation : ℕ → ℚ := sorry

/-- The complete constructive example: a particular transcendental real in
`(1/4,1/3)` which admits no eventually optimal increasing denominator sequence,
together with its total rational approximation and error bound for every
precision index, including `n = 0`. This is a concrete-example result, not a
claim to prove the previously established measure-zero theorem. -/
theorem explicit_counterexample :
    (1 / 4 : ℝ) < explicitReal ∧ explicitReal < (1 / 3 : ℝ) ∧
    Transcendental ℤ explicitReal ∧ ¬ eventuallyOptimal explicitReal ∧
    ∀ n : ℕ, |explicitReal - (approximation n : ℝ)| ≤ (1 / 2 : ℝ)^n / 2 := by
  sorry

end EgyptianPalomar
