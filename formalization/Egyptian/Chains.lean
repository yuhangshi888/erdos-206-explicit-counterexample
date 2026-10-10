module
/-
Copyright (c) 2026 Yuhang Shi.
SPDX-License-Identifier: AGPL-3.0-only
Released under the GNU Affero General Public License, version 3 only.
-/
public import Egyptian.Basic

@[expose] public section

/-! The precise infinite-chain formulation of eventual optimality, and its
bridge to finite strictly increasing prefixes with infinite optimal extensions. -/

namespace Egyptian

structure DenominatorChain where
  denoms : ℕ → ℕ
  positive : ∀ n, 0 < denoms n
  increasing : StrictMono denoms

namespace DenominatorChain

def «prefix» (C : DenominatorChain) (n : ℕ) : Prefix where
  denoms := List.ofFn (fun i : Fin n => C.denoms i)
  positive := by
    intro d hd
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hd
    exact C.positive i
  increasing := by
    apply List.pairwise_ofFn.2
    intro i j hij
    exact C.increasing hij

@[simp] theorem prefix_denoms (C : DenominatorChain) (n : ℕ) :
    (C.prefix n).denoms = List.ofFn (fun i : Fin n => C.denoms i) := rfl

@[simp] theorem prefix_length (C : DenominatorChain) (n : ℕ) :
    (C.prefix n).length = n := by simp [Prefix.length, «prefix»]

@[simp] theorem prefix_zero (C : DenominatorChain) : C.prefix 0 = Prefix.empty := by
  apply Prefix.ext
  simp [«prefix», Prefix.empty]

theorem prefix_denoms_succ (C : DenominatorChain) (n : ℕ) :
    (C.prefix (n + 1)).denoms = (C.prefix n).denoms ++ [C.denoms n] := by
  simp only [prefix_denoms]
  rw [List.ofFn_succ']
  simp [List.concat_eq_append]

@[simp] theorem prefix_last_succ (C : DenominatorChain) (n : ℕ) :
    (C.prefix (n + 1)).last = C.denoms n := by
  change (C.prefix (n + 1)).denoms.getLast?.getD 0 = C.denoms n
  rw [C.prefix_denoms_succ]
  simp

theorem prefix_last_lt (C : DenominatorChain) (n : ℕ) :
    (C.prefix n).last < C.denoms n := by
  cases n with
  | zero => simpa using C.positive 0
  | succ n => simpa using C.increasing (Nat.lt_succ_self n)

theorem prefix_succ (C : DenominatorChain) (n : ℕ) :
    C.prefix (n + 1) = (C.prefix n).append (C.denoms n) (C.prefix_last_lt n) := by
  apply Prefix.ext
  exact C.prefix_denoms_succ n

end DenominatorChain

/-- This is exactly eventual optimality of a positive strictly increasing
infinite denominator sequence, including every prefix order from n₀ onward. -/
def EventuallyGreedy (x : ℝ) : Prop :=
  ∃ C : DenominatorChain, ∃ n₀ : ℕ,
    ∀ n, n₀ ≤ n → BestUnder x (C.prefix n)

theorem eventuallyGreedy_iff_sequences (x : ℝ) : EventuallyGreedy x ↔
    ∃ (m : ℕ → ℕ) (hp : ∀ n, 0 < m n) (hm : StrictMono m) (n₀ : ℕ),
      ∀ n, n₀ ≤ n → BestUnder x ((DenominatorChain.mk m hp hm).prefix n) := by
  constructor
  · rintro ⟨⟨m, hp, hm⟩, n₀, h⟩
    exact ⟨m, hp, hm, n₀, h⟩
  · rintro ⟨m, hp, hm, n₀, h⟩
    exact ⟨⟨m, hp, hm⟩, n₀, h⟩

/-- Shifting the actual infinite denominator chain at n₀ gives an optimal
append chain starting at its finite n₀-prefix. -/
theorem chain_hasBestExtension {x : ℝ} (C : DenominatorChain) (n₀ : ℕ)
    (h : ∀ n, n₀ ≤ n → BestUnder x (C.prefix n)) :
    HasBestExtension x (C.prefix n₀) := by
  refine ⟨fun n => C.prefix (n₀ + n), by simp, ?_, ?_⟩
  · intro n
    refine ⟨C.denoms (n₀ + n), C.prefix_last_lt (n₀ + n), ?_⟩
    simpa only [Nat.add_assoc] using C.prefix_succ (n₀ + n)
  · intro n
    exact h (n₀ + n) (by omega)

theorem not_eventuallyGreedy_of_no_best_extension {x : ℝ}
    (h : ∀ S : Prefix, ¬ HasBestExtension x S) : ¬ EventuallyGreedy x := by
  rintro ⟨C, n₀, hbest⟩
  exact h (C.prefix n₀) (chain_hasBestExtension C n₀ hbest)

end Egyptian
