module
/-
Copyright (c) 2026 Yuhang Shi.
SPDX-License-Identifier: AGPL-3.0-only
Released under the GNU Affero General Public License, version 3 only.
-/
public import Egyptian.Basic
public import Mathlib.Data.Nat.BitIndices

@[expose] public section

namespace Egyptian

/-- Zero-based indexing: this is S_(j+1) in the manuscript. -/
def prefixAt (j : ℕ) : Prefix where
  denoms := j.bitIndices.map Nat.succ
  positive := by
    intro d hd
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
    exact Nat.succ_pos e
  increasing := by
    apply List.pairwise_map.mpr
    exact Nat.bitIndices_sorted.pairwise.imp (fun h => Nat.succ_lt_succ h)

def prefixCode (S : Prefix) : ℕ :=
  ((S.denoms.map Nat.pred).map (fun i => 2 ^ i)).sum

theorem prefixAt_prefixCode (S : Prefix) : prefixAt (prefixCode S) = S := by
  have hsort : (S.denoms.map Nat.pred).SortedLT := by
    apply List.sortedLT_iff_pairwise.mpr
    apply List.pairwise_map.mpr
    apply S.increasing.imp_of_mem
    intro a b ha hb hab
    have hapos := S.positive a ha
    have hbpos := S.positive b hb
    rw [Nat.pred_eq_sub_one, Nat.pred_eq_sub_one]
    omega
  have hbits := Nat.bitIndices_sum_map_two_pow hsort
  have hden : (prefixAt (prefixCode S)).denoms = S.denoms := by
    dsimp [prefixAt, prefixCode]
    rw [hbits, List.map_map]
    conv_rhs => rw [← List.map_id S.denoms]
    apply List.map_congr_left
    intro a ha
    exact Nat.succ_pred_eq_of_pos (S.positive a ha)
  exact Prefix.ext hden

theorem prefixAt_surjective : Function.Surjective prefixAt :=
  fun S => ⟨prefixCode S, prefixAt_prefixCode S⟩

end Egyptian
