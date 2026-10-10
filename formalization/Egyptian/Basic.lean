module
/-
Copyright (c) 2026 Yuhang Shi.
SPDX-License-Identifier: AGPL-3.0-only
Released under the GNU Affero General Public License, version 3 only.
-/
public import Mathlib

@[expose] public section

/-! Strict, distinct Egyptian denominator prefixes and universal optimality.
There are no assumed existence or optimality conclusions in these definitions. -/

namespace Egyptian

noncomputable def unit (m : ℕ) : ℝ := (m : ℝ)⁻¹

structure Prefix where
  denoms : List ℕ
  positive : ∀ d ∈ denoms, 0 < d
  increasing : denoms.Pairwise (· < ·)

namespace Prefix

@[ext] theorem ext {S T : Prefix} (h : S.denoms = T.denoms) : S = T := by
  cases S
  cases T
  cases h
  rfl

noncomputable def sum (S : Prefix) : ℝ := (S.denoms.map unit).sum
def sumQ (S : Prefix) : ℚ := (S.denoms.map (fun (d : ℕ) => (d : ℚ)⁻¹)).sum
def last (S : Prefix) : ℕ := S.denoms.getLast?.getD 0
def length (S : Prefix) : ℕ := S.denoms.length

def empty : Prefix := ⟨[], by simp, by simp⟩

@[simp] theorem sum_empty : empty.sum = 0 := rfl
@[simp] theorem last_empty : empty.last = 0 := rfl
@[simp] theorem length_empty : empty.length = 0 := rfl

theorem mem_le_last (S : Prefix) {d : ℕ} (hd : d ∈ S.denoms) : d ≤ S.last := by
  have hn : S.denoms ≠ [] := List.ne_nil_of_mem hd
  have hle : S.denoms.Pairwise (· ≤ ·) :=
    S.increasing.imp (fun h => le_of_lt h)
  have h := hle.rel_getLast hd
  simpa [last, List.getLast?_eq_getLast_of_ne_nil hn] using h

def append (S : Prefix) (d : ℕ) (hd : S.last < d) : Prefix where
  denoms := S.denoms ++ [d]
  positive := by
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact S.positive e he
    · have he' : e = d := List.mem_singleton.mp he
      subst e
      exact lt_of_le_of_lt (Nat.zero_le _) hd
  increasing := by
    apply List.pairwise_append.mpr
    refine ⟨S.increasing, by simp, ?_⟩
    intro e he f hf
    have hf' : f = d := List.mem_singleton.mp hf
    subst f
    exact lt_of_le_of_lt (S.mem_le_last he) hd

@[simp] theorem denoms_append (S : Prefix) (d : ℕ) (h : S.last < d) :
    (S.append d h).denoms = S.denoms ++ [d] := rfl

@[simp] theorem sum_append (S : Prefix) (d : ℕ) (h : S.last < d) :
    (S.append d h).sum = S.sum + unit d := by
  simp [sum, append]

@[simp] theorem sumQ_append (S : Prefix) (d : ℕ) (h : S.last < d) :
    (S.append d h).sumQ = S.sumQ + (d : ℚ)⁻¹ := by
  simp [sumQ, append]

@[simp] theorem length_append (S : Prefix) (d : ℕ) (h : S.last < d) :
    (S.append d h).length = S.length + 1 := by
  simp [length, append]

@[simp] theorem last_append (S : Prefix) (d : ℕ) (h : S.last < d) :
    (S.append d h).last = d := by
  simp [last, append]

theorem sum_nonneg (S : Prefix) : 0 ≤ S.sum := by
  apply List.sum_nonneg
  intro z hz
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hz
  exact inv_nonneg.mpr (Nat.cast_nonneg d)

@[simp] theorem cast_sumQ (S : Prefix) : (S.sumQ : ℝ) = S.sum := by
  have aux (l : List ℕ) :
      (((l.map (fun (d : ℕ) => (d : ℚ)⁻¹)).sum : ℚ) : ℝ) = (l.map unit).sum := by
    induction l with
    | nil => simp
    | cons d ds ih =>
      simp only [List.map_cons, List.sum_cons, Rat.cast_add, Rat.cast_inv,
        Rat.cast_natCast, unit, ih]
  exact aux S.denoms

end Prefix

def Allowed (c q : ℝ) (M m : ℕ) : Prop := M < m ∧ q + unit m < c

def IsLeastAllowed (c q : ℝ) (M m : ℕ) : Prop :=
  Allowed c q M m ∧ ∀ d, Allowed c q M d → m ≤ d

def BestUnder (x : ℝ) (S : Prefix) : Prop :=
  S.sum < x ∧ ∀ T : Prefix, T.length = S.length → T.sum < x → T.sum ≤ S.sum

/-- An infinite nested append chain beginning at S, optimal at every order.
The quantifiers range over genuine strictly increasing denominator prefixes. -/
def HasBestExtension (x : ℝ) (S : Prefix) : Prop :=
  ∃ F : ℕ → Prefix, F 0 = S ∧
    (∀ n, ∃ d, ∃ hd : (F n).last < d, F (n + 1) = (F n).append d hd) ∧
    ∀ n, BestUnder x (F n)

theorem least_allowed_unique {c q : ℝ} {M m d : ℕ}
    (hm : IsLeastAllowed c q M m) (hd : IsLeastAllowed c q M d) : m = d :=
  le_antisymm (hm.2 d hd.1) (hd.2 m hm.1)

theorem unit_pos {m : ℕ} (hm : 0 < m) : 0 < unit m := by
  exact inv_pos.mpr (Nat.cast_pos.mpr hm)

theorem unit_strictAnti {m d : ℕ} (hm : 0 < m) (hmd : m < d) : unit d < unit m := by
  exact (inv_lt_inv₀ (Nat.cast_pos.mpr (lt_trans hm hmd)) (Nat.cast_pos.mpr hm)).2 (by exact_mod_cast hmd)

theorem optimal_next_is_least {x : ℝ} (S : Prefix) {d : ℕ}
    (hd : S.last < d) (hbest : BestUnder x (S.append d hd)) :
    IsLeastAllowed x S.sum S.last d := by
  refine ⟨⟨hd, by simpa using hbest.1⟩, ?_⟩
  intro m hm
  by_contra hdm
  have hmd : m < d := Nat.lt_of_not_ge hdm
  have hmp : 0 < m := lt_of_le_of_lt (Nat.zero_le _) hm.1
  have hb := hbest.2 (S.append m hm.1) (by simp) (by simpa using hm.2)
  have hi := unit_strictAnti hmp hmd
  simp only [Prefix.sum_append] at hb
  linarith

end Egyptian
