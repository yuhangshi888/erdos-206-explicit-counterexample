module
/-
Copyright (c) 2026 Yuhang Shi.
SPDX-License-Identifier: AGPL-3.0-only
Released under the GNU Affero General Public License, version 3 only.
-/
public import Egyptian.Greedy

@[expose] public section

/-! Actual attainment of each fixed-order optimal Egyptian sum. Dickson's
lemma gives finitely many coordinatewise-minimal feasible denominator tuples. -/

namespace Egyptian

private theorem exists_max_antitoneOn {α : Type*} [PartialOrder α] [WellQuasiOrderedLE α]
    (s : Set α) (hne : s.Nonempty) (f : α → ℝ) (hf : AntitoneOn f s) :
    ∃ a ∈ s, ∀ b ∈ s, f b ≤ f a := by
  let minima : Set α := {a | Minimal (· ∈ s) a}
  have hs : s.IsPWO := Set.isPWO_of_wellQuasiOrderedLE s
  have hfinite : minima.Finite :=
    WellQuasiOrderedLE.finite_of_isAntichain (setOfPred_minimal_antichain (· ∈ s))
  obtain ⟨a₀, ha₀⟩ := hs.exists_minimal hne
  obtain ⟨a, ha, hmax⟩ := Set.exists_max_image minima f hfinite ⟨a₀, ha₀⟩
  refine ⟨a, ha.1, ?_⟩
  intro b hb
  obtain ⟨d, hdb, hd⟩ := hs.exists_le_minimal hb
  exact le_trans (hf hd.1 hb hdb) (hmax d hd)

private noncomputable def tupleSum {n : ℕ} (d : Fin n → ℕ) : ℝ :=
  ((List.ofFn d).map unit).sum

private def tupleFeasible (x : ℝ) (n : ℕ) : Set (Fin n → ℕ) :=
  {d | (∀ i, 0 < d i) ∧ (List.ofFn d).Pairwise (· < ·) ∧ tupleSum d < x}

private theorem tupleSum_antitone {x : ℝ} {n : ℕ} :
    AntitoneOn tupleSum (tupleFeasible x n) := by
  intro a ha b hb hab
  simp only [tupleSum, List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_le_sum
  intro i _
  exact (inv_le_inv₀ (Nat.cast_pos.mpr (hb.1 i)) (Nat.cast_pos.mpr (ha.1 i))).2
    (by exact_mod_cast (hab i))

private def prefixTuple (S : Prefix) {n : ℕ} (h : S.length = n) : Fin n → ℕ :=
  fun i => S.denoms.get (Fin.cast h.symm i)

private theorem ofFn_prefixTuple (S : Prefix) {n : ℕ} (h : S.length = n) :
    List.ofFn (prefixTuple S h) = S.denoms := by
  exact (List.ofFn_congr h S.denoms.get).symm.trans (List.ofFn_get S.denoms)

private theorem prefixTuple_feasible {x : ℝ} (S : Prefix) (hx : S.sum < x)
    {n : ℕ} (h : S.length = n) : prefixTuple S h ∈ tupleFeasible x n := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply S.positive
    have hm : prefixTuple S h i ∈ List.ofFn (prefixTuple S h) :=
      List.mem_ofFn.mpr ⟨i, rfl⟩
    rwa [ofFn_prefixTuple S h] at hm
  · rw [ofFn_prefixTuple S h]
    exact S.increasing
  · simpa only [tupleSum, ofFn_prefixTuple S h, Prefix.sum] using hx

/-- Every nonempty feasible family of a fixed length has a maximizer.
The witness S is merely a feasible tuple, with no optimality premise. -/
theorem exists_bestUnder_of_feasible {x : ℝ} (S : Prefix) (hx : S.sum < x) :
    ∃ P : Prefix, P.length = S.length ∧ BestUnder x P := by
  let n := S.length
  have hne : (tupleFeasible x n).Nonempty :=
    ⟨prefixTuple S rfl, prefixTuple_feasible S hx rfl⟩
  obtain ⟨d, hd, hmax⟩ := exists_max_antitoneOn (tupleFeasible x n) hne
    tupleSum tupleSum_antitone
  let P : Prefix := ⟨List.ofFn d, by
      intro a ha
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
      exact hd.1 i, hd.2.1⟩
  have hP : P.length = n := by simp [P, Prefix.length]
  refine ⟨P, hP, hd.2.2, ?_⟩
  intro T hT hxT
  have hTn : T.length = n := hT.trans hP
  have ht := prefixTuple_feasible T hxT hTn
  have hm := hmax (prefixTuple T hTn) ht
  simpa only [tupleSum, ofFn_prefixTuple T hTn, Prefix.sum] using hm

/-- For every positive real target and every finite order, the maximum below
the target is attained by a strictly increasing positive denominator prefix. -/
theorem exists_bestUnder {x : ℝ} (hx : 0 < x) (n : ℕ) :
    ∃ P : Prefix, P.length = n ∧ BestUnder x P := by
  obtain ⟨c, hc0, hcx⟩ := exists_rat_btwn hx
  have hcq : (0 : ℚ) < c := by
    exact_mod_cast hc0
  have hstart : Prefix.empty.sumQ < c := by simpa [Prefix.sumQ, Prefix.empty] using hcq
  let S := greedyIterQ c Prefix.empty n
  have hs : S.sum < (c : ℝ) := by
    have hr : (S.sumQ : ℝ) < (c : ℝ) := Rat.cast_lt.mpr (greedyIterQ_below Prefix.empty hstart n)
    simpa using hr
  obtain ⟨P, hp, hbest⟩ := exists_bestUnder_of_feasible S (lt_trans hs hcx)
  refine ⟨P, ?_, hbest⟩
  simpa [S] using hp

/-- The original fixed-order maximum, expressed by the supremum of the actual
feasible reciprocal sums. The following theorems prove this supremum is attained. -/
noncomputable def Rn (x : ℝ) (n : ℕ) : ℝ :=
  sSup {y : ℝ | ∃ S : Prefix, S.length = n ∧ S.sum < x ∧ S.sum = y}

theorem Rn_eq_of_bestUnder {x : ℝ} (S : Prefix) (hb : BestUnder x S) :
    Rn x S.length = S.sum := by
  apply IsGreatest.csSup_eq
  refine ⟨⟨S, rfl, hb.1, rfl⟩, ?_⟩
  rintro y ⟨T, hT, hxT, hy⟩
  rw [← hy]
  exact hb.2 T hT hxT

theorem bestUnder_iff_sum_eq_Rn {x : ℝ} (hx : 0 < x) (S : Prefix) :
    BestUnder x S ↔ S.sum < x ∧ S.sum = Rn x S.length := by
  constructor
  · intro hb
    exact ⟨hb.1, (Rn_eq_of_bestUnder S hb).symm⟩
  · rintro ⟨hS, heq⟩
    obtain ⟨P, hlen, hbest⟩ := exists_bestUnder hx S.length
    have hR : Rn x S.length = P.sum := by
      simpa only [hlen] using Rn_eq_of_bestUnder P hbest
    refine ⟨hS, ?_⟩
    intro T hT hxT
    have hbound := hbest.2 T (hT.trans hlen.symm) hxT
    linarith

theorem Rn_attained {x : ℝ} (hx : 0 < x) (n : ℕ) :
    ∃ S : Prefix, S.length = n ∧ S.sum < x ∧ S.sum = Rn x n := by
  obtain ⟨S, hlen, hb⟩ := exists_bestUnder hx n
  refine ⟨S, hlen, hb.1, ?_⟩
  simpa only [hlen] using (Rn_eq_of_bestUnder S hb).symm

end Egyptian
