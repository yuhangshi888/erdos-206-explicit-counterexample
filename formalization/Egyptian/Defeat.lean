module
/-
Copyright (c) 2026 Yuhang Shi.
SPDX-License-Identifier: AGPL-3.0-only
Released under the GNU Affero General Public License, version 3 only.
-/
public import Egyptian.Basic
public import Egyptian.BadPair

@[expose] public section

/-! A two-term local obstruction to a chain of optimal Egyptian prefixes. -/

namespace Egyptian

private theorem unit_antitone {m d : ℕ} (hm : 0 < m) (hmd : m ≤ d) :
    unit d ≤ unit m := by
  have hmr : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hmdr : (m : ℝ) ≤ (d : ℝ) := by exact_mod_cast hmd
  simpa [unit, one_div] using one_div_le_one_div_of_le hmr hmdr

theorem least_first_bad_pair (S : Prefix) (i : ℕ) (hi : 3 ≤ i)
    (hSi : S.last < i) (x : ℝ)
    (hr : BadPair.r i < x - S.sum) (hu : x - S.sum < BadPair.u i) :
    IsLeastAllowed x S.sum S.last i := by
  have hc := BadPair.greedy_cell i hi (x - S.sum) hr hu
  have hlo : unit i < x - S.sum := by
    simpa [unit, one_div] using hc.1
  have hhigh : x - S.sum < unit (i - 1) := by
    simpa [unit, one_div] using hc.2.1
  refine ⟨⟨hSi, by linarith⟩, ?_⟩
  intro m hm
  by_contra h
  have hmi : m < i := Nat.lt_of_not_ge h
  have hm0 : 0 < m := lt_of_le_of_lt (Nat.zero_le _) hm.1
  have hmp : m ≤ i - 1 := by omega
  have hrec := unit_antitone hm0 hmp
  have hallow := hm.2
  linarith

theorem least_second_bad_pair (S : Prefix) (i : ℕ) (hi : 3 ≤ i)
    (hSi : S.last < i) (x : ℝ)
    (hr : BadPair.r i < x - S.sum) (hu : x - S.sum < BadPair.u i) :
    IsLeastAllowed x (S.append i hSi).sum (S.append i hSi).last
      (BadPair.D i + 1) := by
  have hc := BadPair.greedy_cell i hi (x - S.sum) hr hu
  have hlo : unit (BadPair.D i + 1) < x - S.sum - unit i := by
    simpa [unit, one_div] using hc.2.2.1
  have hhigh : x - S.sum - unit i < unit (BadPair.D i) := by
    simpa [unit, one_div] using hc.2.2.2
  simp only [Prefix.sum_append, Prefix.last_append]
  refine ⟨⟨(BadPair.denominator_orders i hi).2.2, by linarith⟩, ?_⟩
  intro m hm
  by_contra h
  have hmi : m < BadPair.D i + 1 := Nat.lt_of_not_ge h
  have hm0 : 0 < m := lt_of_le_of_lt (Nat.zero_le _) hm.1
  have hmp : m ≤ BadPair.D i := by omega
  have hrec := unit_antitone hm0 hmp
  have hallow := hm.2
  linarith

def greedyPair (S : Prefix) (i : ℕ) (hi : 3 ≤ i) (hSi : S.last < i) : Prefix :=
  (S.append i hSi).append (BadPair.D i + 1)
    (by simpa using (BadPair.denominator_orders i hi).2.2)

def competingPair (S : Prefix) (i : ℕ) (hi : 3 ≤ i) (hSi : S.last < i) : Prefix :=
  (S.append (i + 1) (by omega)).append (BadPair.V i)
    (by simpa using (BadPair.denominator_orders i hi).1)

@[simp] theorem greedyPair_sum (S : Prefix) (i : ℕ) (hi : 3 ≤ i)
    (hSi : S.last < i) :
    (greedyPair S i hi hSi).sum = S.sum + unit i + unit (BadPair.D i + 1) := by
  simp [greedyPair]

@[simp] theorem competingPair_sum (S : Prefix) (i : ℕ) (hi : 3 ≤ i)
    (hSi : S.last < i) :
    (competingPair S i hi hSi).sum = S.sum + BadPair.r i := by
  simp [competingPair, BadPair.r, unit, one_div, add_assoc]

@[simp] theorem greedyPair_length (S : Prefix) (i : ℕ) (hi : 3 ≤ i)
    (hSi : S.last < i) : (greedyPair S i hi hSi).length = S.length + 2 := by
  simp [greedyPair]

@[simp] theorem competingPair_length (S : Prefix) (i : ℕ) (hi : 3 ≤ i)
    (hSi : S.last < i) : (competingPair S i hi hSi).length = S.length + 2 := by
  simp [competingPair]

theorem bad_pair_not_best (S : Prefix) (i : ℕ) (hi : 3 ≤ i)
    (hSi : S.last < i) (x : ℝ)
    (hr : BadPair.r i < x - S.sum) :
    ¬ BestUnder x (greedyPair S i hi hSi) := by
  intro hb
  have ht : (competingPair S i hi hSi).sum < x := by
    rw [competingPair_sum]
    linarith
  have hlen : (competingPair S i hi hSi).length =
      (greedyPair S i hi hSi).length := by simp
  have hmax := hb.2 (competingPair S i hi hSi) hlen ht
  have hsmall : (greedyPair S i hi hSi).sum < (competingPair S i hi hSi).sum := by
    rw [greedyPair_sum, competingPair_sum]
    have hlo : unit i + unit (BadPair.D i + 1) < BadPair.r i := by
      simpa only [unit, one_div] using (BadPair.bounds i hi).1
    linarith
  linarith

theorem not_two_successive_best (S : Prefix) (i : ℕ) (hi : 3 ≤ i)
    (hSi : S.last < i) (x : ℝ)
    (hr : BadPair.r i < x - S.sum) (hu : x - S.sum < BadPair.u i)
    (d : ℕ) (hd : S.last < d) (e : ℕ) (he : (S.append d hd).last < e) :
    ¬ (BestUnder x (S.append d hd) ∧ BestUnder x ((S.append d hd).append e he)) := by
  rintro ⟨hb1, hb2⟩
  have hid := least_first_bad_pair S i hi hSi x hr hu
  have hdd := optimal_next_is_least S hd hb1
  have hdi : d = i := Nat.le_antisymm (hdd.2 i hid.1) (hid.2 d hdd.1)
  subst d
  have hie := least_second_bad_pair S i hi hd x hr hu
  have hee := optimal_next_is_least (S.append i hd) he hb2
  have hei : e = BadPair.D i + 1 :=
    Nat.le_antisymm (hee.2 (BadPair.D i + 1) hie.1) (hie.2 e hee.1)
  subst e
  apply bad_pair_not_best S i hi hd x hr
  simpa [greedyPair] using hb2

theorem not_hasBestExtension_bad_pair (S : Prefix) (i : ℕ) (hi : 3 ≤ i)
    (hSi : S.last < i) (x : ℝ)
    (hr : BadPair.r i < x - S.sum) (hu : x - S.sum < BadPair.u i) :
    ¬ HasBestExtension x S := by
  rintro ⟨F, h0, hstep, hbest⟩
  have hs0 : ∃ d, ∃ hd : S.last < d, F 1 = S.append d hd := by
    simpa only [h0] using hstep 0
  obtain ⟨d, hd, h1⟩ := hs0
  have hb1 : BestUnder x (S.append d hd) := by
    rw [← h1]
    exact hbest 1
  have hs1 : ∃ e, ∃ he : (S.append d hd).last < e,
      F 2 = (S.append d hd).append e he := by
    simpa only [h1] using hstep 1
  obtain ⟨e, he, h2⟩ := hs1
  have hb2 : BestUnder x ((S.append d hd).append e he) := by
    rw [← h2]
    exact hbest 2
  exact not_two_successive_best S i hi hSi x hr hu d hd e he ⟨hb1, hb2⟩

end Egyptian
