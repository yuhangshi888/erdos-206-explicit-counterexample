module
/-
Copyright (c) 2026 Yuhang Shi.
SPDX-License-Identifier: AGPL-3.0-only
Released under the GNU Affero General Public License, version 3 only.
-/
public import Egyptian.Basic

@[expose] public section

/-! Executable rational constrained greedy steps and their finite crossing property.
Real comparisons occur only in proved specifications, not in the denominator algorithm. -/

namespace Egyptian

def unitQ (m : ℕ) : ℚ := (m : ℚ)⁻¹

def AllowedQ (c q : ℚ) (M m : ℕ) : Prop := M < m ∧ q + unitQ m < c

def IsLeastAllowedQ (c q : ℚ) (M m : ℕ) : Prop :=
  AllowedQ c q M m ∧ ∀ d, AllowedQ c q M d → m ≤ d

/-- The strict convention uses floor plus one, including at integer reciprocals. -/
def greedyDenomQ (c q : ℚ) (M : ℕ) : ℕ :=
  max (M + 1) (Nat.floor ((c - q)⁻¹) + 1)

theorem last_lt_greedyDenomQ (c q : ℚ) (M : ℕ) : M < greedyDenomQ c q M := by
  exact lt_of_lt_of_le (Nat.lt_succ_self M) (le_max_left _ _)

theorem greedyDenomQ_least {c q : ℚ} (hq : q < c) (M : ℕ) :
    IsLeastAllowedQ c q M (greedyDenomQ c q M) := by
  have hr : 0 < c - q := sub_pos.mpr hq
  have hm : 0 < greedyDenomQ c q M :=
    lt_of_le_of_lt (Nat.zero_le M) (last_lt_greedyDenomQ c q M)
  have hi : (c - q)⁻¹ < (greedyDenomQ c q M : ℚ) := by
    have hf := Nat.lt_floor_add_one ((c - q)⁻¹)
    have hb : Nat.floor ((c - q)⁻¹) + 1 ≤ greedyDenomQ c q M := le_max_right _ _
    exact lt_of_lt_of_le (by exact_mod_cast hf) (by exact_mod_cast hb)
  have hf : unitQ (greedyDenomQ c q M) < c - q :=
    (inv_lt_comm₀ (Nat.cast_pos.mpr hm) hr).2 hi
  refine ⟨⟨last_lt_greedyDenomQ c q M, by dsimp [unitQ] at hf; change q + (greedyDenomQ c q M : ℚ)⁻¹ < c; linarith⟩, ?_⟩
  intro d hd
  have hdp : 0 < d := lt_of_le_of_lt (Nat.zero_le M) hd.1
  have hdi : (c - q)⁻¹ < (d : ℚ) :=
    (inv_lt_comm₀ (Nat.cast_pos.mpr hdp) hr).1 (by have hd2 := hd.2; dsimp [unitQ] at hd2; linarith)
  apply max_le
  · have hMd := hd.1; omega
  · have hfl : Nat.floor ((c - q)⁻¹) < d :=
      (Nat.floor_lt (le_of_lt (inv_pos.mpr hr))).2 hdi
    omega

@[simp] theorem cast_unitQ (m : ℕ) : (unitQ m : ℝ) = unit m := by
  simp [unitQ, unit]

theorem allowedQ_iff_real (c q : ℚ) (M m : ℕ) :
    AllowedQ c q M m ↔ Allowed (c : ℝ) (q : ℝ) M m := by
  simp only [AllowedQ, Allowed]
  constructor
  · rintro ⟨hM, h⟩
    refine ⟨hM, ?_⟩
    have hc : ((q + unitQ m : ℚ) : ℝ) < (c : ℝ) := Rat.cast_lt.mpr h
    simpa only [Rat.cast_add, cast_unitQ] using hc
  · rintro ⟨hM, h⟩
    refine ⟨hM, ?_⟩
    have hc : ((q + unitQ m : ℚ) : ℝ) < (c : ℝ) := by
      simpa only [Rat.cast_add, cast_unitQ] using h
    exact Rat.cast_lt.mp hc

theorem greedyDenomQ_least_real {c q : ℚ} (hq : q < c) (M : ℕ) :
    IsLeastAllowed (c : ℝ) (q : ℝ) M (greedyDenomQ c q M) := by
  obtain ⟨h, hmin⟩ := greedyDenomQ_least hq M
  exact ⟨(allowedQ_iff_real c q M _).1 h,
    fun d hd => hmin d ((allowedQ_iff_real c q M d).2 hd)⟩

def greedyStepQ (c : ℚ) (S : Prefix) : Prefix :=
  S.append (greedyDenomQ c S.sumQ S.last) (last_lt_greedyDenomQ c S.sumQ S.last)

def greedyIterQ (c : ℚ) (S : Prefix) : ℕ → Prefix
  | 0 => S
  | n + 1 => greedyStepQ c (greedyIterQ c S n)

@[simp] theorem greedyIterQ_zero (c : ℚ) (S : Prefix) : greedyIterQ c S 0 = S := rfl
@[simp] theorem greedyIterQ_succ (c : ℚ) (S : Prefix) (n : ℕ) :
    greedyIterQ c S (n + 1) = greedyStepQ c (greedyIterQ c S n) := rfl

@[simp] theorem greedyStepQ_last (c : ℚ) (S : Prefix) :
    (greedyStepQ c S).last = greedyDenomQ c S.sumQ S.last := by
  simp [greedyStepQ]

@[simp] theorem greedyStepQ_sumQ (c : ℚ) (S : Prefix) :
    (greedyStepQ c S).sumQ = S.sumQ + unitQ (greedyDenomQ c S.sumQ S.last) := by
  simp [greedyStepQ, unitQ]

@[simp] theorem greedyStepQ_sum (c : ℚ) (S : Prefix) :
    (greedyStepQ c S).sum = S.sum + unit (greedyDenomQ c S.sumQ S.last) := by
  simp [greedyStepQ]

@[simp] theorem greedyStepQ_length (c : ℚ) (S : Prefix) :
    (greedyStepQ c S).length = S.length + 1 := by simp [greedyStepQ]

@[simp] theorem greedyIterQ_length (c : ℚ) (S : Prefix) (n : ℕ) :
    (greedyIterQ c S n).length = S.length + n := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih, Nat.add_assoc]

theorem greedyIterQ_below {c : ℚ} (S : Prefix) (hq : S.sumQ < c) (n : ℕ) :
    (greedyIterQ c S n).sumQ < c := by
  induction n with
  | zero => exact hq
  | succ n ih =>
    have h := (greedyDenomQ_least ih (greedyIterQ c S n).last).1.2
    simpa using h

theorem greedyIterQ_least {c : ℚ} (S : Prefix) (hq : S.sumQ < c) (n : ℕ) :
    IsLeastAllowed (c : ℝ) (greedyIterQ c S n).sum (greedyIterQ c S n).last
      (greedyIterQ c S (n + 1)).last := by
  simpa using greedyDenomQ_least_real (greedyIterQ_below S hq n) (greedyIterQ c S n).last

theorem greedyIterQ_sum_succ (c : ℚ) (S : Prefix) (n : ℕ) :
    (greedyIterQ c S (n + 1)).sum = (greedyIterQ c S n).sum +
      unit (greedyIterQ c S (n + 1)).last := by simp

theorem least_allowed_excludes_predecessor {c q : ℝ} {M m : ℕ}
    (hl : IsLeastAllowed c q M m) (hskip : M + 1 < m) :
    c ≤ q + unit (m - 1) := by
  by_contra hnot
  have hp : M < m - 1 := by omega
  have hm := hl.2 (m - 1) ⟨hp, lt_of_not_ge hnot⟩
  omega

theorem least_allowed_of_predecessor {x q : ℝ} {M m : ℕ}
    (hfeas : Allowed x q M m)
    (hcap : m = M + 1 ∨ x ≤ q + unit (m - 1)) :
    IsLeastAllowed x q M m := by
  refine ⟨hfeas, ?_⟩
  intro d hd
  by_contra hnot
  have hdm : d < m := Nat.lt_of_not_ge hnot
  rcases hcap with hnext | hcap
  · have hMd := hd.1
    omega
  · have hdp : 0 < d := lt_of_le_of_lt (Nat.zero_le _) hd.1
    have hpred : d ≤ m - 1 := by omega
    have hpredp : 0 < m - 1 := lt_of_lt_of_le hdp hpred
    have hi : unit (m - 1) ≤ unit d :=
      (inv_le_inv₀ (Nat.cast_pos.mpr hpredp) (Nat.cast_pos.mpr hdp)).2
        (by exact_mod_cast hpred)
    linarith [hd.2]

theorem least_allowed_cap {c q : ℝ} {M m : ℕ}
    (hl : IsLeastAllowed c q M m) (hskip : M + 1 < m) :
    c ≤ q + unit (m - 1) := least_allowed_excludes_predecessor hl hskip

theorem least_allowed_stable_cap {c q x : ℝ} {M m : ℕ}
    (hl : IsLeastAllowed c q M m) (hx : q + unit m < x)
    (hcap : M + 1 < m → x < q + unit (m - 1)) :
    IsLeastAllowed x q M m := by
  apply least_allowed_of_predecessor ⟨hl.1.1, hx⟩
  by_cases hs : M + 1 < m
  · exact Or.inr (le_of_lt (hcap hs))
  · exact Or.inl (by have hm := hl.1.1; omega)

theorem least_allowed_stable_down {c q x : ℝ} {M m : ℕ}
    (h : IsLeastAllowed c q M m) (hx : q + unit m < x) (hxc : x ≤ c) :
    IsLeastAllowed x q M m := by
  refine ⟨⟨h.1.1, hx⟩, ?_⟩
  intro d hd
  exact h.2 d ⟨hd.1, lt_of_lt_of_le hd.2 hxc⟩

theorem greedyIterQ_sum_mono (c : ℚ) (S : Prefix) :
    Monotone (fun n => (greedyIterQ c S n).sum) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [greedyIterQ_sum_succ]
  exact le_add_of_nonneg_right (inv_nonneg.mpr (Nat.cast_nonneg _))

/-- Every finite greedy choice made towards c persists at each x between the
final partial sum and c. This removes a need to compute per-step upper caps. -/
theorem greedyIterQ_stable_below {c : ℚ} (S : Prefix) (hq : S.sumQ < c)
    (N n : ℕ) (hn : n < N) {x : ℝ}
    (hx : (greedyIterQ c S N).sum < x) (hxc : x ≤ (c : ℝ)) :
    IsLeastAllowed x (greedyIterQ c S n).sum (greedyIterQ c S n).last
      (greedyIterQ c S (n + 1)).last := by
  apply least_allowed_stable_down (greedyIterQ_least S hq n) ?_ hxc
  rw [← greedyIterQ_sum_succ]
  exact lt_of_le_of_lt (greedyIterQ_sum_mono c S (by omega : n + 1 ≤ N)) hx

/-- Any optimal nested chain must coincide with a finite prescribed least-step
continuation. The stability premise is an explicit local denominator condition,
not the desired nonexistence conclusion. -/
theorem best_extension_eq_greedyIterQ {x : ℝ} {c : ℚ} {S : Prefix}
    (F : ℕ → Prefix) (hzero : F 0 = S)
    (hrec : ∀ n, ∃ d, ∃ hd : (F n).last < d, F (n + 1) = (F n).append d hd)
    (hbest : ∀ n, BestUnder x (F n)) (N : ℕ)
    (hstable : ∀ n, n < N → IsLeastAllowed x (greedyIterQ c S n).sum
      (greedyIterQ c S n).last (greedyIterQ c S (n + 1)).last) :
    ∀ n, n ≤ N → F n = greedyIterQ c S n := by
  intro n
  induction n with
  | zero => intro _; simpa using hzero
  | succ n ih =>
    intro hn
    have hie := ih (by omega : n ≤ N)
    obtain ⟨d, hd, heq⟩ := hrec n
    have hb : BestUnder x ((F n).append d hd) := by
      rw [← heq]
      exact hbest (n + 1)
    have hf := optimal_next_is_least (F n) hd hb
    have hf' : IsLeastAllowed x (greedyIterQ c S n).sum (greedyIterQ c S n).last d := by
      simpa only [hie] using hf
    have hdeq := least_allowed_unique hf' (hstable n (by omega))
    have hdeq' : d = greedyDenomQ c (greedyIterQ c S n).sumQ
        (greedyIterQ c S n).last := by simpa using hdeq
    rw [heq]
    apply Prefix.ext
    simp only [Prefix.denoms_append, greedyIterQ_succ, greedyStepQ, Prefix.denoms_append]
    rw [hie, hdeq']

/-- Shift an optimal infinite extension past a finite forced greedy block. -/
theorem hasBestExtension_greedyIterQ {x : ℝ} {c : ℚ} {S : Prefix}
    (h : HasBestExtension x S) (N : ℕ)
    (hstable : ∀ n, n < N → IsLeastAllowed x (greedyIterQ c S n).sum
      (greedyIterQ c S n).last (greedyIterQ c S (n + 1)).last) :
    HasBestExtension x (greedyIterQ c S N) := by
  obtain ⟨F, hzero, hrec, hbest⟩ := h
  have heq := best_extension_eq_greedyIterQ F hzero hrec hbest N hstable N (le_refl N)
  refine ⟨fun n => F (N + n), by simpa using heq, ?_, ?_⟩
  · intro n
    simpa only [Nat.add_assoc] using hrec (N + n)
  · intro n
    exact hbest (N + n)

/-- Least permitted denominators cannot keep the partial sums below a lower
fixed target. The proof bounds all denominators linearly and compares with the
harmonic series; no convergence property is assumed. -/
theorem least_sequence_crosses {q : ℕ → ℝ} {M : ℕ → ℕ} {a c : ℝ}
    (hac : a < c)
    (hstep : ∀ n, q (n + 1) = q n + unit (M (n + 1)))
    (hleast : ∀ n, IsLeastAllowed c (q n) (M n) (M (n + 1))) :
    ∃ n, a < q n := by
  by_contra hnot
  have hbelow : ∀ n, q n ≤ a := by
    intro n
    exact le_of_not_gt (fun h => hnot ⟨n, h⟩)
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.mpr hac)
  let K : ℕ := k + 1
  have hK : 0 < K := by dsimp [K]; omega
  have hunitK : unit K < c - a := by
    simpa [K, unit, Nat.cast_add, one_div] using hk
  have hbound (n : ℕ) : M (n + 1) ≤ max (M n + 1) K := by
    apply (hleast n).2
    refine ⟨lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _), ?_⟩
    have hmp : 0 < max (M n + 1) K := lt_of_lt_of_le hK (le_max_right _ _)
    have hsmall : unit (max (M n + 1) K) ≤ unit K :=
      (inv_le_inv₀ (Nat.cast_pos.mpr hmp) (Nat.cast_pos.mpr hK)).2
        (by exact_mod_cast (le_max_right (M n + 1) K))
    linarith [hbelow n]
  let C : ℕ := M 0 + K + 1
  have hC : 0 < C := by dsimp [C]; omega
  have hlinear : ∀ n, M n ≤ C + n := by
    intro n
    induction n with
    | zero => dsimp [C]; omega
    | succ n ih =>
      have hb := hbound n
      have hmax : max (M n + 1) K ≤ C + (n + 1) := by
        apply max_le
        · omega
        · dsimp [C]; omega
      exact le_trans hb hmax
  have hrecip (n : ℕ) : 1 / ((n : ℝ) + 1) ≤ ((C : ℝ) + 1) * unit (M (n + 1)) := by
    have hmp : 0 < M (n + 1) :=
      lt_of_le_of_lt (Nat.zero_le _) (hleast n).1.1
    have hb : M (n + 1) ≤ (C + 1) * (n + 1) := by
      have hlin := hlinear (n + 1)
      have hc : 1 ≤ C := hC
      nlinarith
    have hbr : (M (n + 1) : ℝ) ≤ ((C : ℝ) + 1) * ((n : ℝ) + 1) := by
      exact_mod_cast hb
    have hn : 0 < (n : ℝ) + 1 := by positivity
    have hd : 0 < (M (n + 1) : ℝ) := Nat.cast_pos.mpr hmp
    have hdiv : 1 / ((n : ℝ) + 1) ≤ ((C : ℝ) + 1) / (M (n + 1) : ℝ) := by
      apply (div_le_div_iff₀ hn hd).2
      simpa using hbr
    simpa [unit, div_eq_mul_inv] using hdiv
  have hsum : ∀ n, (∑ i ∈ Finset.range n, 1 / ((i : ℝ) + 1)) ≤
      ((C : ℝ) + 1) * (q n - q 0) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, hstep n]
      have hr := hrecip n
      nlinarith
  obtain ⟨n, hn⟩ := (Real.tendsto_sum_range_one_div_nat_succ_atTop.eventually_gt_atTop
    (((C : ℝ) + 1) * (a - q 0))).exists
  have hsb := hsum n
  have hmul : ((C : ℝ) + 1) * (q n - q 0) ≤ ((C : ℝ) + 1) * (a - q 0) :=
    mul_le_mul_of_nonneg_left (by linarith [hbelow n]) (by positivity)
  linarith

/-- A finite, executable rational greedy extension crosses every lower real
threshold, while all of its partial sums remain strictly below its target. -/
theorem greedyIterQ_crosses {c : ℚ} (S : Prefix) (hq : S.sumQ < c)
    {a : ℝ} (hac : a < (c : ℝ)) :
    ∃ n, a < (greedyIterQ c S n).sum ∧ (greedyIterQ c S n).sum < (c : ℝ) := by
  obtain ⟨n, hn⟩ := least_sequence_crosses hac
    (greedyIterQ_sum_succ c S) (greedyIterQ_least S hq)
  refine ⟨n, hn, ?_⟩
  have hb := greedyIterQ_below S hq n
  have hbr : ((greedyIterQ c S n).sumQ : ℝ) < (c : ℝ) := Rat.cast_lt.mpr hb
  simpa using hbr

/-- The finite crossing result and monotonicity also give the usual real
convergence statement for the executable rational constrained greedy chain. -/
theorem greedyIterQ_tendsto {c : ℚ} (S : Prefix) (hq : S.sumQ < c) :
    Filter.Tendsto (fun n => (greedyIterQ c S n).sum) Filter.atTop (nhds (c : ℝ)) := by
  apply tendsto_order.2
  constructor
  · intro a hac
    obtain ⟨n, hn, _⟩ := greedyIterQ_crosses S hq hac
    apply Filter.eventually_atTop.2
    refine ⟨n, ?_⟩
    intro m hm
    exact lt_of_lt_of_le hn (greedyIterQ_sum_mono c S hm)
  · intro b hcb
    apply Filter.Eventually.of_forall
    intro n
    have hr : ((greedyIterQ c S n).sumQ : ℝ) < (c : ℝ) :=
      Rat.cast_lt.mpr (greedyIterQ_below S hq n)
    have hsum : (greedyIterQ c S n).sum < (c : ℝ) := by simpa using hr
    exact lt_trans hsum hcb

/-- The rational crossing predicate is decidable and the first crossing index
is executable. Termination is proved by the preceding harmonic argument. -/
theorem greedyIterQ_crossesQ {c : ℚ} (S : Prefix) (hq : S.sumQ < c)
    {a : ℚ} (hac : a < c) : ∃ n, a < (greedyIterQ c S n).sumQ := by
  obtain ⟨n, hn, _⟩ := greedyIterQ_crosses S hq (Rat.cast_lt.mpr hac : (a : ℝ) < (c : ℝ))
  refine ⟨n, ?_⟩
  have hreal : (a : ℝ) < ((greedyIterQ c S n).sumQ : ℝ) := by simpa using hn
  exact Rat.cast_lt.mp hreal

def crossingTimeQ (c a : ℚ) (S : Prefix) (hq : S.sumQ < c) (hac : a < c) : ℕ :=
  Nat.find (greedyIterQ_crossesQ S hq hac)

theorem crossingTimeQ_spec (c a : ℚ) (S : Prefix) (hq : S.sumQ < c) (hac : a < c) :
    a < (greedyIterQ c S (crossingTimeQ c a S hq hac)).sumQ ∧
      (greedyIterQ c S (crossingTimeQ c a S hq hac)).sumQ < c :=
  ⟨Nat.find_spec (greedyIterQ_crossesQ S hq hac), greedyIterQ_below S hq _⟩

end Egyptian
