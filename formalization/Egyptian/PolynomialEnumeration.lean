module
/-
Copyright (c) 2026 Yuhang Shi.
SPDX-License-Identifier: AGPL-3.0-only
Released under the GNU Affero General Public License, version 3 only.
-/
public import Mathlib

@[expose] public section

/-! The manuscript's integer polynomial order: increasing height
`natDegree + sum |coeff|`, then increasing degree, then ascending lexicographic
coefficient vectors. All list construction and indexing are executable. -/

namespace Egyptian.PolynomialEnumeration

/-- Ascending integer box `[-h, ..., h]`. -/
def box (h : ℕ) : List ℤ :=
  (List.range (2 * h + 1)).map (fun (i : ℕ) => (i : ℤ) - (h : ℤ))

theorem mem_box {h : ℕ} {a : ℤ} : a ∈ box h ↔ -(h : ℤ) ≤ a ∧ a ≤ (h : ℤ) := by
  constructor
  · intro ha
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
    have hib : i < 2 * h + 1 := List.mem_range.mp hi
    omega
  · intro ha
    have hnonneg : 0 ≤ a + (h : ℤ) := by omega
    refine List.mem_map.mpr ⟨(a + (h : ℤ)).toNat, ?_, ?_⟩
    · apply List.mem_range.mpr
      have hcast : ((a + (h : ℤ)).toNat : ℤ) = a + (h : ℤ) :=
        Int.toNat_of_nonneg hnonneg
      omega
    · rw [Int.toNat_of_nonneg hnonneg]
      ring

/-- Cartesian powers with the first coefficient varying slowest: lex order. -/
def vectors (h : ℕ) : ℕ → List (List ℤ)
  | 0 => [[]]
  | n + 1 => (box h).flatMap fun a => (vectors h n).map (a :: ·)

theorem mem_vectors (h n : ℕ) (v : List ℤ) :
    v ∈ vectors h n ↔ v.length = n ∧ ∀ a ∈ v, a ∈ box h := by
  induction n generalizing v with
  | zero =>
    constructor
    · intro hv
      have hv' : v = [] := by simpa [vectors] using hv
      subst v
      simp
    · rintro ⟨hlen, _⟩
      have hv : v = [] := List.length_eq_zero_iff.mp hlen
      simp [vectors, hv]
  | succ n ih =>
    cases v with
    | nil => simp [vectors]
    | cons a v =>
      simp only [vectors, List.mem_flatMap, List.mem_map, List.cons.injEq]
      constructor
      · rintro ⟨b, hb, w, hw, hba, hwv⟩
        subst b
        subst w
        obtain ⟨hlen, hall⟩ := (ih v).mp hw
        refine ⟨by simp [hlen], ?_⟩
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact hb
        · exact hall c hc
      · rintro ⟨hlen, hall⟩
        refine ⟨a, hall a (by simp), v, ?_, rfl, rfl⟩
        apply (ih v).mpr
        refine ⟨by simpa using hlen, ?_⟩
        intro c hc
        exact hall c (by simp [hc])

/-- Exact ascending coefficient list to polynomial, using computable Finsupp. -/
def ofCoeffs (v : List ℤ) : Polynomial ℤ := ⟨⟨v.toFinsupp⟩⟩

@[simp] theorem coeff_ofCoeffs (v : List ℤ) (i : ℕ) :
    (ofCoeffs v).coeff i = v.getD i 0 := rfl

/-- Canonical coefficient vector, including internal and initial zero entries. -/
def coeffs (p : Polynomial ℤ) : List ℤ :=
  (List.range (p.natDegree + 1)).map p.coeff

@[simp] theorem coeffs_length (p : Polynomial ℤ) : (coeffs p).length = p.natDegree + 1 := by
  simp [coeffs]

theorem ofCoeffs_coeffs (p : Polynomial ℤ) : ofCoeffs (coeffs p) = p := by
  ext i
  rw [coeff_ofCoeffs]
  by_cases hi : i < p.natDegree + 1
  · have hlen : i < (coeffs p).length := by simpa using hi
    rw [List.getD_eq_getElem _ _ hlen]
    simp [coeffs]
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi)]
    exact (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)).symm

def weight (v : List ℤ) : ℕ := (v.map Int.natAbs).sum

def height (p : Polynomial ℤ) : ℕ := p.natDegree + weight (coeffs p)

theorem natAbs_le_weight {v : List ℤ} {a : ℤ} (ha : a ∈ v) : a.natAbs ≤ weight v := by
  apply List.le_sum_of_mem
  exact List.mem_map.mpr ⟨a, ha, rfl⟩

theorem coeff_mem_coeffs (p : Polynomial ℤ) : p.coeff p.natDegree ∈ coeffs p := by
  exact List.mem_map.mpr ⟨p.natDegree, List.mem_range.mpr (Nat.lt_succ_self _), rfl⟩

theorem degree_lt_height (p : Polynomial ℤ) (hp : p ≠ 0) : p.natDegree < height p := by
  have habs : 0 < (p.coeff p.natDegree).natAbs := by
    have hne := Polynomial.leadingCoeff_ne_zero.mpr hp
    simpa only [Polynomial.coeff_natDegree, Int.natAbs_pos] using hne
  have hw := natAbs_le_weight (coeff_mem_coeffs p)
  unfold height
  omega

theorem coeffs_in_box (p : Polynomial ℤ) : ∀ a ∈ coeffs p, a ∈ box (height p) := by
  intro a ha
  have hb : a.natAbs ≤ height p :=
    (natAbs_le_weight ha).trans (Nat.le_add_left _ _)
  have habs : |a| ≤ (height p : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hb
  exact mem_box.mpr (abs_le.mp habs)

/-- Filtering preserves the box-vector lex order. -/
def Eligible (h d : ℕ) (p : Polynomial ℤ) : Prop :=
  p.leadingCoeff ≠ 0 ∧ p.natDegree = d ∧ height p = h

instance eligibleDecidable (h d : ℕ) (p : Polynomial ℤ) : Decidable (Eligible h d p) :=
  inferInstanceAs (Decidable (p.leadingCoeff ≠ 0 ∧ p.natDegree = d ∧ height p = h))

def degreeLevel (h d : ℕ) : List (Polynomial ℤ) :=
  ((vectors h (d + 1)).map ofCoeffs).filter
    (fun p => decide (Eligible h d p))

/-- Complete finite height level, degrees increasing from `0` to `h-1`. -/
def level (h : ℕ) : List (Polynomial ℤ) :=
  (List.range h).flatMap (degreeLevel h)

theorem mem_level_iff (h : ℕ) (p : Polynomial ℤ) :
    p ∈ level h ↔ p ≠ 0 ∧ height p = h := by
  constructor
  · intro hp
    obtain ⟨d, _, hd⟩ := List.mem_flatMap.mp hp
    have hf : Eligible h d p := of_decide_eq_true (List.mem_filter.mp hd).2
    exact ⟨Polynomial.leadingCoeff_ne_zero.mp hf.1, hf.2.2⟩
  · rintro ⟨hp, hh⟩
    apply List.mem_flatMap.mpr
    refine ⟨p.natDegree, List.mem_range.mpr ?_, ?_⟩
    · rw [← hh]
      exact degree_lt_height p hp
    · apply List.mem_filter.mpr
      constructor
      · apply List.mem_map.mpr
        refine ⟨coeffs p, ?_, ofCoeffs_coeffs p⟩
        apply (mem_vectors h (p.natDegree + 1) (coeffs p)).mpr
        refine ⟨coeffs_length p, ?_⟩
        simpa [hh] using coeffs_in_box p
      · exact decide_eq_true (show Eligible h p.natDegree p from
          ⟨Polynomial.leadingCoeff_ne_zero.mpr hp, rfl, hh⟩)

@[simp] theorem height_C (a : ℤ) : height (Polynomial.C a) = a.natAbs := by
  simp [height, weight, coeffs]

theorem level_nonempty {h : ℕ} (hh : 0 < h) : 0 < (level h).length := by
  have hne : Polynomial.C (h : ℤ) ≠ 0 := by
    apply Polynomial.C_ne_zero.mpr
    exact_mod_cast (Nat.ne_of_gt hh)
  have hm : Polynomial.C (h : ℤ) ∈ level h :=
    (mem_level_iff h _).mpr ⟨hne, by rw [height_C]; simp⟩
  exact List.length_pos_iff.mpr (List.ne_nil_of_mem hm)

/-- Concatenate exactly the positive height levels up to `H`. -/
def through (H : ℕ) : List (Polynomial ℤ) :=
  (List.range H).flatMap fun h => level (h + 1)

@[simp] theorem through_zero : through 0 = [] := rfl

theorem through_succ (H : ℕ) : through (H + 1) = through H ++ level (H + 1) := by
  simp [through, List.range_succ]

theorem through_length_lower (H : ℕ) : H ≤ (through H).length := by
  induction H with
  | zero => simp
  | succ H ih =>
    rw [through_succ, List.length_append]
    have hh : 0 < (level (H + 1)).length := level_nonempty (by omega)
    omega

theorem through_length_mono : Monotone (fun H => (through H).length) := by
  apply monotone_nat_of_le_succ
  intro H
  rw [through_succ, List.length_append]
  omega

theorem through_nonzero {H : ℕ} {p : Polynomial ℤ} (hp : p ∈ through H) : p ≠ 0 := by
  obtain ⟨h, _, hh⟩ := List.mem_flatMap.mp hp
  exact ((mem_level_iff (h + 1) p).mp hh).1

def zeroPoly : Polynomial ℤ := ofCoeffs []

theorem zeroPoly_eq : zeroPoly = 0 := by
  ext i
  simp [zeroPoly]

theorem through_getD {H K j : ℕ} (hHK : H ≤ K) (hj : j < (through H).length) :
    (through K).getD j zeroPoly = (through H).getD j zeroPoly := by
  induction K, hHK using Nat.le_induction with
  | base => rfl
  | succ K hHK ih =>
    rw [through_succ, List.getD_append]
    · exact ih
    · exact lt_of_lt_of_le hj (through_length_mono hHK)

theorem exists_height (j : ℕ) : ∃ H, j < (through H).length := by
  refine ⟨j + 1, ?_⟩
  have hh := through_length_lower (j + 1)
  omega

/-- Smallest height whose concatenated list contains the requested index. -/
def leastHeight (j : ℕ) : ℕ := Nat.find (exists_height j)

theorem leastHeight_spec (j : ℕ) : j < (through (leastHeight j)).length :=
  Nat.find_spec (exists_height j)

/-- Zero-based stream: index `j` is the original manuscript's `P_(j+1)`. -/
def polyAt (j : ℕ) : Polynomial ℤ :=
  (through (leastHeight j)).getD j zeroPoly

theorem polyAt_nonzero (j : ℕ) : polyAt j ≠ 0 := by
  unfold polyAt
  rw [List.getD_eq_getElem _ _ (leastHeight_spec j)]
  exact through_nonzero (List.getElem_mem _)

theorem polyAt_complete (p : Polynomial ℤ) (hp : p ≠ 0) : ∃ j, polyAt j = p := by
  have hpos : 0 < height p := lt_of_le_of_lt (Nat.zero_le _) (degree_lt_height p hp)
  have hmem : p ∈ through (height p) := by
    apply List.mem_flatMap.mpr
    refine ⟨height p - 1, List.mem_range.mpr (by omega), ?_⟩
    have hh : height p - 1 + 1 = height p := by omega
    rw [hh]
    exact (mem_level_iff (height p) p).mpr ⟨hp, rfl⟩
  obtain ⟨j, hj, heq⟩ := List.getElem_of_mem hmem
  refine ⟨j, ?_⟩
  have hle : leastHeight j ≤ height p := Nat.find_min' (exists_height j) hj
  have hget := through_getD hle (leastHeight_spec j)
  unfold polyAt
  rw [← hget, List.getD_eq_getElem _ _ hj]
  exact heq

theorem getD_coeffs (p : Polynomial ℤ) (i : ℕ) : (coeffs p).getD i 0 = p.coeff i := by
  have h := congrArg (fun q : Polynomial ℤ => q.coeff i) (ofCoeffs_coeffs p)
  simpa only [coeff_ofCoeffs] using h

/-- Computable coefficient-wise integer-to-rational conversion. Polynomial.map
itself uses the abstract polynomial ring operations, so is avoided in execution. -/
def rationalize (p : Polynomial ℤ) : Polynomial ℚ :=
  ⟨⟨((coeffs p).map (fun (a : ℤ) => (a : ℚ))).toFinsupp⟩⟩

theorem rationalize_eq_map (p : Polynomial ℤ) :
    rationalize p = p.map (Int.castRingHom ℚ) := by
  ext i
  rw [Polynomial.coeff_map]
  change ((coeffs p).map (fun (a : ℤ) => (a : ℚ))).getD i 0 = (p.coeff i : ℚ)
  have h := List.getD_map (l := coeffs p) (d := (0 : ℤ)) (n := i)
    (fun (a : ℤ) => (a : ℚ))
  simpa only [Int.cast_zero, getD_coeffs] using h

theorem rationalize_natDegree (p : Polynomial ℤ) :
    (rationalize p).natDegree = p.natDegree := by
  rw [rationalize_eq_map]
  exact Polynomial.natDegree_map_eq_of_injective Int.cast_injective p

def polyAtQ (j : ℕ) : Polynomial ℚ := rationalize (polyAt j)

theorem polyAtQ_eq_map (j : ℕ) : polyAtQ j = (polyAt j).map (Int.castRingHom ℚ) :=
  rationalize_eq_map (polyAt j)

theorem polyAtQ_natDegree (j : ℕ) : (polyAtQ j).natDegree = (polyAt j).natDegree :=
  rationalize_natDegree (polyAt j)

theorem polyAtQ_nonzero (j : ℕ) : polyAtQ j ≠ 0 := by
  rw [polyAtQ_eq_map]
  exact (Polynomial.map_ne_zero_iff (f := Int.castRingHom ℚ) Int.cast_injective).mpr
    (polyAt_nonzero j)

theorem polyAtQ_complete (p : Polynomial ℤ) (hp : p ≠ 0) :
    ∃ j, polyAtQ j = p.map (Int.castRingHom ℚ) := by
  obtain ⟨j, hj⟩ := polyAt_complete p hp
  exact ⟨j, by rw [polyAtQ_eq_map, hj]⟩

end Egyptian.PolynomialEnumeration
