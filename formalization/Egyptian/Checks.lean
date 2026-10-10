module
/-
Copyright (c) 2026 Yuhang Shi.
SPDX-License-Identifier: AGPL-3.0-only
Released under the GNU Affero General Public License, version 3 only.
-/
public import Egyptian.Main
public import Solution
public meta import Egyptian.Main
public meta import Egyptian.PrefixEnumeration
public meta import Egyptian.PolynomialEnumeration

@[expose] public section

#print axioms Egyptian.explicit_counterexample
#print axioms EgyptianPalomar.explicit_counterexample
#print axioms Egyptian.explicitReal_transcendental
#print axioms Egyptian.explicitReal_not_eventuallyGreedy
#print axioms Egyptian.explicitReal_no_eventually_optimal_sequence
#print axioms Egyptian.approximation_certified
#print axioms Egyptian.PolynomialEnumeration.polyAtQ_complete
#print axioms Egyptian.PrefixInterval.defeatQ_spec
#print axioms Egyptian.least_sequence_crosses
#print axioms Egyptian.eventuallyGreedy_iff_sequences
#print axioms Egyptian.Rn_attained
#print axioms Egyptian.bestUnder_iff_sum_eq_Rn
#print axioms Egyptian.FastSearch.defeatFastQ_eq

#eval (Egyptian.prefixAt 0).denoms
#eval (Egyptian.prefixAt 13).denoms
#eval (List.range 8).map (fun j => (Egyptian.PolynomialEnumeration.polyAt j).coeffList.reverse)
#eval Egyptian.explicitInterval 0
#eval Egyptian.explicitInterval 1
#eval Egyptian.approximation 1
#eval Egyptian.explicitInterval 12
#eval Egyptian.approximation 12

example : Egyptian.approximation 0 = (7/24 : ℚ) := by
  norm_num [Egyptian.approximation, Egyptian.Construction.midpoint,
    Egyptian.Construction.intervals, Egyptian.Construction.interval,
    Egyptian.Construction.RationalInterval.pair, Egyptian.Construction.initial]
