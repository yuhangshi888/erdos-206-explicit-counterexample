# An explicit computable counterexample for Erdős Problem #206

[![Paper DOI](https://img.shields.io/badge/Zenodo-10.5281%2Fzenodo.23283007-blue)](https://doi.org/10.5281/zenodo.23283007)
[![Palomar registration](https://img.shields.io/badge/Palomar-registered%20v1-brightgreen)](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-11-000014&version=1)

This repository contains a Lean 4 formalization of a deterministic construction of a transcendental real number whose best Egyptian underapproximations with strictly increasing denominators are not eventually greedy. The main result is the fully instantiated theorem [`Egyptian.explicit_counterexample`](formalization/Egyptian/Main.lean), together with an executable rational approximation algorithm and a proved error bound.

| Resource | Link |
| --- | --- |
| Paper on Zenodo | [10.5281/zenodo.23283007](https://doi.org/10.5281/zenodo.23283007) |
| Registered formalization | [PALOMAR-2026-10-11-000014 · version 1](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-11-000014&version=1) |
| Exact registered source | [`b0c255255c1b8ba45fd0ab6c693ecce747fd602f`](https://github.com/yuhangshi888/erdos-206-explicit-counterexample/tree/b0c255255c1b8ba45fd0ab6c693ecce747fd602f/formalization) |
| Mechanical verification | [Passed: Lean, nanoda and con-ron](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/38071556700) |
| Preserved proof source | [Palomar Archive copy](https://github.com/PalomarArchive/yuhangshi888--erdos-206-explicit-counterexample--385ee6dc63f2/tree/b0c255255c1b8ba45fd0ab6c693ecce747fd602f/formalization) |

Author: [Yuhang Shi](https://orcid.org/0009-0006-3180-4767), Zhengzhou University. This code repository contains the formalization and exact finite illustration. The paper is distributed separately on Zenodo under an all-rights-reserved notice.

**Palomar registration completed on 11 October 2026.** Version 1 records the exact source commit linked above. Its archived mechanical report, review and source-preservation receipt are available from the registration page. Later documentation updates to this repository do not alter that registered snapshot.

The complete construction and publication bridge have passed the full build under Lean 4.35.0-rc2 and Mathlib commit `065356127b1dc0016f66b7283ce0ce2c4055aa55`. The final axiom and runtime checks also passed.

## Exact theorem

For a positive real number $x$, let

$$
R_n(x)=\max\left\{\sum_{k=0}^{n-1}\frac1{m_k}:
0<m_0<\cdots<m_{n-1},\quad
\sum_{k=0}^{n-1}\frac1{m_k}<x\right\},
$$

where the denominators are integers, and $R_0(x)=0$. Existence of each maximum is proved in [`MaxExists.lean`](formalization/Egyptian/MaxExists.lean).

The construction defines a particular real $x$ and a total rational algorithm $q_n$ such that

$$
\frac14<x<\frac13,\qquad x\text{ is transcendental over }\mathbb Z,
\qquad |x-q_n|\le 2^{-n-1}\quad(n\ge0).
$$

For this same $x$, there do **not** exist a strictly increasing infinite sequence of positive integer denominators $(m_k)_{k\ge0}$ and an index $n_0$ such that

$$
\sum_{k=0}^{n-1}\frac1{m_k}=R_n(x)
\qquad\text{for every }n\ge n_0.
$$

This quantifies over all candidate sequences and all tied best representations. It uses strict underapproximation and distinct denominators. The conclusion is formalized directly in the original maximum-value notation by `Egyptian.explicitReal_no_eventually_optimal_sequence`.

The rational output is `Egyptian.approximation n`; its error bound is `Egyptian.approximation_certified`. The real limit is defined in the classical proof layer. Mathematical computability follows from the total executable rational algorithm and its proved precision bound; a separate `Partrec` or Turing-machine encoding and a computational complexity bound are not supplied.

## Reproduce the verification

Install [elan](https://github.com/leanprover/elan), enter the `formalization` directory, and run:

```sh
cd formalization
lake exe cache get
lake build
lake env lean Egyptian/Checks.lean
```

`lean-toolchain` fixes `leanprover/lean4:v4.35.0-rc2`. The Mathlib commit is `065356127b1dc0016f66b7283ce0ce2c4055aa55`; all dependency revisions are recorded in [`lake-manifest.json`](formalization/lake-manifest.json). Dependencies and build caches are downloaded locally and are not included in this repository.

The first command retrieves the Mathlib build cache. The build checks the complete construction. `Checks.lean` prints the axioms of the final theorems and executes the actual rational interval and midpoint algorithms, including stage 12.

The [verification log](formalization/VERIFICATION_LOG.txt) records the new Lean 4.35.0-rc2 checks on 10 October 2026. The full build completed successfully, and all thirteen actual axiom reports and exact runtime checks passed. These include the complete construction theorem and the independent publication theorem. The printed dependencies of the final theorems are only the standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`. The `Egyptian` proof library and the completed `Solution.lean` contain no `sorry`, `admit`, custom axioms, `unsafe`, `native_decide`, or `implemented_by`. The independent `Challenge.lean` statement deliberately contains three Palomar statement/value placeholders; it is not the proof artifact. No unproved enumeration, interval-exclusion, or termination hypothesis remains in the final theorem.

## Proof and implementation

Every finite increasing denominator prefix is enumerated by a binary support set. Every nonzero integer polynomial is enumerated in the paper's height, degree, and coefficient lexicographic order. At each stage the algorithm first defeats the prescribed prefix throughout a rational open interval, then selects a rational closed subinterval avoiding the prescribed polynomial's roots. The nested intervals determine the unique real $x$.

The Lean recursion retains the original cap minimum, least successful bad-pair index, least successful polynomial grid index, and four-term radius. [`FastSearch.lean`](formalization/Egyptian/FastSearch.lean) proves that an accelerated two-candidate search is equal to the original least-index search on every valid input, so this acceleration preserves the constructed number.

| Entry point | Role |
| --- | --- |
| [`Main.lean`](formalization/Egyptian/Main.lean) | The specific real, executable approximations, and final unconditional theorems |
| [`Construction.lean`](formalization/Egyptian/Construction.lean) | The full rational recursion and global exclusion arguments |
| [`Checks.lean`](formalization/Egyptian/Checks.lean) | Axiom reports and exact runtime examples |
| [Detailed formalization guide](formalization/README.md) | All modules, definitions, and verification scope |
| [Execution crosscheck](formalization/EXECUTION_CROSSCHECK.json) | Exact agreement with the original certificate for stages 0–12 |

## Finite illustration

The [exact Python illustration](computation/egyptian_exact_generator.py) is accompanied by a [twelve-stage certificate](computation/egyptian_exact_certificate.json).

The optional Python illustration uses only the standard library and exact rational arithmetic. From the repository root:

```sh
python3 computation/egyptian_exact_generator.py --stages 3 --seconds 60 --output reproduced_certificate.json
```

Its permitted finite scope is at most 32 stages and 60 seconds. On reaching the deadline it saves a valid certificate for the fully completed stages. Such a finite calculation illustrates the definitions; the infinite theorem is justified by the Lean proof. The independent execution crosscheck verified all 13 interval pairs from stages 0–12 against the existing exact certificate under the new toolchain, in about 9.20 seconds.

## Relation to previous work

[Erdős Problem #206](https://erdosproblems.com/206) concerns eventual greediness of best Egyptian underapproximations. Erdős and Graham already asserted the existence of failing irrational numbers in 1980. [Kovač's 2024 paper](https://arxiv.org/abs/2406.07218v3) proved the measure-zero theorem, and its two-term obstruction is used here. Effective Baire and nested-interval diagonalization are established methods. [Kovač and Tang's 2026 paper](https://arxiv.org/abs/2607.28387v2) proves the positive rational case.

This repository gives a particular deterministic computable transcendental example and a kernel-checked proof of its complete construction. It does not claim the first existence result, the first proof of the measure-zero theorem, the first formalization of Problem #206, or established global priority. A bounded literature audit was conducted on the public sources as of 10 October 2026; it does not establish global priority. Acceptance of an algorithmic example by the problem's authors or maintainers is not asserted.

## Integrity and rights

[`MIGRATION_BASELINE.json`](MIGRATION_BASELINE.json) records the hashes of the 22 accepted baseline files before toolchain and module-system migration. The original proof sources remain unchanged outside this publication copy. The new verification record and [`SHA256SUMS`](SHA256SUMS) identify the migrated release snapshot.

Copyright © 2026 Yuhang Shi. The original code is licensed under the GNU Affero General Public License, version 3 only (**AGPL-3.0-only**); see [`LICENSE`](LICENSE). Lean, Mathlib, and other third-party dependencies retain their own copyright notices and licenses. The separately distributed paper is not licensed by this code repository.
