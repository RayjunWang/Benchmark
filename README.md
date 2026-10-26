# Comparisons of benchmark equivalence relations

Complete Lean proofs of Theorems 1.1–1.6 in the supplied `paper/Benchmark.tex`.
Prepared for https://github.com/RayjunWang/Benchmark.

The entry point is [MainTheorems.lean](MainTheorems.lean). It proves every
main statement and their conjunction using the exact definitions in
[Definitions/Def_BenchmarkRelations.lean](Definitions/Def_BenchmarkRelations.lean).

| Theorem | Formal result |
| --- | --- |
| 1.1 | The countable product of the full binary free-group shift reduces to null difference; the shift is incomparable with every finite real Lp relation, for p≥1. |
| 1.2 | For the extended exponents 1≤p≤∞, Lp reduces to measure equivalence exactly when p≤2. |
| 1.3 | Null difference does not reduce to measure equivalence. |
| 1.4 | Neither null difference nor measure equivalence reduces to the Friedman–Stanley jump of bounded difference. |
| 1.5 | Measure equivalence is strictly below unitary equivalence of all bounded operators on the fixed complex Hilbert space. |
| 1.6 | Arbitrary unitary representations of Z are bireducible with measure equivalence, which is strictly below arbitrary representations of the countably generated free group; those are bireducible with bounded-operator unitary equivalence. |

The sequence relations act on all real sequences. The free-group shift includes
points with stabilizers. Operator and representation Borel structures are the
strong structures specified in the definitions. Probability-measure maps use
the canonical evaluation sigma-algebra; weak-topology arguments prove the
required measurable bridges explicitly.

## Build

The project pins Lean `4.30.0` and Mathlib
`c5ea00351c28e24afc9f0f84379aa41082b1188f`, a revision supported by Prove2Me
when the submissions were prepared.

```text
lake exe cache get
lake build
lake env lean -DautoImplicit=false tools/AxiomAudit.lean
```

The GitHub workflow runs the build and axiom audit. `Benchmark.lean` imports the
delivered source modules. The full-project audit checks every project declaration,
allowing only `propext`, `Classical.choice`, and `Quot.sound`.

## Earlier manuscript

The previous `MeasureEquivalence.tex` theorem numbers correspond as follows:

| Earlier theorem | Benchmark theorem | Complete entry point |
| --- | --- | --- |
| 1.1 | 1.2 | `BenchmarkComparisons.theorem_1_2` |
| 1.2 | 1.3 | `BenchmarkComparisons.theorem_1_3` |
| 1.3 | 1.5 | `OperatorCoding.theorem_13_proved` |
| 1.4 | 1.6 | `OperatorCoding.theorem_14_proved` |

Both manuscripts are in `paper/`. The previous unfinished operator and
representation proofs are completed in this snapshot.

## Verification and Prove2Me

`verification/package-build.json` records the isolated dependency-ordered replay.
Unchanged verified objects are reused only when their source and transitive
dependencies match the recorded hashes and toolchain. New or changed objects
are rebuilt. The complete project axiom audit then runs on the resulting closure.
`verification/source-inventory.json` and `source-manifest.json` bind the source
files to their SHA-256 hashes.

`verification/lake-build/report.json` separately records an actual Lake build of
the full source snapshot and its final default target, using the same pinned
local dependencies for the offline check. Every source module has an explicit
library glob, including the flat sibling modules. The Lake build and a fresh
axiom audit in its environment passed; their logs and source hashes are included.

Independent bounded semantic reviews and independent native checks of the
countable, representation, and paired jump results are included under
`verification/independent-reviews/`. The reports state their scope and limitations.

The public OpenProblem proposal is titled **Comparisons of benchmark equivalence
relations**. Its proposal ID is `77e1f724-fc67-49f6-a4d9-3f1ef77814af`.
Current proof submission IDs and statuses are in `proof-submissions.json`.
This source archive contains complete proofs regardless of the platform queue.
Pending or uncaptured platform acceptance is not claimed as completed by this
source checkpoint; the saved receipts are the authority for server status.
