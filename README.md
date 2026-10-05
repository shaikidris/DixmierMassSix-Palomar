# Six homogeneous components in the first Weyl algebra

This development proves that, over every characteristic-zero field K, elements
P and Q of the first Weyl algebra with QP−PQ=1 generate the algebra whenever P
has at most six nonzero homogeneous components for deg X=1 and deg Y=−1.
There is no degree, order, support or mass restriction on Q.

`Challenge.lean` states this result and displays the operator realization,
coefficient inversion formula, PBW symbol and occupied-grade mass.
`Solution.lean` supplies the proof from the substantive local development.
`SubmissionAudit.lean` checks the selected root's axioms and model adapters.

The mathematical source is Idris Ali Shaik's manuscript *The rank-one Dixmier
conjecture for elements of mass at most six*, Theorem 1.1. Structural results
originate in the cited work of Guccione, Guccione and Valqui; the six structural
inputs consumed by this theorem are proved internally in the Lean development.
`SOURCE_MANIFEST.json` records the exact substantive source files and hashes.

The target environment is Lean 4.35.0-rc3 with a pinned matching canonical
Mathlib revision. The selected root and its model audits compile successfully;
all three axiom reports contain only propext, Classical.choice and Quot.sound.
The completed Lean 4.33.0 formalization and its evidence are preserved separately.
No Palomar registration or independent-kernel acceptance is claimed.

The extracted Lean code is licensed under MIT. Development and porting used
AI assistance; kernel checks do not constitute independent human review.

Reproduction targets:

```sh
lake build Challenge Solution SubmissionAudit
```

The release gate additionally requires exact Challenge/Solution comparison,
the current full Palomar Linux workflow, independent-kernel verification,
metadata validation and an exact-source handoff. Publication and live submission
are separate user-controlled stages.
