# The rank-one Dixmier conjecture for elements of mass at most six

This Lean development proves that, over every characteristic-zero field K,
elements P,Q of the first Weyl algebra satisfying QP−PQ=1 generate the algebra
if P has at most six nonzero homogeneous components for deg X=1 and deg Y=−1.
There is no degree, order, support or mass bound on Q. The theorem includes
mass five; applying it to (Q,−P) gives the conclusion when Q has mass at most six.

`Challenge.lean` specifies the operator realization, PBW symbol and occupied-grade
mass. `Solution.lean` proves `Dixmier.Palomar.massSixGeneration`.
`SubmissionAudit.lean` checks its axioms and model adapters.

The mathematical source is Idris Ali Shaik's paper with the same title,
version 1.10.5, Theorem 1.1. Its Zenodo DOI is
[10.5281/zenodo.23161793](https://doi.org/10.5281/zenodo.23161793)
(reserved; publication pending). The structural interfaces drawn from
Guccione, Guccione and Valqui are proved internally. `SOURCE_MANIFEST.json`
records the substantive source modules and hashes. The paper's scalar
classification and pure-power face exclusion are supporting mathematics,
not additional selected declarations in this registry entry.

## Registered result

[PALOMAR-2026-10-05-000006, version 1](https://palomar-registry.org/entry?id=PALOMAR-2026-10-05-000006&version=1)
registers the immutable baseline identified in [SOURCE_PROVENANCE.md](SOURCE_PROVENANCE.md).
Its [official mechanical verification](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/37338549288)
passed exact Challenge/Solution comparison and acceptance by Lean, nanoda and
con-ron. The mechanical report has no errors or warnings. Its
[official Challenge rendering](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/37341477335)
also passed. The automated registry review records no warnings.

The selected theorem uses only `propext`, `Classical.choice` and `Quot.sound`;
its Solution has no `sorry` or unproved literature dependency. The Challenge
contains the intentional statement hole used by Comparator.

The build uses Lean 4.35.0-rc3 and Mathlib
`c55e6e786f49471c72fbddbec5415808896aec1e`. Reproduce it with:

```sh
lake build Challenge Solution SubmissionAudit
```

Registration applies to its exact source commit. A revised snapshot requires
its own verification and rendering before a new registry version.
Kernel verification and automated registry review do not establish literature
priority, independent human review or journal acceptance.

The code is MIT-licensed; the paper is CC BY 4.0. OpenAI Codex assisted with
development and packaging. See [SUBMISSION.md](SUBMISSION.md) for version routing.
