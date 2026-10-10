# The rank-one Dixmier conjecture for elements of mass at most six

These Lean 4 and Isabelle/HOL developments prove that, over every
characteristic-zero field K, elements P,Q of the first Weyl algebra satisfying
QP−PQ=1 generate the algebra if P has at most six nonzero homogeneous
components for deg X=1 and deg Y=−1. Mass counts occupied grades, not PBW
monomials. There is no degree or order bound on either element and no mass
bound on Q. Applying the theorem to (Q,−P) gives the symmetric conclusion.

The mathematical source is Idris Ali Shaik's
[paper with the same title](https://doi.org/10.5281/zenodo.23161793),
version 1.10.6, Theorem 1.1. The structural interfaces drawn from Guccione,
Guccione and Valqui are proved internally in both developments.

## Lean 4

`Challenge.lean` specifies the operator realization, PBW symbol and occupied-grade
mass. `Solution.lean` proves `Dixmier.Palomar.massSixGeneration`.
`SubmissionAudit.lean` checks its axioms and model adapters.
`SOURCE_MANIFEST.json` records the substantive source modules and hashes.

[PALOMAR-2026-10-05-000006, version 2](https://palomar-registry.org/entry?id=PALOMAR-2026-10-05-000006&version=2)
registers source commit `61783d52b6ae44cd2d8d20ad6cb798e7bbbce3ff`.
Its [official mechanical verification](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/37353942411)
passed Challenge/Solution comparison and checks by Lean, nanoda and con-ron.
Registration applies to that immutable source commit.

The selected theorem uses only `propext`, `Classical.choice` and `Quot.sound`;
its Solution has no `sorry` or unproved literature dependency. The Challenge
contains the intentional statement hole used by Comparator.

Use Lean 4.35.0-rc3 and Mathlib
`c55e6e786f49471c72fbddbec5415808896aec1e`:

```sh
lake build Challenge Solution SubmissionAudit
```

## Isabelle/HOL

The [Isabelle entry](isabelle/Dixmier_Mass_Six/README.md) contains 457 theories
and proves `Dixmier_Mass_Six.mass_six_generation`. Use Isabelle2025-2:

```sh
isabelle build -o document=false -D isabelle/Dixmier_Mass_Six Dixmier_Mass_Six
```

The entry includes document sources and a portable document builder.
Its public theorem checks that its recursive proof dependencies contain no
oracles and that it has no ambient hypotheses. The
[source manifest](isabelle/source-manifest.json) and
[validation record](isabelle/verification.json) identify the published files
and the checked AFP submission package. AFP editorial review is pending;
publication here does not imply AFP acceptance.

## Licensing and attribution

The Lean code is MIT-licensed. The Isabelle entry is BSD-3-Clause and preserves
the Lean source's MIT notice in `COPYING.source`. The paper is CC BY 4.0.
OpenAI Codex assisted with development and packaging; the Isabelle entry's
README gives the formalization-specific disclosure.
