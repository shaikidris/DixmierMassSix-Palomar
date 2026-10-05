# Six homogeneous components in the first Weyl algebra

This Lean development proves that, over every characteristic-zero field K,
elements P,Q of the first Weyl algebra satisfying QP−PQ=1 generate the algebra
if P has at most six nonzero homogeneous components for deg X=1 and deg Y=−1.
There is no degree, order, support or mass bound on Q.

`Challenge.lean` specifies the operator realization, PBW symbol and occupied-grade
mass. `Solution.lean` proves `Dixmier.Palomar.massSixGeneration`.
`SubmissionAudit.lean` checks its axioms and model adapters.

The source is Idris Ali Shaik's *The rank-one Dixmier conjecture for elements
of mass at most six*, version 1.10.5, Theorem 1.1. Its Zenodo DOI is
[10.5281/zenodo.23161793](https://doi.org/10.5281/zenodo.23161793)
(reserved; publication pending). The six structural interfaces drawn from
Guccione, Guccione and Valqui are proved internally. `SOURCE_MANIFEST.json`
records the substantive source modules and hashes.

## Verification

The [full mechanical rehearsal](https://github.com/shaikidris/DixmierMassSix-Palomar/actions/runs/37264857021)
passed for [proof commit b2601df](https://github.com/shaikidris/DixmierMassSix-Palomar/tree/b2601df23b5c26969595d8546d5b58b83de4f911).
It completed exact Challenge/Solution comparison and acceptance by Lean,
nanoda and con-ron. The selected theorem uses only `propext`, `Classical.choice`
and `Quot.sound`; it has no `sorry` or unproved literature dependency.
The mechanical report has no errors or warnings.

The replacement targets Lean 4.35.0-rc3 and Mathlib commit
`c55e6e786f49471c72fbddbec5415808896aec1e`, and verifier commit
`d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44`.
The report SHA-256 is
`61d51e1b39c35a56ca9d5a49f0eb68acd27e5c81919fa9b6517ba3b7336cea92`.
The cited report verifies the historical proof commit. Verification and rendering
of the replacement snapshot require their own reports. These checks establish
the selected formal theorem; they do not establish
literature priority or independent human review. Palomar registration is separate.

Reproduce the build with:

```sh
lake build Challenge Solution SubmissionAudit
```

The code is MIT-licensed; the paper is CC BY 4.0. OpenAI Codex assisted with
development and packaging. See [SUBMISSION.md](SUBMISSION.md) for the exact
manual registration fields and verification boundary.
