# Dixmier mass six

This Isabelle/HOL development proves that, over every field of characteristic zero,
elements `P` and `Q` of the first Weyl algebra satisfying `QP - PQ = 1` generate
that algebra if `P` has at most six nonzero homogeneous components for
`deg X = 1` and `deg Y = -1`. Mass counts occupied grades, rather than PBW
monomials. Neither element has a degree bound, and `Q` has no mass bound.

The public theorem is `Dixmier_Mass_Six.mass_six_generation`. It directly uses
`Mass_Six_Generation_Proved.massSixGeneration`, whose hypotheses are the two
Weyl-carrier memberships, the commutator identity, and the mass bound on `P`.
The Newton and companion structural inputs used by its proof are proved inside
the development. This result does not settle the unrestricted rank-one
Dixmier conjecture.

Use **Isabelle2025-2**. From this entry directory, with `isabelle` on `PATH`,
build the entry with:

```sh
isabelle build -D . Dixmier_Mass_Six
```

Build the proof PDF and browser information with:

```sh
isabelle build -v -o browser_info \
  -o "document_variants=document:outline=/proof,/ML" -D .
```

The portable document builder uses LuaLaTeX and BibTeX when available, or
Tectonic otherwise. The document contains the introduction, bibliography,
and Isabelle-generated theory text. The outline variant hides proof and ML
bodies while retaining theorem statements.

The proof follows Idris Ali Shaik's
[The rank-one Dixmier conjecture for elements of mass at most six](https://zenodo.org/records/23161793),
version 1.10.6, Theorem 1.1, and its
[registered Lean formalization](https://palomar-registry.org/entry?id=PALOMAR-2026-10-05-000006&version=2),
Palomar version 2, source commit
`61783d52b6ae44cd2d8d20ad6cb798e7bbbce3ff`.
The literature sources include Guccione, Guccione and Valqui's
[shape of counterexamples](https://arxiv.org/abs/1111.6100v3) and
[homogeneous-component argument](https://arxiv.org/abs/2402.11135v1),
and [Han and Tan's Newton and one-sided-grade arguments](https://arxiv.org/abs/2210.00257v1).

The mathematical conception, manuscript, verification of the mathematical results, and part of the Lean 4 formalization were carried out by the author, with AI assistance as disclosed in the respective manuscript or code. OpenAI Codex generated a substantial portion of the Isabelle/HOL formalization while porting the existing Lean 4 development, including proof reconstruction, supporting lemmas, proof-script adaptation, and build troubleshooting. The resulting formal proofs were checked by Isabelle’s kernel.

`LICENSE` records the author-approved BSD 3-Clause license for this Isabelle
entry. `COPYING.source` preserves the MIT copyright and permission notice
from the pinned registered Lean source.
