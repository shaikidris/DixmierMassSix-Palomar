# Dixmier mass-six Palomar release contract

## Selected mathematical surface

One selected theorem formalizes Manuscript Theorem 1.1: for every
characteristic-zero field K and P,Q in its first Weyl algebra, QP−PQ=1 and
at most six occupied homogeneous grades of P imply K⟨P,Q⟩=A₁(K).
The mate is unrestricted. The grading is deg X=1, deg Y=−1.

The selected declaration is `Dixmier.Palomar.massSixGeneration` in
Challenge and Solution. Solution consumes `Dixmier.Weyl.massSixGeneration`
through `DixmierFormal.Weyl.GGVDegreeBoundProved`. The Challenge exposes
the operator realization, PBW symbol, occupied-grade mass and generation
statement using trusted imports. Its intentional statement hole is checked
against the complete Solution by Comparator.

This surface does not advertise the unrestricted Dixmier conjecture, mass
seven, independent human review, novelty certification or journal acceptance.
Supporting scalar and geometric results are not separately selected theorems.

## Repository and dependency boundary

Mode: **EXTRACTION**. This repository contains the substantive proof cone
extracted from the completed local formalization. SOURCE_MANIFEST.json records
443 source-module entries and extraction hashes. There are 447 total local
Lean files, including Challenge, Solution and SubmissionAudit.

Ceilings: 450 proof/interface/audit modules, 65,000 local Lean lines, one
selected theorem, Challenge at most 300 lines and 32 KiB, and zero unreachable
local modules. The owner modules are the existing 443 substantive modules
and the three release interfaces. Adding proof architecture, a selected
theorem or an unreachable module requires a separate scope review.

Lean is pinned to v4.35.0-rc3. Mathlib and the exact verifier pins are listed
in SOURCE_PROVENANCE.md. Resolve dependency changes through Lake and repeat
both proof verification and rendering; never weaken the theorem to pass a port.
The original research formalization and mathematical manuscript are preserved.

## Candidate release gates

Before each submission, reconcile the complete YAML, README, Challenge,
Comparator and final manuscript. Check title, authors, ORCID, references,
classification, theorem scope, axioms, provenance and review status together.
Keep the exact submitted SHA out of self-referential tracked current-SHA claims.

Require a clean exact candidate, matching pushed SHA, metadata validation,
strict import-cone audit, selected-root build and axiom audits, exact preflight,
full Comparator/independent-kernel replay, and successful Challenge rendering.
For a new version, compare its statement and visible documentation with the
highest active public record and preserve any corrected metadata.

The registered baseline is PALOMAR-2026-10-05-000006 version 1. A later
candidate uses that registration target rather than creating a duplicate entry.
Publication and live registration require author authorization for the exact
candidate and review. Local preparation does not authorize those actions.

The extracted Lean code is MIT-licensed. The source paper is CC BY 4.0.
Attribution and AI assistance are recorded in formalization.yaml and README.
