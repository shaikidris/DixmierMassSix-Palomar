# Dixmier mass-six Palomar release contract

Date: 4 October 2026. Status: approved by the user on 4 October 2026; local preparation only.

## Selected mathematical surface

One registry entry will advertise the mass-six generation theorem: for every
characteristic-zero field K and P,Q in its first Weyl algebra, [Q,P]=1 and
at most six occupied homogeneous grades of P imply K⟨P,Q⟩=A₁(K).
The mate is unrestricted. The grading is deg X=1, deg Y=-1.

The checked Solution root is
`Dixmier.Weyl.massSixGeneration` in
`formal/DixmierFormal/Weyl/GGVDegreeBoundProved.lean`.
The Challenge declaration is proposed as `Dixmier.Palomar.massSixGeneration`.
The statement will expose the algebra/model, exact commutator, occupied-grade
mass and generation definitions on the trusted statement surface. It must not
import project proof modules or hide these objects behind unspecified values.
Challenge/Solution identity and the abstract/operator model adapter must be
checked explicitly. No GGV-input assumption may appear in the exported theorem.

This entry does not advertise the unrestricted Dixmier conjecture, mass seven,
a novelty certification, independent human review or journal acceptance.
Appendix and supporting results are retained only when required by the selected
root; they are not separately selected registry declarations.

## Repository mode and source boundary

Mode: **EXTRACTION**. The authoritative completed proof laboratory is
`/Users/shaik.i/research/dixmier/formal/`. Its final checked source hashes and
completion receipt are in `formal/evidence/2026-10-04-final-audit/`.
It currently has no authoritative Git commit recorded by this contract.

Prospective release path: `/Users/shaik.i/research/dixmier/palomar-mass-six/`.
It will contain a substantive copied proof cone, not a thin wrapper.
The completed Lean 4.33.0 source and frozen manuscript stay unchanged.
The extracted tree receives a separate compatibility port and provenance record.
GitHub creation, public visibility, pushes and live submission are separate
authorization stages; none is approved by this contract.

## Baseline and ceilings

The read-only import audit found 443 modules reachable from the selected
Solution root, containing 61,811 physical lines; the largest file has 2,113
lines. None currently has a `module` header. These are import-cone counts,
not a claim that every declaration in every module is necessary.

Proposed ceilings: 450 proof/interface/audit modules, 65,000 local Lean lines,
one selected theorem, Challenge at most 300 lines and 32 KiB, and zero
unreachable local modules. The initial owner modules are the existing 443
reachable modules; preserve their boundaries for the compatibility port.
Additional owners are Challenge, Solution and a scoped SubmissionAudit.
Any ceiling breach or additional proof architecture requires replanning.

## Tasks and exit gates

| Task | Owner | Selected-root obligation | Exit gate |
|---|---|---|---|
| Freeze semantic surface | Challenge/Solution | Exact algebra, grading, commutator and generation statement | Human-readable definitions, scope and substitution audit |
| Extract strict cone | Existing reachable source modules | Supply only the checked root's dependencies | Recorded file/hash manifest; zero unreachable modules |
| Compatibility port | Existing owner modules and Lake metadata | Supported toolchain and module visibility | Full selected-root build; unchanged mathematical scope |
| Compare statements | Comparator/SubmissionAudit | Challenge and Solution elaborated identity | Comparator exit zero and standard-only axiom reports |
| Validate metadata | Release metadata/guard | Author, provenance, licence and exact source binding | Pinned parser and strict metadata validator pass |
| Linux replay | Pinned full Palomar workflow | Independent-kernel release evidence | Complete mechanical report, Comparator and required kernel pass |
| Handoff | Submission packet | Exact reviewable public snapshot | User approval for publication; manual live-state actions |

Live policy refreshed today specifies minimum Lean `v4.35.0-rc2`, matching
canonical Mathlib toolchain, module headers and visibility, Challenge size limits,
and independent verification. The exact compatible Mathlib pin and verifier
commit will be resolved and recorded before porting or expensive replay.
No theorem may be weakened to make the port pass.

## Licence and publication

No release licence was found in the source inventory. MIT is proposed for the
user-authored extracted Lean code, subject to explicit approval and a provenance
audit of copied third-party material. Existing attribution must be preserved.
No public repository or live submission is created by the preparation audit.

Live Palomar actions are handoff-only in this environment: the user performs
submission, ownership proof, verification request and registration. Preparation
and public rehearsals are not official registry verification or registration.

## Current exit condition

Approve the selected theorem, separate extraction/compatibility-port scope,
size ceilings and licence before admitting proof modules to the release tree.
The completed research formalization remains the authority throughout.
