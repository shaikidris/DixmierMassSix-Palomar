# Source and verification provenance

This is a substantive repository containing the selected proof cone, not a
wrapper around an external proof source. The authoritative snapshot for each
registry version is the immutable source commit recorded by Palomar. A new
submission must use a clean local HEAD equal to the pushed canonical commit.

| Role | Repository | Commit |
| --- | --- | --- |
| Immutable source of PALOMAR-2026-10-05-000006 version 1; verified and rendered baseline, not the commit of a later revision | shaikidris/DixmierMassSix-Palomar | `61c0318729cc8539663a753c48be1b9a51b897ca` |
| Mathlib dependency pin | leanprover-community/mathlib4 | `c55e6e786f49471c72fbddbec5415808896aec1e` |
| Verifier and renderer pipeline pin; not a project proof-source commit | PalomarRegistry/PalomarSubmission | `d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44` |

`SOURCE_MANIFEST.json` contains 443 substantive module entries with SHA-256
file digests and extraction provenance. Its source-snapshot path identifies
the local extraction input; it is not an external build dependency.
The proof modules themselves are present in this repository.

The [version 1 public record](https://data.palomar-registry.org/entries/PALOMAR-2026-10-05-000006-v1.json)
binds the source to official verification run 37338549288 and the selected
declaration `Dixmier.Palomar.massSixGeneration`. The mechanical report SHA-256 is
`6ea8db30014231a83ec298e2c0d165bb3cb5880063ea4133ef8b73719b8e9cdb`.
Official renderer run 37341477335 passed for that same source. The registry
preserves the source and dependencies in PalomarArchive.

The mathematical paper is version 1.10.5, Theorem 1.1, SHA-256
`85145159671e864be4dd8ae3c53220de3337f787141e5bc09a20408ff1561ce8`.
Its reserved DOI is `10.5281/zenodo.23161793`; publication is pending.
File and report SHA-256 digests are content identifiers, not Git commits.
