# Source and verification provenance

The authoritative formalization snapshot is the exact immutable commit supplied
to Palomar intake, equal to the clean local HEAD and pushed canonical remote
commit. This is a substantive repository containing the selected proof cone.
It is not a wrapper around an external proof source.

| Commit | Role |
| --- | --- |
| `b2601df23b5c26969595d8546d5b58b83de4f911` | Historical proof snapshot accepted by the full mechanical rehearsal linked in README; not the current submission commit. |
| `dd56d02cb7a58fa066c4a2c7fddec3cbb59ae8df` | Historical Mathlib dependency pin used by the verified proof snapshot. |
| `c55e6e786f49471c72fbddbec5415808896aec1e` | Replacement Mathlib dependency pin, matching the registered Gallai baseline. |
| `d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44` | PalomarSubmission verifier and workflow pin; not a project proof-source commit. |

`SOURCE_MANIFEST.json` contains 443 substantive module entries with SHA-256
file digests and extraction provenance. Its source-snapshot path records the
historical local extraction input; it is not an external build dependency.
The proof modules themselves are present in this repository. The selected
Challenge, Solution and comparator are unchanged
from the verified proof snapshot. The full Lake dependency manifest is deliberately
re-resolved for the replacement Mathlib revision and fully revalidated.

The paper source is version 1.10.5, Theorem 1.1, SHA-256
`85145159671e864be4dd8ae3c53220de3337f787141e5bc09a20408ff1561ce8`.
Its reserved DOI is `10.5281/zenodo.23161793`; publication is pending.
File and report SHA-256 digests are content identifiers, not Git commits.
