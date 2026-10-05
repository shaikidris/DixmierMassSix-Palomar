# Full Palomar mechanical rehearsal

The manually dispatched GitHub workflow runs the pinned full Palomar verifier
on the caller repository at the exact dispatched commit. A prerequisite guard
validates clean source and pipeline snapshots, metadata, selected declarations,
request fields, and the workflow bindings. Its regression suite runs first.

The pipeline is PalomarSubmission d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44,
with mode full and execution profile palomar-standard-v1. The selected result
is Dixmier.Palomar.massSixGeneration. The Comparator path is comparator.json.

The local regression suite passes 15 checks. The supported Lean build passes;
normal Comparator and independent kernels await the Linux rehearsal. This
workflow is a mechanical rehearsal and performs no Palomar intake,
ownership proof, registration, or other registry-state operation.

The workflow requires a public source repository. Publication of this release
and dispatch of the completed batch require the owner's explicit approval.
Personal Git operations use the configured passwordless SSH route.

Local guard regression command:

```sh
python3 scripts/test_palomar_guard.py --pipeline ../palomar-tooling/PalomarSubmission-d4e41c1d --scratch-root /private/tmp
```

In GitHub Actions, supply a unique twelve-character lowercase alphanumeric
request identifier and the actual authorization relationship. The workflow
binds all replay inputs through the successful guard; branch names are not
substituted for the source commit. Preserve the complete mechanical report,
Comparator verdict and independent-kernel results before claiming success.
