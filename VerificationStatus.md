# Verification status

The final theorems in `Main.lean` were elaborated and accepted by Lean 4.32.2.
`AxiomAudit.lean` was also compiled. Both final endpoints depend only on
`propext`, `Classical.choice`, and `Quot.sound`; there is no additional
irrationality hypothesis or assumed numerical inequality.

## Numerical certificates

All 215 generated numerical batches were elaborated successfully: 86 potential
batches, 86 field batches, and 43 cell-bound batches. The combined certificate
proves all 684 cell inequalities and their interval coverage. The build results
and axiom audit are recorded in `AppendixNumericalCertificate-build.json` and
`AppendixNumericalCertificate-audit.txt`.

## Source and artifact consistency

The delivered Lean sources and dependency pins are inventoried by
`scripts/project_audit.py`. Local modules are registered explicitly in
`lakefile.toml`; diagnostic scratch modules are excluded. The final build roots
are `Main` and `AxiomAudit`, with `Main` the default Lake target.

During development, local artifacts lived in `build432` and beside their source
files. The consistency audit uses that exact search order, after the pinned
external dependencies. Four source files had newer timestamps than their
selected artifacts and were re-elaborated before the final kernel replay:
`LogCertificates`, `AppendixNumericBase`, `AppendixNumericConstants`, and
`InnerPrimeCellBase`.

All **406 modules** in the complete local import closure of `Main` and
`AxiomAudit` passed the Lean 4.32.2 `leanchecker` utility, with every invocation
exiting successfully. Unlike importing an existing artifact, this rechecks each
module's stored declarations through the kernel against its currently selected
imports, including private proof terms. `KernelReplay-audit.json` records the
exact search path, selected artifacts, SHA-256 hashes of sources and all artifact
parts, and per-module results. Its final check confirmed that no selected source
or artifact changed during replay. This is Lean's own kernel replay, not an
independent implementation of the kernel.

`ArtifactConsistency-audit.json` records the final comparison of import-path
selection and every source/artifact hash against the frozen inputs in
`KernelReplay-inputs.json`. `SourceManifest.sha256` fingerprints the 411 delivered
Lean source files and the build configuration/scripts. Five auxiliary source
modules lie outside the final 406-module closure and are not included in the
claim of complete kernel replay.

## Standard Lake build

A separate normal Lake build successfully resolved and built the external
dependency closure and **42 local modules**, including shared foundations and
14 numerical potential batches. It was deliberately stopped before repeating
all previously checked numerical elaborations. The successful local results are
preserved in `StandardLake-checks.json`. A complete clean build of every local
module through normal Lake has **not** been claimed.

The ordinary Lake target graph resolves `Main` and `AxiomAudit` without missing
modules. `scripts/build.py` provides a reproducible build using only standard
Lake artifacts, with a bounded number of simultaneous local jobs. It neither
copies development artifacts into Lake nor manufactures build traces. Fresh
reproduction elaborates all source files again; compiled development artifacts
are not required or included in the source distribution.

The Lean toolchain is pinned to 4.32.2 and all 14 external packages are pinned to
Git commits in `lake-manifest.json`. No dependency update is needed to rebuild.
