# Palomar submission preparation

This branch prepares the substantive proof development for Palomar. Read this
file for the current port; the older audit files describe the Lean 4.32.2
snapshot and are retained as historical evidence, not verification of this port.

## Mathematical statement and scope

`Challenge.lean` states two unconditional results using only standard Mathlib
definitions: the real part of `riemannZeta 5` is irrational, and the real infinite
sum of reciprocal fifth powers is irrational. The zero-index summand is zero;
thus this is the usual series starting at one. The zeta function at five is real,
so the first statement represents the ordinary real zeta value.

`Solution.lean` imports the substantive development and proves matching
declarations from the two endpoints in `Main.lean`. It does not import Challenge.
The two deliberate `sorry` holes in Challenge are statement placeholders only.
Comparator must reject any such axiom in Solution's proof dependencies.

The source is Aabir Fauzan, *ζ(5) is irrational*, version 1, 17 September 2026,
[DOI 10.5281/zenodo.22826419](https://doi.org/10.5281/zenodo.22826419).
Credit for the original mathematical proof belongs to Fauzan. Formal Lean proof
credit belongs to Astra and Azriel Fasten. The AI contribution is disclosed in
`formalization.yaml`; Azriel Fasten is the human author and responsible maintainer.
The MIT license covers this repository's software, not the cited paper or the
separately licensed dependencies.

This is a claimed formalization of the source's irrationality conclusion, not an
independent claim to its discovery. The paper's quantitative irrationality measure
is excluded. `PROOF_GUIDE.md` maps the determinant construction, integrality,
positive moment representation, analytic decay, and prime normalization to Lean
modules. No independent human mathematical review has been established. Passing
the build and Comparator does not by itself establish source fidelity or replace
Palomar's editorial assessment.

### Research context

The claim concerns a specific odd zeta value. It is stronger than an assertion
that at least one member of a list is irrational: for example, Zudilin's
[*Arithmetic of linear forms involving odd zeta values*](https://arxiv.org/abs/math/0206176)
proves irrationality of at least one of ζ(5), ζ(7), ζ(9), and ζ(11), and discusses
the infinitely-many result. Those collective conclusions alone do not identify
ζ(5) as irrational. The present Challenge states that individual conclusion
directly, without a disjunction or unproved mathematical hypothesis. This
distinction is central to assessing the claimed advance in Fauzan's preprint.
The intended audience is researchers in Diophantine approximation and the
arithmetic of special values. This comparison is context, not a claim that the
preprint has received independent validation or that a literature-priority
review has been completed.

## Reproduce the submission checks

Use Linux with elan, Python 3.11 or later, and bubblewrap installed. The pinned
toolchain is Lean 4.35.0-rc2; Mathlib and its supporting libraries are pinned to
the exact compatible revisions. Solution-only dependencies remain pinned.

```sh
python3 scripts/project_audit.py --check --output project-inventory.json
python3 scripts/build.py --jobs 8 Tests.KernelCertificates Challenge Solution AxiomAudit
python3 scripts/verify_comparator.py
```

The Comparator script selects Palomar's required bundled
NanoDa and con-ron independent kernels. Its generated protected configuration is
temporary; the committed `comparator.json` contains only submitter fields.

## Submission coordinates

Repository: `realazthat/zeta5-lean2`. The Lean project is at the repository root;
the conventional files are `comparator.json` and `formalization.yaml`. Submit a
full, pushed 40-character commit SHA after all verification succeeds. The
preparation task does not itself register a result.

The human submission entry point is <https://submit.palomar-registry.org/>.
Agents should follow that host's `llms.txt` protocol instead of driving the form.
The responsible maintainer must supply an accurate authorization declaration.

## Verification status

- Structured metadata: passed Palomar's current metadata contract validator.
- Local import inventory: no missing imports; Challenge and Solution registered.
- Lean 4.35.0-rc2 build of `Tests.KernelCertificates`, `Challenge`, `Solution`,
  and `AxiomAudit`: passed (4,588 Lake jobs in the final build).
- Both submitted Solution statements and the principal intermediate results:
  only `propext`, `Classical.choice`, and `Quot.sound` in their axiom closures.
- Kernel-certificate regression: a true logarithmic bound accepted and a false
  bound rejected in kernel mode.
- Sandboxed Comparator: passed on 24 September 2026. con-ron accepted
  91,762 declarations; NanoDa and the default Lean kernel also accepted the
  Solution. Comparator completed with `Your solution is okay!` and exit code 0.

The local technical submission checks have passed. This is preparation for
submission, not a claim of registration or editorial acceptance. The complete
build and Comparator logs are in `verification/palomar/`; their fingerprints are
recorded in `verification/palomar/evidence.json`.

Two finite-sum proofs were rewritten to avoid NanoDa worker-stack overflow.
Their statements are unchanged. All checkers in the final run were the
unmodified binaries bundled with the pinned Lean toolchain.
