# Zeta(5) formalization

## Compact, readable proof branch

See [CODEGOLF.md](CODEGOLF.md) for measured source reduction and
[NUMERICAL_CERTIFICATES.md](NUMERICAL_CERTIFICATES.md) for the checked certificate
format. The verified baseline is preserved on `palomar-preparation`; this
branch has saved local build and three-kernel acceptance logs for commit
`53f1134`. See `PALOMAR.md` for their scope and evidence limitations.

## Palomar preparation

The Palomar port targets Lean **4.35.0-rc2**. See [PALOMAR.md](PALOMAR.md)
for the independent statements, reproducible checks, and current verification
status. Saved local logs record a full build and acceptance by con-ron,
NanoDa, and Lean's default kernel; they do not establish hosted CI success. The historical notes below concern the original Lean
4.32.2 snapshot; current port evidence is recorded separately in `PALOMAR.md`.

Original mathematical proof: **Aabir Fauzan**. Formal Lean proof: **Astra and
Azriel Fasten**. Azriel Fasten is the human author and responsible maintainer;
Astra's AI contribution is recorded in [formalization.yaml](formalization.yaml).
This repository is licensed under [MIT](LICENSE). The cited paper and software
dependencies retain their respective licenses.

## Original proof snapshot and historical verification

Lean formalization of Aabir Fauzan's preprint, version 1, 17 September 2026:
https://zenodo.org/records/22826419.

The final theorem is `Zeta5.irrational_zeta_five` in `Main.lean`; its statement is
`Irrational ((riemannZeta (5 : ℂ)).re)`. A second statement identifies the
convergent reciprocal-fifth-power series. Both final endpoints have compiled on
Lean 4.32.2, and their axiom audits list only `propext`, `Classical.choice`, and
`Quot.sound`. See `VerificationStatus.md` for the source, artifact, and kernel
checks performed, including the exact extent of the standard Lake rebuild.

## Historical rebuild instructions (Lean 4.32.2)

For this branch use the current instructions in [PALOMAR.md](PALOMAR.md).

The historical snapshot pinned Lean **4.32.2** in `lean-toolchain` and every dependency commit
in `lake-manifest.json`. The principal dependencies are:

| Dependency | Commit |
| --- | --- |
| PrimeNumberTheoremAnd | `a5154676af9aa3095150ee410cdda80555aa0642` |
| mathlib | `905b95818eb32af7874a58b427f50c1711a5e96c` |
| LeanCert | `6b11513512c9d27183fb4725bfc291ab38b4a6d7` |

After installing elan, the recommended build command is:

```sh
python3 scripts/build.py --jobs 2 Main AxiomAudit
```

The helper requires Python 3.11 or later. It checks the pins and local imports,
fetches the optional mathlib cache, builds shared external dependencies, and
checks local modules in dependency order with a bounded number of workers.
It writes ordinary Lake artifacts under `.lake/build` and per-module logs under
`.lake/build/verification-logs`. `--no-cache` skips the cache download; `--jobs`
controls simultaneous local-module builds. The committed manifest is used
without updating dependency versions.

The equivalent direct Lake entry point is `lake build`, whose default target
is `Main`. To fetch the mathlib cache manually for this pinned release:

```sh
MATHLIB_CACHE_GET_URL=https://lakecache.blob.core.windows.net/mathlib4 \
TAR_OPTIONS=--no-same-owner lake exe cache get
lake build
lake build AxiomAudit
```

After a build, the stored declarations of every local module can also be
replayed through Lean's kernel using its bundled `leanchecker` utility:

```sh
python3 scripts/kernel_audit.py --jobs 4 Main AxiomAudit
```

This records source and artifact hashes, actual import-path precedence, and one
kernel replay result for every local module in the final theorem's import closure.
All **406 modules** in the `Main` and `AxiomAudit` closure passed this replay;
the sources and selected artifacts remained unchanged throughout the check.

The build uses no `build432` directory, source-adjacent compiled files, or custom
`LEAN_PATH`. A source distribution needs the Lean files, project configuration,
manifest, and scripts; compiled artifacts and local dependency checkouts are
rebuildable.

## Verified numerical and arithmetic components

`AppendixNumericalCertificate.lean` has passed Lean's kernel for **all 684 cell
inequalities**, exact coverage of `[0,2]`, both field-minimum derivative signs,
and the energy constants. Its audit uses only `propext`, `Classical.choice`, and
`Quot.sound`. See `AppendixCertificateREADME.md`,
`AppendixNumericalCertificate-audit.txt`, and the 215-batch build record.
The Python numerical audit is an independent check; its results are not assumed
by any Lean theorem.

The small-prime branch includes the actual integer-valued binomial basis,
quotient and residue estimates, full functional pullback, determinant
normalization, and primes 2 and 3. `SmallPrimeAudit.lean` audits its analytic and
binomial prerequisites; the final branch is assembled in `SmallPrimeBound.lean`.
The PNT dependency and von Staudt–Clausen endpoint are independently audited in
`PNT-dependency-audit.txt`.

`PROOF_GUIDE.md` gives the mathematical module map.

## Source inventory

```sh
python3 scripts/project_audit.py --check --output project-inventory.json
```

This reports local imports, dependency commits, and available artifact versions.
When adding a source module, `--sync-lake` updates the generated module registry
in `lakefile.toml`. Missing imports are reported before a build starts.
