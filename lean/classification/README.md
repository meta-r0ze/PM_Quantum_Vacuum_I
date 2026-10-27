# Imaginary-quadratic class-number-one classification

A Lean 4.34.1 project: the `ELEM` and `CN1` sources are vendored unmodified (see PROVENANCE.md);
`Classification.lean` is added here. The main PMArch project uses the same Lean version and depends
on this directory as the local Lake package `ELEM`.

`ELEM/Main.lean` proves `CN1.classNumber_eq_one_iff` for actual Mathlib number
fields and `NumberField.classNumber`. The theorem assumes a quadratic number
field containing a square root of a negative squarefree natural number. Its
proof imports the proved foundation, bound, nonvanishing, divisibility, and
finite sieve modules. It does not import challenge declarations or negative
controls.

`Classification.lean` derives the absolute discriminant candidates, proves their
identification with `NumberField.discr`, and proves that class number one plus
32 ≤ |disc K| ≤ 64 implies |disc K| = 43. The physical identification of a clock
period with this discriminant is not a number-theoretic theorem.

Build and audit:

```sh
lake exe cache get  # first setup
lake build
lake env lean Audit.lean
```

The audit rejects any transitive axiom other than Lean's standard `propext`,
`Classical.choice`, and `Quot.sound`. The first build includes a substantial
kernel-checked finite sieve and can take several minutes.

The full main-project `../check.sh` also runs this build and audit. With explicit
Lake executables, set `PM_ARCH_LAKE_BIN` for the main project and
`PM_ARCH_CLASSIFICATION_LAKE_BIN` for this project.

Vendored sources are unmodified. See `PROVENANCE.md`, `NOTICE.md`, and `LICENSE`.

## Local verification

On 2026-10-27, `lake build` completed successfully (8982 build jobs), and
`lake env lean Audit.lean` exited successfully. The class-number-one theorem
and all integration wrappers passed the standard-axiom allowlist check.
All 57 vendored Lean source files were compared with the pinned upstream
revision and are unmodified.
