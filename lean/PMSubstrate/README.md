# PMSubstrate — Paper I substrate

Lean 4 proofs for *Persistence Mechanics of the Quantum Vacuum I: The E8 Substrate and the
Fine-Structure Constant*.

- What is checked: [OVERVIEW.md](OVERVIEW.md) — main theorem, postulates, six terms, module map.
- What remains: [REVIEW-AND-NEXT.md](REVIEW-AND-NEXT.md) — the missing physical implications.

Build: Lean 4.34.1, with sibling `PM/lean` and the vendored `classification/` package.

```sh
lake exe cache get
./check.sh
```

`check.sh` builds the library, runs the strict axiom audit, the readable audit, and the
class-number audit.
