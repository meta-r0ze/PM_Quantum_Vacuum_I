# Notices

- **openai/math** (https://github.com/openai/math), Apache-2.0. The zero-free region Re s > 7/8 for Dirichlet L-functions
  (family 003, commit adc7f124) is a Lake dependency of `formalization/` and of `hcn/formalization/`. It is fetched at build
  time and is not vendored here. OpenAI's Lean-v4.34.1 compatibility patches for its dependencies are applied from openai/math's
  own `lean/patches/` directory by `formalization/scripts/apply_oai_patches.sh` (and its identical copy in
  `hcn/formalization/scripts/`); they are not copied here either.
- **The packages openai/math depends on**, at the revisions it pins (listed in `formalization/lake-manifest.json`, and in
  `hcn/formalization/lake-manifest.json`, which pins the same packages at the same revisions), each under its own license.
  Besides Mathlib's own dependencies Batteries and Aesop, two of them appear in the checked dependency closures of our theorems,
  the first proof's and the two of class number two: PrimeNumberTheoremAnd and RellichKondrachov.
- **Mathlib** (https://github.com/leanprover-community/mathlib4), Apache-2.0. It is the one direct dependency of
  `determinant/formalization/`, at revision `d13f23b` (the same revision openai/math pins), fetched at build time with its own
  dependencies at the revisions it pins (listed in `determinant/formalization/lake-manifest.json`).
- **Comparator** (https://github.com/leanprover/comparator), with its **lean4export**, and **nanoda**
  (https://github.com/ammkrn/nanoda_lib) were used to check the proofs. They are not included here.
- **Telperion** (`telperion/`), Business Source License 1.1; see `telperion/LICENSE`. Snapshot of development commit `5b8eea03`
  (2026-10-18).
- `determinant/formalization/CN1/` and `determinant/formalization/CN1Challenges/` are verbatim copies of files from
  `formalization/`; `determinant/formalization/ELEMNegControls/Tamper/` copies `formalization/CN1Challenges/Tamper/`.
- `hcn/formalization/CN1/` is a verbatim copy of `formalization/CN1/`. `hcn/certificates/data/` holds class numbers computed by
  PARI/GP (https://pari.math.u-bordeaux.fr) and by the C programs in that directory.
- The mathematical routes are credited in the README (Credits), in `determinant/README.md`, in `hcn/README.md` and in the three
  papers. The companion
  note that the determinant route formalizes is cited, not copied.
