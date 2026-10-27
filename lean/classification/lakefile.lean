-- Integration configuration; upstream proof sources are unmodified.
import Lake
open Lake DSL
package ELEM where
  version := v!"0.1.0"
  leanOptions := #[⟨`autoImplicit, false⟩]
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "d13f23b723b8a846827a245b89c10fc7d3f11612"
lean_lib CN1 where
  globs := #[`CN1.Foundations.+, `CN1.Finite.+]
@[default_target]
lean_lib ELEM where
  globs := #[`ELEM.+]

@[default_target] lean_lib Classification where
