import PMArch.OrthogonalExchange
import Lean

-- Audit all declarations from the new module, including generated helpers,
-- and their transitive axiom dependencies. Earlier modules retain their full
-- project audit; this check does not merely grep for `sorry`.
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    let fromModule := match env.getModuleIdxFor? name with
      | some idx => env.allImportedModuleNames[idx.toNat]! == `PMArch.OrthogonalExchange
      | none => false
    if fromModule || (`PMArch.OrthogonalExchange).isPrefixOf name then
      let deps ← Lean.collectAxioms name
      for dep in deps do
        unless dep == ``propext || dep == ``Classical.choice || dep == ``Quot.sound do
          throwError "Unapproved axiom {dep} in {name}"
      checked := checked + 1
  if checked == 0 then throwError "No orthogonal exchange declarations found"
  logInfo m!"Orthogonal exchange strict axiom audit passed: {checked} declarations"
