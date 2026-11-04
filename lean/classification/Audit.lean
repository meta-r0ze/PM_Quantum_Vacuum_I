import Classification
import Lean

#print axioms CN1.classNumber_eq_one_iff
#print axioms PMSubstrateClassification.class_one_window

open Lean Elab Command in
run_cmd do
  for name in [``CN1.classNumber_eq_one_iff,
      ``PMSubstrateClassification.class_one_discriminant_candidates,
      ``PMSubstrateClassification.class_one_window,
      ``PMSubstrateClassification.abs_discriminant_eq,
      ``PMSubstrateClassification.actual_discriminant_window] do
    let deps ← Lean.collectAxioms name
    for dep in deps do
      unless dep == ``propext || dep == ``Classical.choice || dep == ``Quot.sound do
        throwError "Unapproved axiom {dep} in {name}"
  logInfo "Class-number axiom audit passed"
