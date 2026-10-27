import Classification
import Lean

#print axioms CN1.classNumber_eq_one_iff
#print axioms PMArchClassification.class_one_window

open Lean Elab Command in
run_cmd do
  for name in [``CN1.classNumber_eq_one_iff,
      ``PMArchClassification.class_one_discriminant_candidates,
      ``PMArchClassification.class_one_window,
      ``PMArchClassification.abs_discriminant_eq,
      ``PMArchClassification.actual_discriminant_window] do
    let deps ← Lean.collectAxioms name
    for dep in deps do
      unless dep == ``propext || dep == ``Classical.choice || dep == ``Quot.sound do
        throwError "Unapproved axiom {dep} in {name}"
  logInfo "Class-number axiom audit passed"
