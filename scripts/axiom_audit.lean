/-! Appended after legacy imports of every project module by check_axioms.py.
Select by defining module, not declaration namespace: private helpers, generated
declarations and declarations in other namespaces must also be checked. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let moduleName := moduleNames[idx.toNat]!
    if (`FreeProbability).isPrefixOf moduleName || (`Verification).isPrefixOf moduleName then
      count := count + 1
      for ax in ← collectAxioms name do
        unless allowed.contains ax do
          throwError "Forbidden axiom {ax} in {name} (module {moduleName})"
  unless count > 0 do
    throwError "No project declarations were audited"
  logInfo m!"Axiom audit passed for {count} project declarations. Allowed: propext, Classical.choice, Quot.sound."
