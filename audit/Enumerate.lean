import SharpCut
import Lean

/- Enumerate the actual imported project environment, including definitions. -/
run_cmd do
  let env ← Lean.getEnv
  let names := env.constants.toList.map Prod.fst |>.filter ((`SharpCut).isPrefixOf ·)
  let names := names.mergeSort (fun a b => a.toString < b.toString)
  for name in names do
    Lean.logInfo m!"SHARPCUT_DECL {name}"
    let some info := env.find? name | throwError "Missing declaration: {name}"
    let some idx := env.getModuleIdxFor? name | throwError "Missing source module: {name}"
    let mod := env.header.moduleNames[idx]!
    let kind := match info with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "definition"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
      | .axiomInfo _ => "axiom"
      | .opaqueInfo _ => "opaque"
      | .quotInfo _ => "quotient"
    Lean.logInfo m!"SHARPCUT_SOURCE {name} {mod} {kind}"
  let legacy := env.constants.toList.map Prod.fst |>.filter ((`Khachiyan).isPrefixOf ·)
  for name in legacy.mergeSort (fun a b => a.toString < b.toString) do
    Lean.logInfo m!"LEGACY_DECL {name}"
  for mod in env.header.moduleNames do
    if (`SharpCut).isPrefixOf mod then
      Lean.logInfo m!"SHARPCUT_MODULE {mod}"
    if (`Khachiyan).isPrefixOf mod then
      Lean.logInfo m!"LEGACY_MODULE {mod}"
  let mut pending := names ++ legacy
  let mut visited : Lean.NameSet := {}
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail
    if visited.contains name then continue
    visited := visited.insert name
    let some info := env.find? name
      | throwError "Missing dependency: {name}"
    if (`SharpCut).isPrefixOf name || (`Khachiyan).isPrefixOf name then
      let some idx := env.getModuleIdxFor? name
        | throwError "Missing source module: {name}"
      let mod := env.header.moduleNames[idx]!
      unless (`SharpCut).isPrefixOf mod || (`Khachiyan).isPrefixOf mod do
        throwError "Unexpected project dependency module: {name} in {mod}"
    for dep in info.getUsedConstantsAsSet.toArray do
      pending := dep :: pending
  Lean.logInfo "SHARPCUT_CLOSURE_PASS"
