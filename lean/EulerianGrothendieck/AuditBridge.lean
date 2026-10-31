import Bridge
open Lean Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut nThm := 0
  let mut bad : Array (Name × Array Name) := #[]
  let std : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for (n, ci) in env.constants.toList do
    if (`EulerianBridge).isPrefixOf n then
      if let .thmInfo _ := ci then
        if !n.isInternal then
          nThm := nThm + 1
          let axs ← liftCoreM (Lean.collectAxioms n)
          let extra := axs.filter (fun a => !std.contains a)
          if extra.size > 0 then bad := bad.push (n, extra)
  logInfo m!"theorems: {nThm}; with non-standard axioms: {bad.size}"
  for (n, a) in bad do
    logInfo m!"{n}: {a}"
