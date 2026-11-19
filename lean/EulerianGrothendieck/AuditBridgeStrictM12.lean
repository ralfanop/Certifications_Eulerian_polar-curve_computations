/-!
Fresh strict kernel-environment inventory for the retained Manuscript 12
Bridge library. The historical 821/849 counts are not used as assumptions.
Every public theorem in EulerianBridge is independently enumerated,
its declaration type and axiom set are recorded, and nonstandard axioms
fail this audit. This is an inventory, not a claim of semantic equality
to all 293 current manuscript equations.
-/
import Bridge

open Lean Elab Command
set_option maxHeartbeats 0
set_option pp.fullNames true
set_option pp.universes true

#eval show CommandElabM Unit from do
  let env ← getEnv
  let std : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count := 0
  let mut bad : Array (Name × Array Name) := #[]
  for (n, ci) in env.constants.toList do
    if (`EulerianBridge).isPrefixOf n then
      if let .thmInfo _ := ci then
        if !n.isInternal then
          count := count + 1
          let axs ← liftCoreM (Lean.collectAxioms n)
          let extra := axs.filter (fun a => !std.contains a)
          if extra.size > 0 then bad := bad.push (n, extra)
          logInfo m!"M12_BRIDGE_DECL {n}\nTYPE {ci.type}\nAXIOMS {axs}\nEND_DECL"
  logInfo m!"M12_BRIDGE_COUNT {count} BAD {bad.size}"
  for (n, extra) in bad do
    logError m!"M12_BRIDGE_NONSTANDARD {n}: {extra}"
  if count == 0 || bad.size > 0 then
    throwError "M12 Bridge audit failed"
  logInfo "M12_BRIDGE_AUDIT_SUCCESS"
