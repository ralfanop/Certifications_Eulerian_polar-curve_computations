import EulerianGrothendieck
import EulerianGrothendieck.ExactPolynomialAllOrders
import UniformLanczos
/-! Strict M12 public theorem-type and transitive-axiom inventory.
The imports are supplied by the reproducible CI job; this only measures the
loaded declarations, not semantic equivalence with the manuscript. -/
open Lean Elab Command
set_option maxHeartbeats 0
set_option maxRecDepth 8192
set_option pp.fullNames true
set_option pp.universes true

#eval show CommandElabM Unit from do
  let env ← getEnv
  let std : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let prefixes : Array Name := #[`EulerianGrothendieck, `UniformLanczos]
  for p in prefixes do
    let mut count := 0
    let mut bad : Array (Name × Array Name) := #[]
    for (n, ci) in env.constants.toList do
      if p.isPrefixOf n then
        if let .thmInfo _ := ci then
          if !n.isInternal then
            count := count + 1
            let axs ← liftCoreM (Lean.collectAxioms n)
            let extra := axs.filter (fun a => !std.contains a)
            if extra.size > 0 then bad := bad.push (n, extra)
            logInfo m!"M12_LIBRARY_DECL {n}\nTYPE {ci.type}\nAXIOMS {axs}\nEND_DECL"
    logInfo m!"M12_LIBRARY_COUNT {p} {count} BAD {bad.size}"
    for (n, extra) in bad do
      logError m!"M12_LIBRARY_NONSTANDARD {n}: {extra}"
    if count == 0 || bad.size > 0 then
      throwError "M12 library audit failed"
  logInfo "M12_LIBRARY_AUDIT_SUCCESS"
