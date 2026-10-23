#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")/.."
# Prerequisites: elan/Lean 4.24.0, lake update, lake exe cache get.
if [ -z "${V033_LEAN_BIN:-}" ]; then
 V033_LEAN_BIN="$(lake env which lean)"
 export LEAN_PATH="$PWD/lean:$(lake env printenv LEAN_PATH)"
else
 # Optional explicit runtime for an already prepared dependency cache.
 : "${LEAN_PATH:?Set LEAN_PATH with the package and pinned mathlib dependencies}"
fi
mkdir -p results
for module in V033Core V033Data V033MomentSpec; do
 "$V033_LEAN_BIN" -M 2048 -o "lean/$module.olean" "lean/$module.lean" > "results/$module.log" 2>&1
done
for n in $(seq 0 16); do
 for kind in Moment Degree; do
  module="V033${kind}${n}"
  "$V033_LEAN_BIN" -M 2048 -s 65536 -o "lean/$module.olean" "lean/$module.lean" > "results/$module.log" 2>&1
 done
done
for module in V033AsymptoticAlgebra V033EndpointAndLeading V033UniformIntegrals V033Verification; do
 "$V033_LEAN_BIN" -M 2048 -o "lean/$module.olean" "lean/$module.lean" > "results/$module.log" 2>&1
done
for module in V033GaussianAlgebra V033UniformSumMoments V033CumulantPolynomials \
 V033GaussianGram V033MomentExpansion V033MomentFunctional V033PolynomialJets \
 V033GramExpansion V033RationalRemainder V033GramBasis V033DeterminantAsymptotic \
 V033ProbabilityFunctional V033RecurrenceGram V033AllDegreeTheorem V033FullVerification; do
 "$V033_LEAN_BIN" -M 2048 -s 65536 -o "lean/$module.olean" "lean/$module.lean" > "results/$module.log" 2>&1
done
if rg 'sorryAx|Lean.ofReduceBool|error:' results/V033*.log; then exit 1; fi
python3 code/audit_kernel.py > results/kernel_audit_validation.log
echo "All modules compiled. Inspect results/V033Verification.log and results/V033FullVerification.log for the complete axiom audit."
