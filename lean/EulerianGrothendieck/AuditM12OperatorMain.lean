import UniformLanczos.Rate514Assembly
import UniformLanczos.Rate514ConcreteBridge
import UniformLanczos.Rate514ConcreteResidual
import UniformLanczos.Rate514AveragedKernel
import UniformLanczos.Rate514FrechetPath
import UniformLanczos.Rate514HybridResidual
import UniformLanczos.Rate514ActualOperatorCertificate
import UniformLanczos.Lemma512Propagation
import UniformLanczos.Lemma512Kernel
import UniformLanczos.Rate514Residual
import UniformLanczos.Rate514Constant
import UniformLanczos.Rate514HighamSpectral

/-!
# Manuscript 12, Theorem 5.14 — reproducible final operator-chain audit

This file must be rebuilt on the exact HEAD SHA of GitHub `main` by
`.github/workflows/m12-operator-main-final-audit.yml`.

Auditing the kernel with `#print axioms` establishes that Lean checked
*precisely the declarative theorem types* and found no `sorryAx`, custom
axioms or `native_decide`. It does NOT automatically establish that the
published functional-calculus assumptions or the original endpoint residual
estimates (163) are satisfied by the actual spectral operators. Those are
explicit fields of `PublishedJacobiInput`; such claims must not be inferred
from a green CI. The quantitative uniform conclusion only follows after
the analytical inputs are instantiated in that structure.

The finite-compression spectral kernel from merged Higham PR #538 is
audited here as well. Finite spectral positivity does not prove the
infinite-operator passage or the uniform off-diagonal Frechet bounds.
-/

#print UniformLanczos.Rate514ActualOperatorCertificate.PublishedJacobiInput

#print axioms UniformLanczos.Lemma512Propagation.duhamel_decay
#print axioms UniformLanczos.Lemma512Kernel.kernel_psd_of_limit
#print axioms UniformLanczos.Lemma512Kernel.kernel_symm_of_limit
#print axioms UniformLanczos.Rate514Residual.residual_a_bound
#print axioms UniformLanczos.Rate514Residual.residual_b_bound
#print axioms UniformLanczos.Rate514Residual.locality_bound
#print axioms UniformLanczos.Rate514Assembly.hybrid_tail
#print axioms UniformLanczos.Rate514Assembly.rate_assembly
#print axioms UniformLanczos.Rate514Assembly.theorem_5_14_conclusion
#print axioms UniformLanczos.Rate514ConcreteBridge.actualDifference_center
#print axioms UniformLanczos.Rate514ConcreteBridge.compact_uniform_rate_from_operator_certificates
#print axioms UniformLanczos.Rate514ConcreteResidual.residual_difference_actual
#print axioms UniformLanczos.Rate514ConcreteResidual.actualMu_lower
#print axioms UniformLanczos.Rate514AveragedKernel.averageKernel_matrix_certificate
#print axioms UniformLanczos.Rate514FrechetPath.jacobiPath_one
#print axioms UniformLanczos.Rate514FrechetPath.actual_entry_difference_of_frechet_derivative
#print axioms UniformLanczos.Rate514HybridResidual.actual_hybrid_residual_bound
#print axioms UniformLanczos.Rate514ActualOperatorCertificate.constructActualCertificate
#print axioms UniformLanczos.Rate514ActualOperatorCertificate.actual_rate_of_published_calculus
#print axioms UniformLanczos.Rate514ActualOperatorCertificate.compact_uniform_rate_of_published_calculus

#print axioms UniformLanczos.Rate514HighamSpectral.dividedDifference_nonneg
#print axioms UniformLanczos.Rate514HighamSpectral.spectralBondKernel_symmetric
#print axioms UniformLanczos.Rate514HighamSpectral.spectralBondKernel_psd
