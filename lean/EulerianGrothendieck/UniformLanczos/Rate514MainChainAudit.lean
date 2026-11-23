import UniformLanczos.Rate514AveragedKernel
import UniformLanczos.Rate514FrechetPath
import UniformLanczos.Rate514HybridResidual
import UniformLanczos.Rate514ActualOperatorCertificate
import UniformLanczos.Rate514HighamSpectral
import Mathlib

/-!
# M12 §5.8: exact-HEAD operator-chain compile and axiom audit

This audit checks all five integrated Lean modules, rebuilding from source
on the EXACT Git commit and auditing transitive axioms of named statements.

CRUCIAL SEMANTIC LIMIT: The constructActualCertificate theorem proves
the rate CONDITIONAL on a PublishedJacobiInput. Its fields
K_positive, K_decay, derivative, residual_actual, residual_profile,
locality and locality_summable are inputs, NOT proved for the literal
bilateral Jacobi operator. Rate514HighamSpectral.spectralBondKernel_psd
proves positivity of an explicitly defined finite-dimensional Gram kernel
conditional on abstract eigenvalues/eigenvectors in the interval; it
does not establish identity with the operator K in PublishedJacobiInput
or finite-compression-to-bilateral convergence. Neither is a gap in
Lean's kernel: these are unproved mathematical instantiation obligations.

DO NOT reinterpret this green audit as 'fully Lean formalized'.
-/

#print axioms UniformLanczos.Rate514AveragedKernel.averageKernel_symmetric
#print axioms UniformLanczos.Rate514AveragedKernel.averageKernel_quadratic_integral
#print axioms UniformLanczos.Rate514AveragedKernel.averageKernel_psd
#print axioms UniformLanczos.Rate514AveragedKernel.averageKernel_decay
#print axioms UniformLanczos.Rate514AveragedKernel.averageKernel_matrix_certificate

#print axioms UniformLanczos.Rate514FrechetPath.jacobiPath_zero
#print axioms UniformLanczos.Rate514FrechetPath.jacobiPath_one
#print axioms UniformLanczos.Rate514FrechetPath.actual_entry_difference_of_frechet_derivative

#print axioms UniformLanczos.Rate514HybridResidual.hybrid_on_window
#print axioms UniformLanczos.Rate514HybridResidual.actual_hybrid_residual_bound

#print axioms UniformLanczos.Rate514HighamSpectral.dividedDifference_nonneg
#print axioms UniformLanczos.Rate514HighamSpectral.spectralBondKernel_symmetric
#print axioms UniformLanczos.Rate514HighamSpectral.spectralBondKernel_psd

#print axioms UniformLanczos.Rate514ActualOperatorCertificate.constructActualCertificate
#print axioms UniformLanczos.Rate514ActualOperatorCertificate.actual_rate_of_published_calculus
#print axioms UniformLanczos.Rate514ActualOperatorCertificate.compact_uniform_rate_of_published_calculus
