import GegenbauerFock.UltrasphericalSturmLiouvilleMonicDegree
import GegenbauerFock.UltrasphericalSturmLiouvilleRealPolynomialL2
import GegenbauerFock.UltrasphericalMeasureDensity
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

/-!
# V007 — nonvanishing of actual monic Gegenbauer vectors in weighted real L²

The ultraspherical probability measure is a density with respect to Lebesgue
measure, hence has zero mass on every singleton. Every nonzero real
polynomial has a finite set of roots. Consequently polynomial evaluation
into the genuine weighted real L² is injective, and every explicitly
constructed monic Gegenbauer eigenvector has strictly positive norm.

This provides the missing nonzero-norm input for normalizing the total
orthogonal family into a genuine Hilbert basis.
-/

noncomputable section

namespace GegenbauerFock.Ultraspherical

open MeasureTheory Polynomial

/-- The genuine ultraspherical probability law is atomless.
This uses the already-certified exact transported density formula. -/
theorem measure_nullSingletonClass
    (lam : ℝ) (hlam : 0 < lam) :
    NullSingletonClass (measure lam) := by
  rw [measure_eq_withDensity_affine lam hlam]
  infer_instance

/-- A nonzero real polynomial cannot represent the zero element in
the actual ultraspherical weighted real L² space. -/
theorem sturmRealPolynomialLp_ne_zero
    (lam : ℝ) (hlam : 0 < lam)
    (p : ℝ[X]) (hp : p ≠ 0) :
    sturmRealPolynomialLp lam hlam p ≠ 0 := by
  letI : IsProbabilityMeasure (measure lam) := probability lam hlam
  letI : NullSingletonClass (measure lam) :=
    measure_nullSingletonClass lam hlam
  intro hzero
  have heval := sturmRealPolynomialLp_ae_eval lam hlam p
  rw [hzero] at heval
  have hz : ∀ᵐ u ∂measure lam, p.eval u = 0 := by
    simpa using heval.symm
  have hfinite : {u : ℝ | p.eval u = 0}.Finite := by
    exact Polynomial.finite_setOf_isRoot hp
  have hn : ∀ᵐ u ∂measure lam, p.eval u ≠ 0 :=
    hfinite.countable.ae_notMem (measure lam)
  have hfalse : ∀ᵐ u ∂measure lam, False :=
    (hz.and hn).mono (fun _ h => h.2 h.1)
  obtain ⟨u, hu⟩ := hfalse.exists
  exact hu

/-- Every explicit monic Gegenbauer mode is nonzero in the
actual real Hilbert L², independently of spectral completeness. -/
theorem sturmMonicEigenCandidate_realL2_ne_zero
    (lam : ℝ) (hlam : 0 < lam) (n : ℕ) :
    sturmRealPolynomialLp lam hlam
      (sturmMonicEigenCandidate lam n) ≠ 0 := by
  exact sturmRealPolynomialLp_ne_zero lam hlam _
    (sturmMonicEigenCandidate_monic lam n).ne_zero

/-- Each monic Gegenbauer mode has a strictly positive weighted L² norm. -/
theorem sturmMonicEigenCandidate_realL2_norm_pos
    (lam : ℝ) (hlam : 0 < lam) (n : ℕ) :
    0 < ‖sturmRealPolynomialLp lam hlam
      (sturmMonicEigenCandidate lam n)‖ := by
  exact norm_pos_iff.mpr (sturmMonicEigenCandidate_realL2_ne_zero lam hlam n)

#print axioms GegenbauerFock.Ultraspherical.measure_nullSingletonClass
#print axioms GegenbauerFock.Ultraspherical.sturmRealPolynomialLp_ne_zero
#print axioms GegenbauerFock.Ultraspherical.sturmMonicEigenCandidate_realL2_ne_zero
#print axioms GegenbauerFock.Ultraspherical.sturmMonicEigenCandidate_realL2_norm_pos

end GegenbauerFock.Ultraspherical
