import GegenbauerFock.CanonicalCFCGramTikhonovSharpErrorNorm
import GegenbauerFock.CanonicalCFCDeterministicNoiseEstimate
import Mathlib.Tactic.Abel

/-!
# V007 — exact Tikhonov reconstruction from genuine noisy Fock data

For the genuine Gegenbauer–Fock analysis map C, and source Gram
G=C* C, define R_eps=(G+eps I)^(-1) C*. This bounded operator maps
the actual complete Fock coefficient Hilbert space back to weighted L².

Prove that its noiseless reconstruction error is exactly -E_eps f,
where E_eps=eps(G+eps I)^(-1), and specialize the previously certified
generic deterministic bias-noise estimate to this *specific* operator.

The bound in this module has the actual reconstruction norm ‖R_eps‖.
The more quantitative factor 1/(2 sqrt(eps)) is a separate obligation,
not smuggled in as an assumption.
-/

noncomputable section
open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

private abbrev ReconstructH (lam : ℝ) := Lp ℂ 2 (Ultraspherical.measure lam)

/-- The actual bounded data-to-source regularized inverse, for
positive regularization parameter eps. -/
noncomputable def sourceGramTikhonovReconstructor
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (eps : ℝ) :
    InfiniteAnalysis.FockCoefficients →L[ℂ] ReconstructH lam :=
  (Ring.inverse (sourceGramPositiveShift lam alpha hlam ha eps)) ∘L
    C_adjoint lam alpha hlam ha

/-- Noiseless reconstruction has the exact true source-Gram bias
-E_eps f, as an identity of genuine weighted L² vectors. -/
theorem sourceGramTikhonovReconstructor_noiseless_bias
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (eps : ℝ) (heps : 0 < eps)
    (f : ReconstructH lam) :
    sourceGramTikhonovReconstructor lam alpha hlam ha eps
      (C lam alpha hlam ha f) - f =
      - (((eps : ℂ) •
        Ring.inverse (sourceGramPositiveShift lam alpha hlam ha eps)) f) := by
  let G := gram lam alpha hlam ha
  let A := sourceGramPositiveShift lam alpha hlam ha eps
  let B := Ring.inverse A
  have hinv : B * A = (1 : ReconstructH lam →L[ℂ] ReconstructH lam) :=
    (sourceGramPositiveShift_two_sided_inverse lam alpha hlam ha eps heps).2
  have hA : A = G + (eps : ℂ) •
      (1 : ReconstructH lam →L[ℂ] ReconstructH lam) := rfl
  have hBG :
      B * G + (eps : ℂ) • B =
        (1 : ReconstructH lam →L[ℂ] ReconstructH lam) := by
    calc
      B * G + (eps : ℂ) • B =
          B * (G + (eps : ℂ) •
            (1 : ReconstructH lam →L[ℂ] ReconstructH lam)) := by
              rw [mul_add, mul_smul_comm, mul_one]
      _ = B * A := by rw [hA]
      _ = 1 := hinv
  have hf := congrArg (fun T : ReconstructH lam →L[ℂ] ReconstructH lam => T f) hBG
  have hf' : B (G f) + (eps : ℂ) • B f = f := by
    simpa only [ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
      ContinuousLinearMap.mul_apply] using hf
  change B (G f) - f = -((eps : ℂ) • B f)
  calc
    B (G f) - f = B (G f) - (B (G f) + (eps : ℂ) • B f) := by rw [hf']
    _ = -((eps : ℂ) • B f) := by abel

/-- Actual deterministic Tikhonov reconstruction error on Fock
observations g=Cf+eta, with no spectral truncations or surrogate maps. -/
theorem sourceGramTikhonovReconstructor_noisy_bound
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (eps : ℝ) (heps : 0 < eps)
    (f : ReconstructH lam) (eta : InfiniteAnalysis.FockCoefficients) :
    ‖sourceGramTikhonovReconstructor lam alpha hlam ha eps
       (C lam alpha hlam ha f + eta) - f‖ ≤
      ‖(((eps : ℂ) •
          Ring.inverse (sourceGramPositiveShift lam alpha hlam ha eps)) f)‖ +
      ‖sourceGramTikhonovReconstructor lam alpha hlam ha eps‖ * ‖eta‖ := by
  have h := C_noisy_reconstruction_bound lam alpha hlam ha
    (sourceGramTikhonovReconstructor lam alpha hlam ha eps) f eta
  rw [sourceGramTikhonovReconstructor_noiseless_bias
    lam alpha hlam ha eps heps f] at h
  simpa only [norm_neg] using h

#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGramTikhonovReconstructor_noiseless_bias
#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGramTikhonovReconstructor_noisy_bound

end GegenbauerFock.GeneralUltrasphericalFock
