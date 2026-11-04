import GegenbauerFock.CanonicalCFCGramTikhonovNoisyReconstruction
import GegenbauerFock.CanonicalCFCGramTikhonovScalarEnergy
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# V007 — sharp noisy-data bound for the genuine Tikhonov reconstruction map

For the actual Gegenbauer-Fock transform C and source Gram G=C* C,
let R_eps=(G+eps I)^(-1) C*. The normal equation for u=R_eps eta
and the defining Hilbert adjoint identity imply the energy inequality

  eps * ‖u‖² + ‖C u‖² ≤ ‖eta‖ * ‖C u‖.

The already certified scalar complete-square bound yields
  ‖R_eps eta‖ ≤ ‖eta‖ / (2 sqrt eps),
and the sharp universal operator bound on Fock-to-source reconstruction.
All maps are the genuine bounded operators on complete Hilbert spaces.
-/

noncomputable section
open MeasureTheory
open scoped InnerProduct

namespace GegenbauerFock.GeneralUltrasphericalFock

private abbrev EnergyH (lam : ℝ) := Lp ℂ 2 (Ultraspherical.measure lam)

/-- The exact normal equation for the *actual* Fock-data regularizer. -/
theorem sourceGramTikhonovReconstructor_normal_equation
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (eps : ℝ) (heps : 0 < eps)
    (eta : InfiniteAnalysis.FockCoefficients) :
    gram lam alpha hlam ha
        (sourceGramTikhonovReconstructor lam alpha hlam ha eps eta) +
      (eps : ℂ) •
        (sourceGramTikhonovReconstructor lam alpha hlam ha eps eta) =
      C_adjoint lam alpha hlam ha eta := by
  let A := sourceGramPositiveShift lam alpha hlam ha eps
  let u := sourceGramTikhonovReconstructor lam alpha hlam ha eps eta
  have hu : u = (Ring.inverse A) (C_adjoint lam alpha hlam ha eta) := rfl
  have h := (sourceGramPositiveShift_two_sided_inverse
      lam alpha hlam ha eps heps).1
  have heval := congrArg (fun T : EnergyH lam →L[ℂ] EnergyH lam =>
    T (C_adjoint lam alpha hlam ha eta)) h
  change A ((Ring.inverse A) (C_adjoint lam alpha hlam ha eta)) =
    C_adjoint lam alpha hlam ha eta at heval
  rw [← hu] at heval
  change (gram lam alpha hlam ha +
      (eps : ℂ) • (1 : EnergyH lam →L[ℂ] EnergyH lam)) u =
    C_adjoint lam alpha hlam ha eta at heval
  simpa only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply] using heval

/-- Hilbert energy inequality for true Tikhonov reconstruction from
arbitrary Fock noise eta, with no spectral or finite-dimensional surrogate. -/
theorem sourceGramTikhonovReconstructor_energy_le
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (eps : ℝ) (heps : 0 < eps)
    (eta : InfiniteAnalysis.FockCoefficients) :
    eps * ‖sourceGramTikhonovReconstructor lam alpha hlam ha eps eta‖ ^ 2 +
      ‖C lam alpha hlam ha
        (sourceGramTikhonovReconstructor lam alpha hlam ha eps eta)‖ ^ 2 ≤
      ‖eta‖ * ‖C lam alpha hlam ha
        (sourceGramTikhonovReconstructor lam alpha hlam ha eps eta)‖ := by
  let u := sourceGramTikhonovReconstructor lam alpha hlam ha eps eta
  let T := C lam alpha hlam ha
  let G := gram lam alpha hlam ha
  have hnormal : G u + (eps : ℂ) • u = C_adjoint lam alpha hlam ha eta :=
    sourceGramTikhonovReconstructor_normal_equation
      lam alpha hlam ha eps heps eta
  have hgram : inner ℂ (G u) u = inner ℂ (T u) (T u) := by
    change inner ℂ ((C lam alpha hlam ha).adjoint
      (C lam alpha hlam ha u)) u =
      inner ℂ (C lam alpha hlam ha u) (C lam alpha hlam ha u)
    exact C_adjoint_pairing lam alpha hlam ha (C lam alpha hlam ha u) u
  have hg : (inner ℂ (G u) u).re = ‖T u‖ ^ 2 := by
    rw [hgram]
    exact inner_self_eq_norm_sq (T u)
  have he : (inner ℂ ((eps : ℂ) • u) u).re = eps * ‖u‖ ^ 2 := by
    rw [inner_smul_left]
    simp only [Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    rw [inner_self_eq_norm_sq]
  have hadj :
      inner ℂ (C_adjoint lam alpha hlam ha eta) u =
        inner ℂ eta (T u) :=
    C_adjoint_pairing lam alpha hlam ha eta u
  have hreal := congrArg Complex.re
    (congrArg (fun z : EnergyH lam => inner ℂ z u) hnormal)
  rw [hadj] at hreal
  have hsum :
      eps * ‖u‖ ^ 2 + ‖T u‖ ^ 2 =
        (inner ℂ eta (T u)).re := by
    rw [inner_add_left, Complex.add_re] at hreal
    rw [hg, he] at hreal
    linarith
  have hcs : (inner ℂ eta (T u)).re ≤ ‖eta‖ * ‖T u‖ :=
    (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
  change eps * ‖u‖ ^ 2 + ‖T u‖ ^ 2 ≤ ‖eta‖ * ‖T u‖
  exact hsum.le.trans hcs

/-- Actual Fock-to-source Tikhonov noise amplification has the
universal 1/(2 sqrt eps) bound without assuming an SVD. -/
theorem sourceGramTikhonovReconstructor_pointwise_noise_le
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (eps : ℝ) (heps : 0 < eps)
    (eta : InfiniteAnalysis.FockCoefficients) :
    ‖sourceGramTikhonovReconstructor lam alpha hlam ha eps eta‖ ≤
      ‖eta‖ / (2 * Real.sqrt eps) := by
  exact tikhonov_scalar_energy_noise_bound
    eps
    ‖sourceGramTikhonovReconstructor lam alpha hlam ha eps eta‖
    ‖C lam alpha hlam ha
        (sourceGramTikhonovReconstructor lam alpha hlam ha eps eta)‖
    ‖eta‖ heps (norm_nonneg _) (norm_nonneg _)
    (sourceGramTikhonovReconstructor_energy_le
      lam alpha hlam ha eps heps eta)

/-- Sharp universal noise-amplification bound for the genuine complex
bounded Fock-to-source operator R_eps. -/
theorem sourceGramTikhonovReconstructor_opNorm_le
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (eps : ℝ) (heps : 0 < eps) :
    ‖sourceGramTikhonovReconstructor lam alpha hlam ha eps‖ ≤
      1 / (2 * Real.sqrt eps) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro eta
  have h := sourceGramTikhonovReconstructor_pointwise_noise_le
    lam alpha hlam ha eps heps eta
  simpa only [div_eq_mul_inv, one_mul, mul_comm] using h

/-- Final deterministic data-space Tikhonov error estimate on genuine
full Fock data, including the 1/(2 sqrt eps) noise coefficient. -/
theorem sourceGramTikhonovReconstructor_noisy_bound_explicit
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (eps : ℝ) (heps : 0 < eps)
    (f : EnergyH lam) (eta : InfiniteAnalysis.FockCoefficients) :
    ‖sourceGramTikhonovReconstructor lam alpha hlam ha eps
       (C lam alpha hlam ha f + eta) - f‖ ≤
      ‖(((eps : ℂ) •
        Ring.inverse (sourceGramPositiveShift lam alpha hlam ha eps)) f)‖ +
      ‖eta‖ / (2 * Real.sqrt eps) := by
  have h := sourceGramTikhonovReconstructor_noisy_bound
    lam alpha hlam ha eps heps f eta
  have hn := sourceGramTikhonovReconstructor_opNorm_le
    lam alpha hlam ha eps heps
  have hmul := mul_le_mul_of_nonneg_right hn (norm_nonneg eta)
  calc
    ‖sourceGramTikhonovReconstructor lam alpha hlam ha eps
        (C lam alpha hlam ha f + eta) - f‖ ≤
        ‖(((eps : ℂ) •
          Ring.inverse (sourceGramPositiveShift lam alpha hlam ha eps)) f)‖ +
        ‖sourceGramTikhonovReconstructor lam alpha hlam ha eps‖ * ‖eta‖ := h
    _ ≤ ‖(((eps : ℂ) •
          Ring.inverse (sourceGramPositiveShift lam alpha hlam ha eps)) f)‖ +
        (1 / (2 * Real.sqrt eps)) * ‖eta‖ := add_le_add_left hmul _
    _ = ‖(((eps : ℂ) •
          Ring.inverse (sourceGramPositiveShift lam alpha hlam ha eps)) f)‖ +
        ‖eta‖ / (2 * Real.sqrt eps) := by ring

#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGramTikhonovReconstructor_normal_equation
#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGramTikhonovReconstructor_energy_le
#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGramTikhonovReconstructor_pointwise_noise_le
#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGramTikhonovReconstructor_opNorm_le
#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGramTikhonovReconstructor_noisy_bound_explicit

end GegenbauerFock.GeneralUltrasphericalFock
