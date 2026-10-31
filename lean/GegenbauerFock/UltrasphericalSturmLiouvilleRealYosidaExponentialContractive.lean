import GegenbauerFock.UltrasphericalSturmLiouvilleRealYosidaExponentialNorm
import GegenbauerFock.UltrasphericalSturmLiouvilleRealYosidaContraction
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# V007 — contractivity of the bounded Yosida semigroup (all nonnegative times)

Let R_t = (tI-A)⁻¹ on the genuine real weighted L², B_t = tR_t.
The previously certified resolvent estimate gives ‖B_t‖ ≤ 1.

For each s≥0, writing c=st, the bounded-generator exponential factorizes:
  exp(s A_t) = exp(-c I) * exp(c B_t)
             = exp(-c) * exp(c B_t).
The general Banach-algebra exponential norm estimate yields
‖exp(c B_t)‖ ≤ exp(c ‖B_t‖) ≤ exp(c), hence ‖exp(s A_t)‖ ≤ 1.

This proof never assumes an unbounded semigroup or eigenbasis.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- The genuine globally defined scaled resolvent is a contraction
in full weighted-L² operator norm. -/
theorem sturmRealYosidaScaledResolvent_opNorm_le
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    ‖t • sturmRealPositiveResolventFullCLM lam t hlam ht‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [one_mul, ContinuousLinearMap.smul_apply] using
    (sturmRealYosidaContraction_norm_le lam t hlam ht f)

/-- The bounded Yosida exponential contracts every vector of the
actual real ultraspherical weighted L² for all nonnegative times. -/
theorem sturmRealYosidaExponential_opNorm_le_one
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (s : ℝ) (hs : 0 ≤ s) :
    ‖sturmRealYosidaExponential lam t hlam ht s‖ ≤ 1 := by
  let R := sturmRealPositiveResolventFullCLM lam t hlam ht
  let B : SturmH lam →L[ℝ] SturmH lam := t • R
  let A := sturmRealYosidaGenerator lam t hlam ht
  let c : ℝ := s * t
  have hc : 0 ≤ c := mul_nonneg hs ht.le
  have hB : ‖B‖ ≤ 1 :=
    sturmRealYosidaScaledResolvent_opNorm_le lam t hlam ht
  have hCnorm : ‖c • B‖ ≤ c := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
    nlinarith [mul_le_mul_of_nonneg_left hB hc]
  have hfactor : s • A =
      (-c) • (1 : SturmH lam →L[ℝ] SturmH lam) + c • B := by
    change s • (t • (t • R - ContinuousLinearMap.id ℝ (SturmH lam))) =
      (-(s*t)) • ContinuousLinearMap.id ℝ (SturmH lam) +
        (s*t) • (t • R)
    rw [smul_smul, smul_sub]
    simp only [sub_eq_add_neg, smul_smul]
    abel
  have hcomm : Commute
      ((-c) • (1 : SturmH lam →L[ℝ] SturmH lam)) (c • B) := by
    change ((-c) • (1 : SturmH lam →L[ℝ] SturmH lam)) * (c • B) =
      (c • B) * ((-c) • (1 : SturmH lam →L[ℝ] SturmH lam))
    ext f
    simp [ContinuousLinearMap.mul_def, smul_smul, mul_comm]
  letI : NormedAlgebra ℚ (SturmH lam →L[ℝ] SturmH lam) :=
    .restrictScalars ℚ ℝ _
  have hscalar :
      NormedSpace.exp ((-c) • (1 : SturmH lam →L[ℝ] SturmH lam)) =
        Real.exp (-c) • (1 : SturmH lam →L[ℝ] SturmH lam) := by
    calc
      NormedSpace.exp ((-c) • (1 : SturmH lam →L[ℝ] SturmH lam)) =
        NormedSpace.exp
          (algebraMap ℝ (SturmH lam →L[ℝ] SturmH lam) (-c)) := by
            rw [Algebra.algebraMap_eq_smul_one]
      _ = algebraMap ℝ (SturmH lam →L[ℝ] SturmH lam)
          (NormedSpace.exp (-c : ℝ)) :=
            (NormedSpace.algebraMap_exp_comm (𝕂 := ℝ) (-c)).symm
      _ = Real.exp (-c) • (1 : SturmH lam →L[ℝ] SturmH lam) := by
          rw [← Real.exp_eq_exp_ℝ]
          exact Algebra.algebraMap_eq_smul_one _
  have hscalarNorm :
      ‖NormedSpace.exp ((-c) • (1 : SturmH lam →L[ℝ] SturmH lam))‖ ≤
        Real.exp (-c) := by
    rw [hscalar, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos (-c))]
    have hone :
        ‖(1 : SturmH lam →L[ℝ] SturmH lam)‖ ≤ 1 := by
      simpa only [ContinuousLinearMap.one_def] using
        (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := SturmH lam))
    nlinarith [mul_le_mul_of_nonneg_left hone (Real.exp_pos (-c)).le]
  have hBExp :
      ‖NormedSpace.exp (c • B)‖ ≤ Real.exp c :=
    (sturmRealOperatorExponential_norm_le_exp_norm lam (c • B)).trans
      ((Real.exp_le_exp).mpr hCnorm)
  have hmul : Real.exp (-c) * Real.exp c = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  change ‖NormedSpace.exp (s • A)‖ ≤ 1
  rw [hfactor, NormedSpace.exp_add_of_commute hcomm]
  calc
    ‖NormedSpace.exp ((-c) • (1 : SturmH lam →L[ℝ] SturmH lam)) *
        NormedSpace.exp (c • B)‖ ≤
      ‖NormedSpace.exp ((-c) • (1 : SturmH lam →L[ℝ] SturmH lam))‖ *
        ‖NormedSpace.exp (c • B)‖ := norm_mul_le _ _
    _ ≤ Real.exp (-c) * ‖NormedSpace.exp (c • B)‖ :=
      mul_le_mul_of_nonneg_right hscalarNorm (norm_nonneg _)
    _ ≤ Real.exp (-c) * Real.exp c :=
      mul_le_mul_of_nonneg_left hBExp (Real.exp_pos (-c)).le
    _ = 1 := hmul

/-- Pointwise contractivity of each bounded Yosida exponential
semigroup for every nonnegative time and every weighted-L² vector. -/
theorem sturmRealYosidaExponential_norm_le
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (s : ℝ) (hs : 0 ≤ s) (f : SturmH lam) :
    ‖sturmRealYosidaExponential lam t hlam ht s f‖ ≤ ‖f‖ := by
  calc
    ‖sturmRealYosidaExponential lam t hlam ht s f‖ ≤
        ‖sturmRealYosidaExponential lam t hlam ht s‖ * ‖f‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖f‖ := mul_le_mul_of_nonneg_right
      (sturmRealYosidaExponential_opNorm_le_one lam t hlam ht s hs)
      (norm_nonneg _)
    _ = ‖f‖ := one_mul _

/-- All bounded semigroup properties, packaged for the actual full
weighted-L² Yosida approximant: identity, exact additive-time law,
norm-continuity, and positive-time contraction. -/
theorem sturmRealYosidaExponential_contractingC0Semigroup
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    (sturmRealYosidaExponential lam t hlam ht 0 =
      (1 : SturmH lam →L[ℝ] SturmH lam)) ∧
    (∀ s u : ℝ,
      sturmRealYosidaExponential lam t hlam ht (s + u) =
        sturmRealYosidaExponential lam t hlam ht s *
          sturmRealYosidaExponential lam t hlam ht u) ∧
    Continuous (fun s : ℝ => sturmRealYosidaExponential lam t hlam ht s) ∧
    (∀ s : ℝ, 0 ≤ s →
      ‖sturmRealYosidaExponential lam t hlam ht s‖ ≤ 1) := by
  refine ⟨sturmRealYosidaExponential_zero lam t hlam ht, ?_, ?_, ?_⟩
  · intro s u
    exact sturmRealYosidaExponential_add lam t hlam ht s u
  · exact sturmRealYosidaExponential_continuous lam t hlam ht
  · intro s hs
    exact sturmRealYosidaExponential_opNorm_le_one lam t hlam ht s hs

#print axioms GegenbauerFock.Ultraspherical.sturmRealYosidaScaledResolvent_opNorm_le
#print axioms GegenbauerFock.Ultraspherical.sturmRealYosidaExponential_contractingC0Semigroup
#print axioms GegenbauerFock.Ultraspherical.sturmRealYosidaExponential_opNorm_le_one
#print axioms GegenbauerFock.Ultraspherical.sturmRealYosidaExponential_norm_le

end GegenbauerFock.Ultraspherical
