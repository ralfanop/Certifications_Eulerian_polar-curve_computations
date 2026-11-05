import GegenbauerFock.UltrasphericalSturmLiouvilleMonicHilbertSharpResolventNorm

/-!
# V007 — sharp norm for the product of two true closed Sturm resolvents

The product R_t ∘ R_s of the canonical positive-shift resolvents in
weighted real L² achieves the sharp product norm 1/(ts).
The upper estimate follows from submultiplicativity and the already
certified exact norm of each resolvent. The normalized degree-zero
Gegenbauer eigenvector attains equality for every pair t,s>0.
This is an exact all-Hilbert-space operator result, not a finite
polynomial-section calculation.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- The normalized constant Gegenbauer eigenmode is a simultaneous
eigenvector of the composition of any two positive closed Sturm
resolvents, with exact eigenvalue 1/(ts). -/
theorem sturmRealPositiveResolventFullCLM_comp_zero_mode
    (lam t s : ℝ) (hlam : 0 < lam) (ht : 0 < t) (hs : 0 < s) :
    (sturmRealPositiveResolventFullCLM lam t hlam ht).comp
      (sturmRealPositiveResolventFullCLM lam s hlam hs)
      (sturmMonicEigenCandidate_realL2_normalized lam hlam 0) =
      (t⁻¹ * s⁻¹) •
        sturmMonicEigenCandidate_realL2_normalized lam hlam 0 := by
  let Rt := sturmRealPositiveResolventFullCLM lam t hlam ht
  let Rs := sturmRealPositiveResolventFullCLM lam s hlam hs
  let u : SturmH lam :=
    sturmMonicEigenCandidate_realL2_normalized lam hlam 0
  have ht0 : Rt u = t⁻¹ • u :=
    sturmRealPositiveResolventFullCLM_zero_mode lam t hlam ht
  have hs0 : Rs u = s⁻¹ • u :=
    sturmRealPositiveResolventFullCLM_zero_mode lam s hlam hs
  change Rt (Rs u) = (t⁻¹ * s⁻¹) • u
  calc
    Rt (Rs u) = Rt (s⁻¹ • u) := by rw [hs0]
    _ = s⁻¹ • Rt u := by rw [map_smul]
    _ = s⁻¹ • (t⁻¹ • u) := by rw [ht0]
    _ = (t⁻¹ * s⁻¹) • u := by
      rw [smul_smul, mul_comm (s⁻¹) (t⁻¹)]

/-- The composition of two canonical closed Sturm resolvents has
the EXACT sharp operator norm t⁻¹s⁻¹ on the full weighted real L². -/
theorem sturmRealPositiveResolventFullCLM_comp_opNorm_eq
    (lam t s : ℝ) (hlam : 0 < lam) (ht : 0 < t) (hs : 0 < s) :
    ‖(sturmRealPositiveResolventFullCLM lam t hlam ht).comp
        (sturmRealPositiveResolventFullCLM lam s hlam hs)‖ =
      t⁻¹ * s⁻¹ := by
  let Rt := sturmRealPositiveResolventFullCLM lam t hlam ht
  let Rs := sturmRealPositiveResolventFullCLM lam s hlam hs
  let u : SturmH lam :=
    sturmMonicEigenCandidate_realL2_normalized lam hlam 0
  have hu : ‖u‖ = 1 :=
    sturmMonicEigenCandidate_realL2_normalized_norm lam hlam 0
  have hupper : ‖Rt.comp Rs‖ ≤ t⁻¹ * s⁻¹ := by
    calc
      ‖Rt.comp Rs‖ ≤ ‖Rt‖ * ‖Rs‖ :=
        ContinuousLinearMap.opNorm_comp_le Rt Rs
      _ = t⁻¹ * s⁻¹ := by
        rw [show ‖Rt‖ = t⁻¹ from
          sturmRealPositiveResolventFullCLM_opNorm_eq lam t hlam ht,
          show ‖Rs‖ = s⁻¹ from
          sturmRealPositiveResolventFullCLM_opNorm_eq lam s hlam hs]
  have heig : (Rt.comp Rs) u = (t⁻¹ * s⁻¹) • u :=
    sturmRealPositiveResolventFullCLM_comp_zero_mode lam t s hlam ht hs
  have hlower : t⁻¹ * s⁻¹ ≤ ‖Rt.comp Rs‖ := by
    have h := ContinuousLinearMap.le_opNorm (Rt.comp Rs) u
    rw [heig, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg
        (inv_nonneg.mpr ht.le) (inv_nonneg.mpr hs.le)),
      hu, mul_one, mul_one] at h
    exact h
  exact le_antisymm hupper hlower

#print axioms GegenbauerFock.Ultraspherical.sturmRealPositiveResolventFullCLM_comp_zero_mode
#print axioms GegenbauerFock.Ultraspherical.sturmRealPositiveResolventFullCLM_comp_opNorm_eq

end GegenbauerFock.Ultraspherical
