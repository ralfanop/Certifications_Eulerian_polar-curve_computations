import GegenbauerFock.UltrasphericalSturmLiouvilleRealFullResolventIdentity

/-!
# V007 — commutation of the true closed Gegenbauer Sturm resolvents

For every λ>0 and t,s>0, the actual all-L² closed Sturm
positive resolvents commute:

  R_t ∘ R_s = R_s ∘ R_t.

This is derived from the certified two-shift resolvent identity
in both orders, using scalar cancellation when the shifts differ.
It does not assume a spectral basis, symbolic functional calculus,
or diagonalization of finite polynomial sections.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- The two full weighted-L² positive resolvents for the same closed
Gegenbauer Sturm operator commute for all strictly positive shifts. -/
theorem sturmRealPositiveResolventFullCLM_comp_comm
    (lam t s : ℝ) (hlam : 0 < lam) (ht : 0 < t) (hs : 0 < s) :
    (sturmRealPositiveResolventFullCLM lam t hlam ht).comp
        (sturmRealPositiveResolventFullCLM lam s hlam hs) =
      (sturmRealPositiveResolventFullCLM lam s hlam hs).comp
        (sturmRealPositiveResolventFullCLM lam t hlam ht) := by
  let Rt := sturmRealPositiveResolventFullCLM lam t hlam ht
  let Rs := sturmRealPositiveResolventFullCLM lam s hlam hs
  by_cases hst : s = t
  · subst s
    rfl
  · have hforward : Rt - Rs = (s - t) • (Rt.comp Rs) := by
      apply ContinuousLinearMap.ext
      intro f
      change Rt f - Rs f = (s - t) • Rt (Rs f)
      exact sturmRealPositiveResolventFullCLM_difference
        lam t s hlam ht hs f
    have hreverse : Rs - Rt = (t - s) • (Rs.comp Rt) := by
      apply ContinuousLinearMap.ext
      intro f
      change Rs f - Rt f = (t - s) • Rs (Rt f)
      exact sturmRealPositiveResolventFullCLM_difference
        lam s t hlam hs ht f
    have hmain : (s - t) • (Rt.comp Rs) =
        (s - t) • (Rs.comp Rt) := by
      calc
        (s - t) • (Rt.comp Rs) = Rt - Rs := hforward.symm
        _ = -(Rs - Rt) := by abel
        _ = -((t - s) • (Rs.comp Rt)) := by rw [hreverse]
        _ = (s - t) • (Rs.comp Rt) := by
          rw [← neg_smul]
          congr 1
          ring
    have hnonzero : s - t ≠ 0 := sub_ne_zero.mpr hst
    have hcancel := congrArg
      (fun z : SturmH lam →L[ℝ] SturmH lam => (s - t)⁻¹ • z) hmain
    simpa only [smul_smul, inv_mul_cancel₀ hnonzero, one_smul]
      using hcancel

#print axioms GegenbauerFock.Ultraspherical.sturmRealPositiveResolventFullCLM_comp_comm

end GegenbauerFock.Ultraspherical
