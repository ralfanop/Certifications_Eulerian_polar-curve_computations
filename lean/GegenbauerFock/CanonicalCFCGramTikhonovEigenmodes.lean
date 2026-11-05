import GegenbauerFock.CanonicalCFCGramTikhonovShift

/-!
# V007 — exact Tikhonov multipliers on actual positive Gram eigenmodes

The shifted inverse is a bounded operator on the genuine weighted L².
On every source Gram eigenvector it acts by (mu+eps)^{-1}, and
the Tikhonov filter G(G+eps I)^{-1} acts by mu/(mu+eps).
These are exact infinite-dimensional operator identities on genuine
nonzero source modes, not coefficientwise definitions of a surrogate.
-/

noncomputable section
open MeasureTheory Module End
namespace GegenbauerFock.GeneralUltrasphericalFock

private abbrev EigenH (lam : ℝ) := Lp ℂ 2 (Ultraspherical.measure lam)

/-- True positive-shift inverse on an eigenvector of the actual source Gram. -/
theorem sourceGramPositiveShift_inv_eigenmode
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (eps : ℝ) (heps : 0 < eps)
    (mu : ℝ) (hmu : 0 < mu)
    (u : EigenH lam)
    (hu : gram lam alpha hlam ha u = (mu : ℂ) • u) :
    (Ring.inverse (sourceGramPositiveShift lam alpha hlam ha eps)) u =
      (((mu + eps : ℝ) : ℂ)⁻¹) • u := by
  let A := sourceGramPositiveShift lam alpha hlam ha eps
  have hA : A u = ((mu + eps : ℝ) : ℂ) • u := by
    change ((gram lam alpha hlam ha) +
      (eps : ℂ) • (1 : EigenH lam →L[ℂ] EigenH lam)) u =
      ((mu + eps : ℝ) : ℂ) • u
    rw [ContinuousLinearMap.add_apply, hu]
    change (mu : ℂ) • u + (eps : ℂ) • u =
      ((mu + eps : ℝ) : ℂ) • u
    rw [← add_smul]
    norm_cast
  have hInvA : (Ring.inverse A) (A u) = u := by
    have heq := (sourceGramPositiveShift_two_sided_inverse
      lam alpha hlam ha eps heps).2
    have hx := congrArg (fun T : EigenH lam →L[ℂ] EigenH lam => T u) heq
    change (Ring.inverse A) (A u) = u at hx
    exact hx
  have hsc : ((mu + eps : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (add_pos hmu heps))
  have hscaled : ((mu + eps : ℝ) : ℂ) • ((Ring.inverse A) u) = u := by
    rw [hA, map_smul] at hInvA
    exact hInvA
  have hresult := congrArg
    (fun v : EigenH lam => (((mu + eps : ℝ) : ℂ)⁻¹) • v) hscaled
  simpa only [smul_smul, inv_mul_cancel₀ hsc, one_smul] using hresult

/-- Exact diagonal Tikhonov filter on a genuine Gram eigenmode:
mu/(mu+eps) tends to one as eps decreases to zero. -/
theorem sourceGramTikhonovFilter_eigenmode
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (eps : ℝ) (heps : 0 < eps)
    (mu : ℝ) (hmu : 0 < mu)
    (u : EigenH lam)
    (hu : gram lam alpha hlam ha u = (mu : ℂ) • u) :
    sourceGramTikhonovFilter lam alpha hlam ha eps u =
      ((mu / (mu + eps) : ℝ) : ℂ) • u := by
  have hinv := sourceGramPositiveShift_inv_eigenmode
    lam alpha hlam ha eps heps mu hmu u hu
  change (gram lam alpha hlam ha)
    ((Ring.inverse (sourceGramPositiveShift lam alpha hlam ha eps)) u) =
    ((mu / (mu + eps) : ℝ) : ℂ) • u
  rw [hinv, map_smul, hu, smul_smul]
  have hcoeff : (((mu + eps : ℝ) : ℂ)⁻¹) * (mu : ℂ) =
      ((mu / (mu + eps) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hcoeff]

#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGramPositiveShift_inv_eigenmode
#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGramTikhonovFilter_eigenmode
end GegenbauerFock.GeneralUltrasphericalFock
