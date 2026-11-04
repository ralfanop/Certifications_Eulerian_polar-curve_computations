import GegenbauerFock.CanonicalCFCGramTikhonovEigenmodes
import Mathlib.Topology.Algebra.Module.Basic

/-!
# V007 — exact positive Gram eigenmode Tikhonov strong limit

For every genuine strictly positive source Gram eigenvalue mu,
the actual bounded-operator Tikhonov filter converges in norm on
the corresponding eigenvector as eps tends to zero from above.
This is pointwise strong convergence on the actual eigenmodes;
extension to the whole Hilbert space will also require a uniform
bound and completeness/density.
-/

noncomputable section
open MeasureTheory Filter
namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Tikhonov filter converges strongly to the identity on every
actual strictly positive Gram eigenvector. -/
theorem sourceGramTikhonovFilter_eigenmode_tendsto
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℝ) (hmu : 0 < mu)
    (u : Lp ℂ 2 (Ultraspherical.measure lam))
    (hu : gram lam alpha hlam ha u = (mu : ℂ) • u) :
    Tendsto
      (fun eps : ℝ =>
        sourceGramTikhonovFilter lam alpha hlam ha eps u)
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds u) := by
  have hmu0 : mu ≠ 0 := ne_of_gt hmu
  have hc : ContinuousAt (fun eps : ℝ => mu / (mu + eps)) 0 := by
    apply ContinuousAt.div continuousAt_const
      (continuousAt_const.add continuousAt_id)
    change mu + (0 : ℝ) ≠ 0
    simpa using hmu0
  have hreal : Tendsto
      (fun eps : ℝ => mu / (mu + eps))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds (1 : ℝ)) := by
    simpa only [add_zero, div_self hmu0] using
      hc.tendsto.mono_left nhdsWithin_le_nhds
  have hcomplex : Tendsto
      (fun eps : ℝ => ((mu / (mu + eps) : ℝ) : ℂ))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds (1 : ℂ)) := by
    simpa only [Function.comp_def, Complex.ofReal_div, Complex.ofReal_add,
      Complex.ofReal_one] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
  have hvector : Tendsto
      (fun eps : ℝ => ((mu / (mu + eps) : ℝ) : ℂ) • u)
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds u) := by
    simpa using hcomplex.smul_const u
  have hevent : (fun eps : ℝ =>
      sourceGramTikhonovFilter lam alpha hlam ha eps u) =ᶠ[(nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))]
      (fun eps : ℝ => ((mu / (mu + eps) : ℝ) : ℂ) • u) := by
    filter_upwards [self_mem_nhdsWithin] with eps heps
    exact sourceGramTikhonovFilter_eigenmode
      lam alpha hlam ha eps heps mu hmu u hu
  exact hvector.congr' hevent.symm

#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGramTikhonovFilter_eigenmode_tendsto

end GegenbauerFock.GeneralUltrasphericalFock
