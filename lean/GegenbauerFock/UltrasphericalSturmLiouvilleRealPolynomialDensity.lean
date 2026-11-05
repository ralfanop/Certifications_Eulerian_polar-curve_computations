import GegenbauerFock.UltrasphericalSturmLiouvilleRealPolynomialLinear
import GegenbauerFock.UltrasphericalContinuousDensity
import Mathlib.Topology.ContinuousMap.Weierstrass

/-!
# V007 — genuine density of real polynomial vectors in ultraspherical L²

The real polynomial-image submodule of the concrete
Beta-pushforward L²(νλ;ℝ), already built and proved linear,
is dense by two genuine analytic inputs:

1. Bounded continuous real functions have dense image in
   L²(νλ;ℝ), using the certified probability law and weak regularity.
2. Classical polynomial Weierstrass approximation on [-1,1]
   controls the L² distance by the probability normalization.

No density condition is assumed; no complex-to-real identification
or hypothetical measure is used.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory
open scoped ENNReal

noncomputable def sturmRealBoundedContinuousToLp
    (lam : ℝ) (hlam : 0 < lam) :
    BoundedContinuousFunction ℝ ℝ →L[ℝ] Lp ℝ 2 (measure lam) := by
  letI : IsProbabilityMeasure (measure lam) := probability lam hlam
  exact BoundedContinuousFunction.toLp
    (2 : ℝ≥0∞) (measure lam) ℝ

theorem sturmRealBoundedContinuous_denseRange
    (lam : ℝ) (hlam : 0 < lam) :
    DenseRange (sturmRealBoundedContinuousToLp lam hlam) := by
  letI : IsProbabilityMeasure (measure lam) := probability lam hlam
  letI : Measure.WeaklyRegular (measure lam) :=
    measure_weaklyRegular lam hlam
  change DenseRange
    (BoundedContinuousFunction.toLp
      (2 : ℝ≥0∞) (measure lam) ℝ :
        BoundedContinuousFunction ℝ ℝ →L[ℝ] Lp ℝ 2 (measure lam))
  exact BoundedContinuousFunction.toLp_denseRange
    ℝ (measure lam) ℝ (by norm_num)

/-- Real Weierstrass approximation on the exact closed support of
the genuine ultraspherical probability law. -/
theorem sturmRealWeierstrass_unit_interval
    (f : BoundedContinuousFunction ℝ ℝ)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ P : Polynomial ℝ,
      ∀ u ∈ Set.Icc (-1 : ℝ) 1,
        |f u - P.eval u| < eps := by
  have hcontinuous :
      ContinuousOn (fun u : ℝ => f u) (Set.Icc (-1 : ℝ) 1) :=
    f.continuous.continuousOn
  obtain ⟨P, hP⟩ :=
    exists_polynomial_near_of_continuousOn (-1 : ℝ) 1
      (fun u => f u) hcontinuous eps heps
  refine ⟨P, ?_⟩
  intro u hu
  rw [abs_sub_comm]
  exact hP u hu

/-- Uniform real polynomial approximation controls the norm of the
difference in the ACTUAL weighted real L² probability space. -/
theorem sturmRealPolynomial_norm_sub_le
    (lam : ℝ) (hlam : 0 < lam)
    (f : BoundedContinuousFunction ℝ ℝ)
    (P : Polynomial ℝ)
    (eps : ℝ) (heps : 0 ≤ eps)
    (huniform : ∀ u ∈ Set.Icc (-1 : ℝ) 1,
       |f u - P.eval u| ≤ eps) :
    ‖sturmRealBoundedContinuousToLp lam hlam f -
      sturmRealPolynomialLp lam hlam P‖ ≤ eps := by
  letI : IsProbabilityMeasure (measure lam) := probability lam hlam
  have hcontinuous : Continuous (fun u : ℝ => f u - P.eval u) := by
    fun_prop
  have hb : ∀ᵐ u ∂measure lam, ‖f u - P.eval u‖ ≤ eps :=
    (ae_mem_unit_interval lam).mono (fun u hu => by
      simpa only [Real.norm_eq_abs] using huniform u hu)
  have hbound :
      eLpNorm (fun u : ℝ => f u - P.eval u)
        (2 : ℝ≥0∞) (measure lam) ≤ ENNReal.ofReal eps := by
    have h := eLpNorm_le_of_ae_bound
      (p := (2 : ℝ≥0∞)) hcontinuous.aestronglyMeasurable hb
    simpa [measure_univ lam hlam] using h
  have hf :
      ((sturmRealBoundedContinuousToLp lam hlam f :
        Lp ℝ 2 (measure lam)) : ℝ → ℝ)
          =ᵐ[measure lam] (f : ℝ → ℝ) := by
    change
      ((BoundedContinuousFunction.toLp
        (2 : ℝ≥0∞) (measure lam) ℝ f :
            Lp ℝ 2 (measure lam)) : ℝ → ℝ)
          =ᵐ[measure lam] (f : ℝ → ℝ)
    exact BoundedContinuousFunction.coeFn_toLp
      (2 : ℝ≥0∞) (measure lam) ℝ f
  have hdiff :
      ((sturmRealBoundedContinuousToLp lam hlam f -
        sturmRealPolynomialLp lam hlam P :
          Lp ℝ 2 (measure lam)) : ℝ → ℝ)
        =ᵐ[measure lam] (fun u => f u - P.eval u) := by
    filter_upwards
      [Lp.coeFn_sub
        (sturmRealBoundedContinuousToLp lam hlam f)
        (sturmRealPolynomialLp lam hlam P),
       hf, sturmRealPolynomialLp_ae_eval lam hlam P]
      with u hsub hfu hpoly
    simpa only [Pi.sub_apply, hfu, hpoly] using hsub
  rw [Lp.norm_def, eLpNorm_congr_ae hdiff]
  exact ENNReal.toReal_le_of_le_ofReal heps hbound

/-- The genuine real polynomial-image domain is dense in all
L²(νλ;ℝ), for every λ>0. No density assumption is passed. -/
theorem sturmRealPolynomialDomain_dense
    (lam : ℝ) (hlam : 0 < lam) :
    (sturmRealPolynomialDomain lam hlam).topologicalClosure = ⊤ := by
  let D := sturmRealPolynomialDomain lam hlam
  have hRange :
      Set.range (sturmRealBoundedContinuousToLp lam hlam) ⊆
        (D.topologicalClosure : Set (Lp ℝ 2 (measure lam))) := by
    rintro y ⟨f, rfl⟩
    change sturmRealBoundedContinuousToLp lam hlam f ∈
      closure (D : Set (Lp ℝ 2 (measure lam)))
    apply Metric.mem_closure_iff.mpr
    intro eps heps
    obtain ⟨P, hP⟩ :=
      sturmRealWeierstrass_unit_interval f (eps / 2) (half_pos heps)
    refine ⟨sturmRealPolynomialLp lam hlam P, ?_, ?_⟩
    · exact sturmRealPolynomialLp_mem_domain lam hlam P
    · rw [dist_eq_norm]
      have hnorm := sturmRealPolynomial_norm_sub_le
        lam hlam f P (eps / 2) (half_pos heps).le
          (fun u hu => (hP u hu).le)
      exact lt_of_le_of_lt hnorm (half_lt_self heps)
  have hDense :
      Set.univ ⊆
        (D.topologicalClosure : Set (Lp ℝ 2 (measure lam))) := by
    rw [← (sturmRealBoundedContinuous_denseRange lam hlam).closure_range]
    exact (Submodule.isClosed_topologicalClosure D).closure_subset_iff.mpr hRange
  exact Submodule.eq_top_iff'.mpr fun x => hDense (Set.mem_univ x)

#print axioms GegenbauerFock.Ultraspherical.sturmRealBoundedContinuous_denseRange
#print axioms GegenbauerFock.Ultraspherical.sturmRealWeierstrass_unit_interval
#print axioms GegenbauerFock.Ultraspherical.sturmRealPolynomial_norm_sub_le
#print axioms GegenbauerFock.Ultraspherical.sturmRealPolynomialDomain_dense

end GegenbauerFock.Ultraspherical
