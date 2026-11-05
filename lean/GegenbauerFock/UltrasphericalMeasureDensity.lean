import GegenbauerFock.UltrasphericalAffineJacobian

/-!
# V007: equality of the genuine ultraspherical measure and its affine density

The Beta law is transported as a measure, rather than inferred from the
moment sequence. The proof uses the already certified affine Jacobian
and the general set-lintegral change-of-variables lemma.

The transported density `affineDensity` has the previously verified
Beta/Gamma duplication factorization on (-1,1). A separate algebraic
simplification to the classical single-power density may follow.
-/

open MeasureTheory ProbabilityTheory

namespace GegenbauerFock.Ultraspherical

/-- The concrete pushforward of the symmetric Beta probability measure
is exactly the Lebesgue measure weighted by the actual transported
Beta density, including the Jacobian factor 1/2. -/
theorem measure_eq_withDensity_affine
    (lam : ℝ) (_hlam : 0 < lam) :
    measure lam =
      (volume : Measure ℝ).withDensity
        (fun u => ENNReal.ofReal (affineDensity lam u)) := by
  have hmeas : Measurable betaToInterval := by
    unfold betaToInterval
    fun_prop
  have hdenReal : Measurable
      (fun u : ℝ =>
        ProbabilityTheory.betaPDFReal (shape lam) (shape lam) ((u + 1) / 2)) :=
    (ProbabilityTheory.measurable_betaPDFReal (shape lam) (shape lam)).comp
      (by fun_prop)
  have hden : Measurable
      (fun u : ℝ =>
        ENNReal.ofReal
          (ProbabilityTheory.betaPDFReal (shape lam) (shape lam) ((u + 1) / 2))) :=
    hdenReal.ennreal_ofReal
  have htransport :
      measure lam =
        (Measure.map betaToInterval (volume : Measure ℝ)).withDensity
          (fun u =>
            ENNReal.ofReal
              (ProbabilityTheory.betaPDFReal (shape lam) (shape lam) ((u + 1) / 2))) := by
    unfold measure
    change
      Measure.map betaToInterval
        ((volume : Measure ℝ).withDensity
          (fun x => ENNReal.ofReal
            (ProbabilityTheory.betaPDFReal (shape lam) (shape lam) x))) =
      (Measure.map betaToInterval (volume : Measure ℝ)).withDensity
        (fun u => ENNReal.ofReal
          (ProbabilityTheory.betaPDFReal (shape lam) (shape lam) ((u + 1) / 2)))
    ext s hs
    rw [Measure.map_apply hmeas hs,
      withDensity_apply _ (hs.preimage hmeas),
      withDensity_apply _ hs,
      setLIntegral_map hs hden hmeas]
    refine setLIntegral_congr_fun_ae (hs.preimage hmeas) ?_
    filter_upwards [] with x hx
    change
      ENNReal.ofReal
        (ProbabilityTheory.betaPDFReal (shape lam) (shape lam) x) =
      ENNReal.ofReal
        (ProbabilityTheory.betaPDFReal (shape lam) (shape lam)
          ((betaToInterval x + 1) / 2))
    rw [show (betaToInterval x + 1) / 2 = x by
      unfold betaToInterval
      ring]
  calc
    measure lam =
        (Measure.map betaToInterval (volume : Measure ℝ)).withDensity
          (fun u =>
            ENNReal.ofReal
              (ProbabilityTheory.betaPDFReal (shape lam) (shape lam) ((u + 1) / 2))) :=
      htransport
    _ = (volume : Measure ℝ).withDensity
          (fun u => ENNReal.ofReal (affineDensity lam u)) := by
      rw [map_volume_betaToInterval, withDensity_smul_measure,
        ← withDensity_smul (ENNReal.ofReal (1 / 2 : ℝ)) hden]
      congr 1
      funext u
      change
        (ENNReal.ofReal (1 / 2 : ℝ)) •
          ENNReal.ofReal
            (ProbabilityTheory.betaPDFReal (shape lam) (shape lam) ((u + 1) / 2)) =
        ENNReal.ofReal (affineDensity lam u)
      rw [smul_eq_mul,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      unfold affineDensity
      congr 1
      ring

#print axioms GegenbauerFock.Ultraspherical.measure_eq_withDensity_affine

end GegenbauerFock.Ultraspherical
