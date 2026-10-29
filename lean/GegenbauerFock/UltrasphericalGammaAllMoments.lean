import GegenbauerFock.UltrasphericalGammaKummerComplete

/-!
# V007 — all Gamma-normalized ultraspherical moments

The Gamma-normalized density is the actual pushforward of the symmetric
Beta probability law. Its moments of every natural degree, including
degree zero, are determined without introducing an abstract moment
functional. Even degrees give the Pochhammer ratio and odd degrees
vanish. The unregularized Kummer integral is proved in the imported
module and is not replaced by a regularized hypergeometric function.

The parameter hypothesis here is `0 < lam`, as in the existing
Gamma-density and Beta-integration certificates; extending it to the
maximal integrable range `-1/2 < lam` is a separate obligation.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.Ultraspherical

/-- Every natural-degree moment of the actual Gamma-normalized
ultraspherical probability measure, with parity decided explicitly. -/
theorem gammaDensity_moment_all_degrees
    (lam : ℝ) (hlam : 0 < lam) (k : ℕ) :
    (∫ u : ℝ, u ^ k
      ∂((volume : Measure ℝ).withDensity
        (fun u => ENNReal.ofReal (gammaDensity lam u)))) =
      if k % 2 = 0 then KummerCoefficients.ratio lam (k / 2) else 0 := by
  by_cases hk : k % 2 = 0
  · simp only [if_pos hk]
    have he : k = 2 * (k / 2) := by omega
    conv_lhs => rw [he]
    exact gammaDensity_evenMoment_eq_ratio lam hlam (k / 2)
  · simp only [if_neg hk]
    have ho : k = 2 * (k / 2) + 1 := by omega
    conv_lhs => rw [ho]
    exact gammaDensity_oddMoment_eq_zero lam hlam (k / 2)

/-- The Gamma-normalized ultraspherical density integrates to one.
This is an equality of actual real Bochner integrals against the
density-weighted Lebesgue measure, not merely a formal normalization. -/
theorem gammaDensity_integral_one
    (lam : ℝ) (hlam : 0 < lam) :
    (∫ _u : ℝ, (1 : ℝ)
      ∂((volume : Measure ℝ).withDensity
        (fun u => ENNReal.ofReal (gammaDensity lam u)))) = 1 := by
  simpa only [pow_zero, KummerCoefficients.ratio_zero] using
    (gammaDensity_evenMoment_eq_ratio lam hlam 0)

/-- The Gamma-normalized ultraspherical density is strictly positive
at every point of its open support. -/
theorem gammaDensity_pos_of_mem_Ioo
    (lam u : ℝ) (hlam : 0 < lam)
    (hu : u ∈ Set.Ioo (-1 : ℝ) 1) :
    0 < gammaDensity lam u := by
  rw [← affineDensity_eq_gammaDensity lam u hlam]
  exact affineDensity_pos lam u hlam hu.1 hu.2

/-- The same density vanishes pointwise outside its open support,
including both endpoints. -/
theorem gammaDensity_eq_zero_of_not_mem_Ioo
    (lam u : ℝ) (hu : u ∉ Set.Ioo (-1 : ℝ) 1) :
    gammaDensity lam u = 0 := by
  unfold gammaDensity
  exact if_neg (by simpa only [Set.mem_Ioo] using hu)

#print axioms GegenbauerFock.Ultraspherical.gammaDensity_moment_all_degrees
#print axioms GegenbauerFock.Ultraspherical.gammaDensity_integral_one
#print axioms GegenbauerFock.Ultraspherical.gammaDensity_pos_of_mem_Ioo
#print axioms GegenbauerFock.Ultraspherical.gammaDensity_eq_zero_of_not_mem_Ioo

end GegenbauerFock.Ultraspherical
