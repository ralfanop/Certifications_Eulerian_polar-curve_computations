import GegenbauerFock.PhyslibTraceClassCoisometricClosedRanges
import GegenbauerFock.PhyslibTraceClassCoisometricUniqueness

/-!
# V007 — quantitative stability of the canonical coisometric S₁ coordinates

The certified splitting T=E(R T)+Q T, with E(X)=U† X U and
R(T)=U T U†, is topological, but its coordinate maps also have
quantitative trace-norm stability.

Assuming the coisometry U satisfies U U† = 1 and ‖U‖ ≤ 1,
the true CFC Schatten-S₁ coordinate bounds are

  ‖R(T)-R(V)‖₁ ≤ ‖T-V‖₁,
  ‖P(T)-P(V)‖₁ ≤ ‖T-V‖₁,
  ‖Q(T)-Q(V)‖₁ ≤ 2‖T-V‖₁.

Thus *any* exact decompositions T=E(X)+Y, V=E(X')+Y'
with R(Y)=R(Y')=0 have 1- and 2-Lipschitz respective
coordinates. No positivity, finite rank or singular-value model.
-/

noncomputable section
namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The coisometric retraction is a contraction on the genuine
CFC trace-normed Schatten S₁ space, with no surjectivity claim
for the companion embedding. -/
theorem coisometric_retraction_norm_le_one_v007
    (U : H →L[ℂ] H) (hUnorm : ‖U‖ ≤ (1 : ℝ)) :
    ‖sandwichContinuous U U.adjoint‖ ≤ 1 := by
  have hAdj : ‖U.adjoint‖ = ‖U‖ := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact norm_star U
  have hsq : ‖U‖ ^ 2 ≤ (1 : ℝ) := by
    simpa only [one_pow] using
      ((sq_le_sq₀ (norm_nonneg _) zero_le_one).2 hUnorm)
  calc
    ‖sandwichContinuous U U.adjoint‖ ≤
        ‖U‖ * ‖U.adjoint‖ :=
      sandwichContinuous_norm_le U U.adjoint
    _ = ‖U‖ ^ 2 := by rw [hAdj]; ring
    _ ≤ 1 := hsq

/-- The source coordinate map R is 1-Lipschitz on true Schatten S₁. -/
theorem coisometric_retraction_dist_le_v007
    (U : H →L[ℂ] H) (hUnorm : ‖U‖ ≤ (1 : ℝ))
    (T V : TraceClass H) :
    dist (sandwichContinuous U U.adjoint T)
         (sandwichContinuous U U.adjoint V) ≤ dist T V := by
  calc
    dist (sandwichContinuous U U.adjoint T)
         (sandwichContinuous U U.adjoint V) =
        ‖sandwichContinuous U U.adjoint (T - V)‖ := by
      rw [dist_eq_norm, map_sub]
    _ ≤ ‖sandwichContinuous U U.adjoint‖ * ‖T - V‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖T - V‖ :=
      mul_le_mul_of_nonneg_right
        (coisometric_retraction_norm_le_one_v007 U hUnorm)
        (norm_nonneg _)
    _ = dist T V := by rw [dist_eq_norm, one_mul]

/-- Quantitative 1- and 2-Lipschitz continuity of the certified
projection onto range(E) and its kernel complement. -/
theorem coisometric_component_dist_le_v007
    (U : H →L[ℂ] H) (hUnorm : ‖U‖ ≤ (1 : ℝ))
    (T V : TraceClass H) :
    dist (coisometric_sandwich_projection_v007 U T)
         (coisometric_sandwich_projection_v007 U V) ≤ dist T V ∧
    dist (coisometric_complementaryProjection_v007 U T)
         (coisometric_complementaryProjection_v007 U V) ≤
      2 * dist T V := by
  obtain ⟨hP, hQ⟩ :=
    coisometric_closed_components_norm_le_v007 U hUnorm (T - V)
  constructor
  · simpa only [dist_eq_norm, map_sub] using hP
  · simpa only [dist_eq_norm, map_sub] using hQ

/-- Any two exact coisometric S₁ decompositions have source and
kernel coordinates with explicit Lipschitz bounds. -/
theorem coisometric_unique_coordinates_dist_le_v007
    (U : H →L[ℂ] H) (hUUstar : U * U.adjoint = 1)
    (hUnorm : ‖U‖ ≤ (1 : ℝ))
    (T V X Y X' Y' : TraceClass H)
    (hT : T = sandwichContinuous U.adjoint U X + Y)
    (hV : V = sandwichContinuous U.adjoint U X' + Y')
    (hY : sandwichContinuous U U.adjoint Y = 0)
    (hY' : sandwichContinuous U U.adjoint Y' = 0) :
    dist X X' ≤ dist T V ∧ dist Y Y' ≤ 2 * dist T V := by
  obtain ⟨hX, hYcoord⟩ :=
    coisometric_split_coordinates_unique_v007 U hUUstar T X Y hT hY
  obtain ⟨hX', hYcoord'⟩ :=
    coisometric_split_coordinates_unique_v007 U hUUstar V X' Y' hV hY'
  constructor
  · rw [hX, hX']
    exact coisometric_retraction_dist_le_v007 U hUnorm T V
  · rw [hYcoord, hYcoord']
    exact (coisometric_component_dist_le_v007 U hUnorm T V).2

/-- In particular the unique source coordinate has norm at most
‖T‖₁ and the unique kernel coordinate norm at most 2‖T‖₁. -/
theorem coisometric_unique_coordinates_norm_le_v007
    (U : H →L[ℂ] H) (hUUstar : U * U.adjoint = 1)
    (hUnorm : ‖U‖ ≤ (1 : ℝ))
    (T X Y : TraceClass H)
    (hT : T = sandwichContinuous U.adjoint U X + Y)
    (hY : sandwichContinuous U U.adjoint Y = 0) :
    ‖X‖ ≤ ‖T‖ ∧ ‖Y‖ ≤ 2 * ‖T‖ := by
  obtain ⟨hX, hYcoord⟩ :=
    coisometric_split_coordinates_unique_v007 U hUUstar T X Y hT hY
  rw [hX, hYcoord]
  constructor
  · calc
      ‖sandwichContinuous U U.adjoint T‖ ≤
        ‖sandwichContinuous U U.adjoint‖ * ‖T‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖T‖ :=
        mul_le_mul_of_nonneg_right
          (coisometric_retraction_norm_le_one_v007 U hUnorm)
          (norm_nonneg _)
      _ = ‖T‖ := one_mul _
  · exact (coisometric_closed_components_norm_le_v007 U hUnorm T).2

#print axioms ProbabilisticTheory.TraceClass.coisometric_retraction_norm_le_one_v007
#print axioms ProbabilisticTheory.TraceClass.coisometric_retraction_dist_le_v007
#print axioms ProbabilisticTheory.TraceClass.coisometric_component_dist_le_v007
#print axioms ProbabilisticTheory.TraceClass.coisometric_unique_coordinates_dist_le_v007
#print axioms ProbabilisticTheory.TraceClass.coisometric_unique_coordinates_norm_le_v007

end ProbabilisticTheory.TraceClass
