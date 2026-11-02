import GegenbauerFock.PhyslibTraceClassCoisometricClosedRanges
import GegenbauerFock.PhyslibTraceClassCoisometricUniqueness
import GegenbauerFock.PhyslibTraceClassConjugationPerturbation

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


/-- Simultaneous perturbation of data and the *retraction* multiplier.
The true S₁ estimate does not require the coisometry identity: the
contractivity hypotheses alone suffice. -/
theorem coisometric_retraction_joint_traceNorm_le_v007
    (U V : H →L[ℂ] H) (T S : TraceClass H)
    (hU : ‖U‖ ≤ (1 : ℝ)) (hV : ‖V‖ ≤ (1 : ℝ)) :
    traceNorm H
      (sandwichContinuous U U.adjoint T -
       sandwichContinuous V V.adjoint S) ≤
      traceNorm H (T - S) + 2 * ‖U - V‖ * traceNorm H S := by
  have hAdjU : ‖U.adjoint‖ ≤ (1 : ℝ) := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    simpa only [norm_star] using hU
  have hAdjV : ‖V.adjoint‖ ≤ (1 : ℝ) := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    simpa only [norm_star] using hV
  have h := conjugation_traceNorm_joint_input_contractions_dist_le_v007
    U.adjoint V.adjoint T S hAdjU hAdjV
  change traceNorm H
    (sandwich T U U.adjoint - sandwich S V V.adjoint) ≤
      traceNorm H (T - S) + 2 * ‖U - V‖ * traceNorm H S
  simpa only [conjugate, ContinuousLinearMap.adjoint_adjoint,
    conjugation_adjoint_sub_norm_eq_v007 U V] using h

/-- The canonical range components for *different* contractive
coisometric multipliers are jointly Lipschitz in the data and the
multiplier, with explicit coefficient four on multiplier variation. -/
theorem coisometric_projection_joint_traceNorm_le_v007
    (U V : H →L[ℂ] H) (T S : TraceClass H)
    (hU : ‖U‖ ≤ (1 : ℝ)) (hV : ‖V‖ ≤ (1 : ℝ)) :
    traceNorm H
      (coisometric_sandwich_projection_v007 U T -
       coisometric_sandwich_projection_v007 V S) ≤
      traceNorm H (T - S) + 4 * ‖U - V‖ * traceNorm H S := by
  let RT : TraceClass H := sandwichContinuous U U.adjoint T
  let RS : TraceClass H := sandwichContinuous V V.adjoint S
  have hR : traceNorm H (RT - RS) ≤
      traceNorm H (T - S) + 2 * ‖U - V‖ * traceNorm H S :=
    coisometric_retraction_joint_traceNorm_le_v007 U V T S hU hV
  have hRS : traceNorm H RS ≤ traceNorm H S := by
    change ‖RS‖ ≤ ‖S‖
    calc
      ‖RS‖ ≤ ‖sandwichContinuous V V.adjoint‖ * ‖S‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖S‖ :=
        mul_le_mul_of_nonneg_right
          (coisometric_retraction_norm_le_one_v007 V hV) (norm_nonneg _)
      _ = ‖S‖ := one_mul _
  have hInner :=
    conjugation_traceNorm_joint_input_contractions_dist_le_v007
      U V RT RS hU hV
  have hMult :
      2 * ‖U - V‖ * traceNorm H RS ≤
        2 * ‖U - V‖ * traceNorm H S :=
    mul_le_mul_of_nonneg_left hRS (by positivity)
  change traceNorm H (conjugate RT U - conjugate RS V) ≤
    traceNorm H (T - S) + 4 * ‖U - V‖ * traceNorm H S
  calc
    traceNorm H (conjugate RT U - conjugate RS V) ≤
        traceNorm H (RT - RS) +
          2 * ‖U - V‖ * traceNorm H RS := hInner
    _ ≤ (traceNorm H (T - S) +
          2 * ‖U - V‖ * traceNorm H S) +
          2 * ‖U - V‖ * traceNorm H S :=
      add_le_add hR hMult
    _ = traceNorm H (T - S) +
          4 * ‖U - V‖ * traceNorm H S := by ring

set_option maxHeartbeats 1200000

/-- The canonical complementary components for different coisometries
are stable with coefficient two for input perturbations and four for
multiplier perturbations, in the genuine trace norm. -/
theorem coisometric_complement_joint_traceNorm_le_v007
    (U V : H →L[ℂ] H) (T S : TraceClass H)
    (hU : ‖U‖ ≤ (1 : ℝ)) (hV : ‖V‖ ≤ (1 : ℝ)) :
    traceNorm H
      (coisometric_complementaryProjection_v007 U T -
       coisometric_complementaryProjection_v007 V S) ≤
      2 * traceNorm H (T - S) +
        4 * ‖U - V‖ * traceNorm H S := by
  have hP := coisometric_projection_joint_traceNorm_le_v007
    U V T S hU hV
  change ‖coisometric_sandwich_projection_v007 U T -
    coisometric_sandwich_projection_v007 V S‖ ≤
      ‖T - S‖ + 4 * ‖U - V‖ * ‖S‖ at hP
  have hQ :
      coisometric_complementaryProjection_v007 U T -
          coisometric_complementaryProjection_v007 V S =
        (T - S) -
          (coisometric_sandwich_projection_v007 U T -
           coisometric_sandwich_projection_v007 V S) := by
    change (T - coisometric_sandwich_projection_v007 U T) -
      (S - coisometric_sandwich_projection_v007 V S) = _
    abel
  calc
    traceNorm H
        (coisometric_complementaryProjection_v007 U T -
         coisometric_complementaryProjection_v007 V S) =
        ‖(T - S) -
          (coisometric_sandwich_projection_v007 U T -
           coisometric_sandwich_projection_v007 V S)‖ := by
      rw [hQ]
      exact (norm_eq_genuineTraceNorm _).symm
    _ ≤ ‖T - S‖ +
        ‖coisometric_sandwich_projection_v007 U T -
         coisometric_sandwich_projection_v007 V S‖ := norm_sub_le _ _
    _ ≤ ‖T - S‖ + (‖T - S‖ + 4 * ‖U - V‖ * ‖S‖) :=
      add_le_add (le_refl _) hP
    _ = 2 * traceNorm H (T - S) +
        4 * ‖U - V‖ * traceNorm H S := by
      rw [← norm_eq_genuineTraceNorm (T - S),
        ← norm_eq_genuineTraceNorm S]
      ring

set_option maxHeartbeats 200000

/-- Quantitative stability of the uniquely determined source and kernel
coordinates when both the input and the coisometry vary. Exact
coisometry equations guarantee uniqueness; the numerical constants
come from the separate contractive perturbation estimates. -/
theorem coisometric_unique_coordinates_joint_traceNorm_le_v007
    (U V : H →L[ℂ] H)
    (hUUstar : U * U.adjoint = 1)
    (hVVstar : V * V.adjoint = 1)
    (hUnorm : ‖U‖ ≤ (1 : ℝ))
    (hVnorm : ‖V‖ ≤ (1 : ℝ))
    (T S X Y X' Y' : TraceClass H)
    (hT : T = sandwichContinuous U.adjoint U X + Y)
    (hS : S = sandwichContinuous V.adjoint V X' + Y')
    (hY : sandwichContinuous U U.adjoint Y = 0)
    (hY' : sandwichContinuous V V.adjoint Y' = 0) :
    traceNorm H (X - X') ≤
        traceNorm H (T - S) + 2 * ‖U - V‖ * traceNorm H S ∧
    traceNorm H (Y - Y') ≤
        2 * traceNorm H (T - S) + 4 * ‖U - V‖ * traceNorm H S := by
  obtain ⟨hX, hYcoord⟩ :=
    coisometric_split_coordinates_unique_v007 U hUUstar T X Y hT hY
  obtain ⟨hX', hYcoord'⟩ :=
    coisometric_split_coordinates_unique_v007 V hVVstar S X' Y' hS hY'
  constructor
  · rw [hX, hX']
    exact coisometric_retraction_joint_traceNorm_le_v007
      U V T S hUnorm hVnorm
  · rw [hYcoord, hYcoord']
    exact coisometric_complement_joint_traceNorm_le_v007
      U V T S hUnorm hVnorm

/-- The retraction operators themselves vary 2-Lipschitzly in
operator norm on the genuine CFC Schatten S₁ space. Only contractivity
of U and V is needed; the coisometry identities are not required. -/
theorem coisometric_retraction_operator_perturbation_v007
    (U V : H →L[ℂ] H)
    (hU : ‖U‖ ≤ (1 : ℝ)) (hV : ‖V‖ ≤ (1 : ℝ)) :
    ‖sandwichContinuous U U.adjoint -
      sandwichContinuous V V.adjoint‖ ≤ 2 * ‖U - V‖ := by
  have hAdjU : ‖U.adjoint‖ ≤ (1 : ℝ) := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    simpa only [norm_star] using hU
  have hAdjV : ‖V.adjoint‖ ≤ (1 : ℝ) := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    simpa only [norm_star] using hV
  have h := conjugationContinuous_contractions_dist_le_v007
    U.adjoint V.adjoint hAdjU hAdjV
  simpa only [ContinuousLinearMap.adjoint_adjoint,
    conjugation_adjoint_sub_norm_eq_v007 U V] using h

/-- The range projections P_U and P_V differ by at most
4 ‖U-V‖ in B(S₁), for two contractive bounded multipliers. -/
theorem coisometric_projection_operator_perturbation_v007
    (U V : H →L[ℂ] H)
    (hU : ‖U‖ ≤ (1 : ℝ)) (hV : ‖V‖ ≤ (1 : ℝ)) :
    ‖coisometric_sandwich_projection_v007 U -
      coisometric_sandwich_projection_v007 V‖ ≤
      4 * ‖U - V‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro T
  have h := coisometric_projection_joint_traceNorm_le_v007
    U V T T hU hV
  change ‖coisometric_sandwich_projection_v007 U T -
    coisometric_sandwich_projection_v007 V T‖ ≤
      ‖T - T‖ + 4 * ‖U - V‖ * ‖T‖ at h
  calc
    ‖(coisometric_sandwich_projection_v007 U -
       coisometric_sandwich_projection_v007 V) T‖ =
        ‖coisometric_sandwich_projection_v007 U T -
          coisometric_sandwich_projection_v007 V T‖ := by
      rw [ContinuousLinearMap.sub_apply]
    _ ≤ ‖T - T‖ + 4 * ‖U - V‖ * ‖T‖ := h
    _ = (4 * ‖U - V‖) * ‖T‖ := by simp

/-- The complementary projections Q_U and Q_V have the same
4-Lipschitz perturbation bound on the genuine Schatten S₁ space. -/
theorem coisometric_complement_operator_perturbation_v007
    (U V : H →L[ℂ] H)
    (hU : ‖U‖ ≤ (1 : ℝ)) (hV : ‖V‖ ≤ (1 : ℝ)) :
    ‖coisometric_complementaryProjection_v007 U -
      coisometric_complementaryProjection_v007 V‖ ≤
      4 * ‖U - V‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro T
  have h := coisometric_complement_joint_traceNorm_le_v007
    U V T T hU hV
  change ‖coisometric_complementaryProjection_v007 U T -
    coisometric_complementaryProjection_v007 V T‖ ≤
      2 * ‖T - T‖ + 4 * ‖U - V‖ * ‖T‖ at h
  calc
    ‖(coisometric_complementaryProjection_v007 U -
       coisometric_complementaryProjection_v007 V) T‖ =
        ‖coisometric_complementaryProjection_v007 U T -
          coisometric_complementaryProjection_v007 V T‖ := by
      rw [ContinuousLinearMap.sub_apply]
    _ ≤ 2 * ‖T - T‖ + 4 * ‖U - V‖ * ‖T‖ := h
    _ = (4 * ‖U - V‖) * ‖T‖ := by simp

/-- Directed quantitative gap for the closed embedded S₁ ranges
under perturbation of coisometries. For each source T in range(E_U),
the explicit target approximation is P_V(T), with trace-norm error
at most 4 ‖U-V‖ ‖T‖. This is an upper bound, not an optimality claim. -/
theorem coisometric_embedding_range_directed_gap_v007
    (U V : H →L[ℂ] H)
    (hUUstar : U * U.adjoint = 1)
    (hUnorm : ‖U‖ ≤ (1 : ℝ))
    (hVnorm : ‖V‖ ≤ (1 : ℝ))
    (T : TraceClass H)
    (hT : T ∈ Set.range (sandwichContinuous U.adjoint U)) :
    ∃ S : TraceClass H,
      S ∈ Set.range (sandwichContinuous V.adjoint V) ∧
      dist T S ≤ 4 * ‖U - V‖ * ‖T‖ := by
  obtain ⟨X, hX⟩ := hT
  have hFix : coisometric_sandwich_projection_v007 U T = T := by
    rw [← hX]
    exact coisometric_projection_fixes_image_v007 U hUUstar X
  let S : TraceClass H := coisometric_sandwich_projection_v007 V T
  have hRange : S ∈ Set.range (sandwichContinuous V.adjoint V) := by
    refine ⟨sandwichContinuous V V.adjoint T, ?_⟩
    rfl
  refine ⟨S, hRange, ?_⟩
  have hOp :=
    coisometric_projection_operator_perturbation_v007
      U V hUnorm hVnorm
  calc
    dist T S =
        ‖(coisometric_sandwich_projection_v007 U -
           coisometric_sandwich_projection_v007 V) T‖ := by
      rw [dist_eq_norm, ContinuousLinearMap.sub_apply, hFix]
    _ ≤ ‖coisometric_sandwich_projection_v007 U -
            coisometric_sandwich_projection_v007 V‖ * ‖T‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ (4 * ‖U - V‖) * ‖T‖ :=
      mul_le_mul_of_nonneg_right hOp (norm_nonneg _)
    _ = 4 * ‖U - V‖ * ‖T‖ := by ring

/-- Directed quantitative gap of the closed kernels ker(R_U).
For T in ker(R_U), the canonical target approximation is Q_V(T),
which lies in ker(R_V), with error bounded in the genuine S₁ norm. -/
theorem coisometric_retraction_kernel_directed_gap_v007
    (U V : H →L[ℂ] H)
    (hUUstar : U * U.adjoint = 1)
    (hVVstar : V * V.adjoint = 1)
    (hUnorm : ‖U‖ ≤ (1 : ℝ))
    (hVnorm : ‖V‖ ≤ (1 : ℝ))
    (T : TraceClass H)
    (hT : sandwichContinuous U U.adjoint T = 0) :
    ∃ S : TraceClass H,
      sandwichContinuous V V.adjoint S = 0 ∧
      dist T S ≤ 4 * ‖U - V‖ * ‖T‖ := by
  have hFix : coisometric_complementaryProjection_v007 U T = T :=
    (coisometric_retraction_kernel_iff_complement_fixed_v007
      U hUUstar T).mp hT
  let S : TraceClass H := coisometric_complementaryProjection_v007 V T
  have hKer : sandwichContinuous V V.adjoint S = 0 :=
    coisometric_retraction_complement_zero_v007 V hVVstar T
  refine ⟨S, hKer, ?_⟩
  have hOp :=
    coisometric_complement_operator_perturbation_v007
      U V hUnorm hVnorm
  calc
    dist T S =
        ‖(coisometric_complementaryProjection_v007 U -
           coisometric_complementaryProjection_v007 V) T‖ := by
      rw [dist_eq_norm, ContinuousLinearMap.sub_apply, hFix]
    _ ≤ ‖coisometric_complementaryProjection_v007 U -
            coisometric_complementaryProjection_v007 V‖ * ‖T‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ (4 * ‖U - V‖) * ‖T‖ :=
      mul_le_mul_of_nonneg_right hOp (norm_nonneg _)
    _ = 4 * ‖U - V‖ * ‖T‖ := by ring

/-- Complementary and range projections have exactly opposite
operator perturbations, without any coisometry or norm hypothesis.
This improves the paired upper bounds to an exact equality of
the associated operator-norm variations. -/
theorem coisometric_complement_operator_difference_eq_neg_projection_v007
    (U V : H →L[ℂ] H) :
    coisometric_complementaryProjection_v007 U -
      coisometric_complementaryProjection_v007 V =
    -(coisometric_sandwich_projection_v007 U -
      coisometric_sandwich_projection_v007 V) := by
  change
    ((ContinuousLinearMap.id ℂ (TraceClass H) -
        coisometric_sandwich_projection_v007 U) -
      (ContinuousLinearMap.id ℂ (TraceClass H) -
        coisometric_sandwich_projection_v007 V)) =
      -(coisometric_sandwich_projection_v007 U -
        coisometric_sandwich_projection_v007 V)
  abel

/-- Exact equality of operator perturbation norms of the
complementary and range projections on true CFC Schatten S₁. -/
theorem coisometric_complement_operator_difference_norm_eq_projection_v007
    (U V : H →L[ℂ] H) :
    ‖coisometric_complementaryProjection_v007 U -
      coisometric_complementaryProjection_v007 V‖ =
    ‖coisometric_sandwich_projection_v007 U -
      coisometric_sandwich_projection_v007 V‖ := by
  rw [coisometric_complement_operator_difference_eq_neg_projection_v007 U V,
    norm_neg]


/-- An explicit upper bound for the normalized directed gap from A
to B. The source vector is restricted to the closed unit ball, and
the target point may be any point in B. This is the quantified
upper-bound formulation of the supremum of point-to-set distances. -/
def normalizedDirectedGapLE_v007
    (A B : Set (TraceClass H)) (eps : ℝ) : Prop :=
  ∀ T : TraceClass H, T ∈ A → ‖T‖ ≤ 1 →
    ∃ S : TraceClass H, S ∈ B ∧ dist T S ≤ eps

/-- The two-sided normalized gap upper bound: both directed unit-ball
distance bounds hold with the same prescribed epsilon. -/
def normalizedBidirectionalGapLE_v007
    (A B : Set (TraceClass H)) (eps : ℝ) : Prop :=
  normalizedDirectedGapLE_v007 A B eps ∧
    normalizedDirectedGapLE_v007 B A eps

/-- Coisometric closed embedding ranges have normalized two-sided
gap at most 4 ‖U-V‖ in the true Schatten S₁ Banach topology. -/
theorem coisometric_embedding_range_normalized_bidirectional_gap_v007
    (U V : H →L[ℂ] H)
    (hUUstar : U * U.adjoint = 1)
    (hVVstar : V * V.adjoint = 1)
    (hUnorm : ‖U‖ ≤ (1 : ℝ))
    (hVnorm : ‖V‖ ≤ (1 : ℝ)) :
    normalizedBidirectionalGapLE_v007
      (Set.range (sandwichContinuous U.adjoint U))
      (Set.range (sandwichContinuous V.adjoint V))
      (4 * ‖U - V‖) := by
  constructor
  · intro T hT hTnorm
    obtain ⟨S, hS, hdist⟩ :=
      coisometric_embedding_range_directed_gap_v007
        U V hUUstar hUnorm hVnorm T hT
    refine ⟨S, hS, ?_⟩
    calc
      dist T S ≤ 4 * ‖U - V‖ * ‖T‖ := hdist
      _ ≤ 4 * ‖U - V‖ * 1 :=
        mul_le_mul_of_nonneg_left hTnorm (by positivity)
      _ = 4 * ‖U - V‖ := by ring
  · intro T hT hTnorm
    obtain ⟨S, hS, hdist⟩ :=
      coisometric_embedding_range_directed_gap_v007
        V U hVVstar hVnorm hUnorm T hT
    refine ⟨S, hS, ?_⟩
    calc
      dist T S ≤ 4 * ‖V - U‖ * ‖T‖ := hdist
      _ ≤ 4 * ‖V - U‖ * 1 :=
        mul_le_mul_of_nonneg_left hTnorm (by positivity)
      _ = 4 * ‖U - V‖ := by rw [norm_sub_rev]; ring

/-- The complementary closed kernels of the coisometric retractions
have normalized bidirectional gap at most 4 ‖U-V‖. No assertion of
optimality or finite-dimensionality is involved. -/
theorem coisometric_retraction_kernel_normalized_bidirectional_gap_v007
    (U V : H →L[ℂ] H)
    (hUUstar : U * U.adjoint = 1)
    (hVVstar : V * V.adjoint = 1)
    (hUnorm : ‖U‖ ≤ (1 : ℝ))
    (hVnorm : ‖V‖ ≤ (1 : ℝ)) :
    normalizedBidirectionalGapLE_v007
      {T : TraceClass H | sandwichContinuous U U.adjoint T = 0}
      {T : TraceClass H | sandwichContinuous V V.adjoint T = 0}
      (4 * ‖U - V‖) := by
  constructor
  · intro T hT hTnorm
    obtain ⟨S, hS, hdist⟩ :=
      coisometric_retraction_kernel_directed_gap_v007
        U V hUUstar hVVstar hUnorm hVnorm T hT
    refine ⟨S, hS, ?_⟩
    calc
      dist T S ≤ 4 * ‖U - V‖ * ‖T‖ := hdist
      _ ≤ 4 * ‖U - V‖ * 1 :=
        mul_le_mul_of_nonneg_left hTnorm (by positivity)
      _ = 4 * ‖U - V‖ := by ring
  · intro T hT hTnorm
    obtain ⟨S, hS, hdist⟩ :=
      coisometric_retraction_kernel_directed_gap_v007
        V U hVVstar hUUstar hVnorm hUnorm T hT
    refine ⟨S, hS, ?_⟩
    calc
      dist T S ≤ 4 * ‖V - U‖ * ‖T‖ := hdist
      _ ≤ 4 * ‖V - U‖ * 1 :=
        mul_le_mul_of_nonneg_left hTnorm (by positivity)
      _ = 4 * ‖U - V‖ := by rw [norm_sub_rev]; ring


#print axioms ProbabilisticTheory.TraceClass.coisometric_retraction_norm_le_one_v007
#print axioms ProbabilisticTheory.TraceClass.coisometric_retraction_dist_le_v007
#print axioms ProbabilisticTheory.TraceClass.coisometric_component_dist_le_v007
#print axioms ProbabilisticTheory.TraceClass.coisometric_unique_coordinates_dist_le_v007
#print axioms ProbabilisticTheory.TraceClass.coisometric_unique_coordinates_norm_le_v007
#print axioms ProbabilisticTheory.TraceClass.coisometric_retraction_joint_traceNorm_le_v007
#print axioms ProbabilisticTheory.TraceClass.coisometric_projection_joint_traceNorm_le_v007
#print axioms ProbabilisticTheory.TraceClass.coisometric_complement_joint_traceNorm_le_v007
#print axioms ProbabilisticTheory.TraceClass.coisometric_unique_coordinates_joint_traceNorm_le_v007
#print axioms ProbabilisticTheory.TraceClass.coisometric_retraction_operator_perturbation_v007
#print axioms ProbabilisticTheory.TraceClass.coisometric_projection_operator_perturbation_v007
#print axioms ProbabilisticTheory.TraceClass.coisometric_complement_operator_perturbation_v007
#print axioms ProbabilisticTheory.TraceClass.coisometric_complement_operator_difference_eq_neg_projection_v007
#print axioms ProbabilisticTheory.TraceClass.coisometric_complement_operator_difference_norm_eq_projection_v007
#print axioms ProbabilisticTheory.TraceClass.coisometric_embedding_range_directed_gap_v007
#print axioms ProbabilisticTheory.TraceClass.coisometric_retraction_kernel_directed_gap_v007
#print axioms ProbabilisticTheory.TraceClass.coisometric_embedding_range_normalized_bidirectional_gap_v007
#print axioms ProbabilisticTheory.TraceClass.coisometric_retraction_kernel_normalized_bidirectional_gap_v007

end ProbabilisticTheory.TraceClass
