import GegenbauerFock.OutputInteriorUniquenessBridge

/-!
# V007 — unconditional continuity of coherent Fock restriction on (-1,1)

The actual coherent evaluation is a locally uniformly convergent series:
on the ultraspherical interior the absolute values of its terms are
dominated by the point-evaluation kernel at the endpoint u=1, paired
with the fixed ℓ² coefficient vector. Hölder's inequality in ℓ²
supplies a summable majorant. This removes the continuity hypothesis
from the a.e.-to-pointwise adjoint-kernel equivalence.

The analytic identity theorem, and hence unconditional injectivity of
the output adjoint, remain separate obligations.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal InnerProduct

namespace GegenbauerFock.FockAnalyticRestriction

/-- On the open ultraspherical support, the genuine ℓ² Fock evaluation
is continuous. The majorant is an actual ℓ² inner-product majorant,
not a finite-dimensional truncation. -/
theorem continuousOn_evaluate_interior
    (alpha : ℝ) (ha : 0 < alpha)
    (F : InfiniteAnalysis.FockCoefficients) :
    ContinuousOn (evaluate alpha ha F) (Set.Ioo (-1 : ℝ) 1) := by
  let k := FockEvaluation.kernelVector alpha ha (imaginaryPoint alpha 1)
  have hs : Summable (fun n : ℕ =>
      ‖FockEvaluation.kernelCoordinate alpha (imaginaryPoint alpha 1) n‖ *
        ‖F n‖) := by
    exact lp.summable_mul
      (by rw [Real.holderConjugate_iff]; norm_num) k F
  have hterm (n : ℕ) :
      Continuous (fun u : ℝ =>
        inner ℂ
          (FockEvaluation.kernelCoordinate alpha (imaginaryPoint alpha u) n)
          (F n)) := by
    unfold imaginaryPoint FockEvaluation.kernelCoordinate
    fun_prop
  have hbound (u : ℝ) (hu : u ∈ Set.Ioo (-1 : ℝ) 1) (n : ℕ) :
      ‖FockEvaluation.kernelCoordinate alpha (imaginaryPoint alpha u) n‖ ≤
        ‖FockEvaluation.kernelCoordinate alpha (imaginaryPoint alpha 1) n‖ := by
    have hu' : |u| ≤ (1 : ℝ) :=
      abs_le.mpr ⟨le_of_lt hu.1, le_of_lt hu.2⟩
    have hnorm : ‖imaginaryPoint alpha u‖ ≤ ‖imaginaryPoint alpha 1‖ := by
      rw [norm_imaginaryPoint alpha u ha, norm_imaginaryPoint alpha 1 ha]
      simpa using (div_le_div_of_nonneg_right hu'
        (by positivity : 0 ≤ 2 * alpha))
    unfold FockEvaluation.kernelCoordinate
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow, norm_star]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) hnorm n) (abs_nonneg _)
  have hcont :
      ContinuousOn (fun u : ℝ => ∑' n : ℕ,
        inner ℂ
          (FockEvaluation.kernelCoordinate alpha (imaginaryPoint alpha u) n)
          (F n)) (Set.Ioo (-1 : ℝ) 1) := by
    apply continuousOn_tsum (fun n => (hterm n).continuousOn) hs
    intro n u hu
    calc
      ‖inner ℂ
          (FockEvaluation.kernelCoordinate alpha (imaginaryPoint alpha u) n)
          (F n)‖ ≤
          ‖FockEvaluation.kernelCoordinate alpha (imaginaryPoint alpha u) n‖ *
            ‖F n‖ := norm_inner_le_norm _ _
      _ ≤ ‖FockEvaluation.kernelCoordinate alpha (imaginaryPoint alpha 1) n‖ *
            ‖F n‖ :=
        mul_le_mul_of_nonneg_right (hbound u hu n) (norm_nonneg _)
  have heq : (fun u : ℝ => ∑' n : ℕ,
      inner ℂ
        (FockEvaluation.kernelCoordinate alpha (imaginaryPoint alpha u) n)
        (F n)) = evaluate alpha ha F := by
    funext u
    exact (FockEvaluation.evaluation_eq_tsum_inner
      alpha ha (imaginaryPoint alpha u) F).symm
  rw [← heq]
  exact hcont

#print axioms GegenbauerFock.FockAnalyticRestriction.continuousOn_evaluate_interior

end GegenbauerFock.FockAnalyticRestriction

namespace GegenbauerFock.Ultraspherical

/-- Full interior-support uniqueness only requires continuity on the
interior; global continuity outside the support is unnecessary. -/
theorem continuousOn_ae_zero_iff_interior_zero
    (lam : ℝ) (hlam : 0 < lam)
    {f : ℝ → ℂ} (hf : ContinuousOn f (Set.Ioo (-1 : ℝ) 1)) :
    f =ᵐ[measure lam] (0 : ℝ → ℂ) ↔
      ∀ u ∈ Set.Ioo (-1 : ℝ) 1, f u = 0 := by
  constructor
  · intro hz u hu
    by_contra hne
    let U : Set ℝ := Set.Ioo (-1 : ℝ) 1 ∩ {x : ℝ | f x ≠ 0}
    have hopen : IsOpen U := by
      change IsOpen (Set.Ioo (-1 : ℝ) 1 ∩
        f ⁻¹' ({(0 : ℂ)} : Set ℂ)ᶜ)
      exact hf.isOpen_inter_preimage isOpen_Ioo isClosed_singleton.isOpen_compl
    obtain ⟨a, b, hab, hsub⟩ :=
      hopen.exists_Ioo_subset (show U.Nonempty from ⟨u, ⟨hu, hne⟩⟩)
    have hinside : Set.Ioo a b ⊆ Set.Ioo (-1 : ℝ) 1 :=
      hsub.trans Set.inter_subset_left
    have hbounds : (-1 : ℝ) ≤ a ∧ b ≤ 1 :=
      (Set.Ioo_subset_Ioo_iff hab).mp hinside
    have hnull : measure lam {x : ℝ | f x ≠ 0} = 0 := ae_iff.mp hz
    have hintervalnull : measure lam (Set.Ioo a b) = 0 :=
      measure_mono_null (hsub.trans Set.inter_subset_right) hnull
    exact (ne_of_gt (measure_Ioo_pos lam a b hlam hbounds.1 hab hbounds.2))
      hintervalnull
  · intro h
    filter_upwards [ae_mem_open_interval lam] with u hu
    exact h u hu

#print axioms GegenbauerFock.Ultraspherical.continuousOn_ae_zero_iff_interior_zero

end GegenbauerFock.Ultraspherical

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The actual adjoint kernel is exactly the pointwise vanishing set
of the coherent restriction on (-1,1), without a continuity premise. -/
theorem C_adjoint_eq_zero_iff_interior_zero
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (F : InfiniteAnalysis.FockCoefficients) :
    C_adjoint lam alpha hlam ha F = 0 ↔
      ∀ u ∈ Set.Ioo (-1 : ℝ) 1,
        FockAnalyticRestriction.evaluate alpha ha F u = 0 := by
  exact
    (C_adjoint_eq_zero_iff_analytic_restriction_ae_zero
      lam alpha hlam ha F).trans
      (Ultraspherical.continuousOn_ae_zero_iff_interior_zero lam hlam
        (FockAnalyticRestriction.continuousOn_evaluate_interior alpha ha F))

/-- The only remaining hypothesis for injectivity of the output
adjoint is pointwise analytic uniqueness on the interior interval. -/
theorem C_adjoint_injective_of_interior_unique
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (hunique : ∀ F : InfiniteAnalysis.FockCoefficients,
      (∀ u ∈ Set.Ioo (-1 : ℝ) 1,
        FockAnalyticRestriction.evaluate alpha ha F u = 0) → F = 0) :
    Function.Injective (C_adjoint lam alpha hlam ha) := by
  apply (C_adjoint_injective_iff_analytic_uniqueness_ae
    lam alpha hlam ha).mpr
  intro F hz
  apply hunique F
  exact (Ultraspherical.continuousOn_ae_zero_iff_interior_zero lam hlam
    (FockAnalyticRestriction.continuousOn_evaluate_interior alpha ha F)).mp hz

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_adjoint_eq_zero_iff_interior_zero
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_adjoint_injective_of_interior_unique

end GegenbauerFock.GeneralUltrasphericalFock
