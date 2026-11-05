import GegenbauerFock.GaussianAreaFullIntrinsicFockSurjectivity
import GegenbauerFock.GaussianAreaEntireDensityByMoments

/-!
# V007 — closed intrinsic holomorphic Gaussian Hilbert space and polynomial density

The analytic Bargmann–Fock space is independently defined as the submodule
of genuine weighted Gaussian L² equivalence classes possessing an entire
representative. We prove that this *intrinsic* submodule is closed in the
ambient Gaussian L², and that the true finite holomorphic monomial
polynomials are dense in it.

The closure proof uses the complete ℓ² source and the independently proved
range identification, not a definition of the analytic space as an a priori
polynomial closure. Density is exhibited by actual L²-convergent finite
polynomial partial sums, for every intrinsic entire L² class.

Finally, uniqueness of entire representatives upgrades the L² synthesis
to a pointwise coherent-series formula on every complex number.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace GegenbauerFock.GaussianArea

/-- The independently defined analytic Gaussian entire L² submodule
coincides as an ambient set with the complete coefficient synthesis range. -/
theorem coefficientSynthesisL2_range_eq_intrinsicEntire
    (alpha : ℝ) (ha : 0 < alpha) :
    Set.range (coefficientSynthesisL2 alpha ha) =
      (entireGaussianL2Submodule alpha :
        Set (Lp ℂ 2 (gaussianAreaMeasure alpha))) := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact coefficientSynthesisL2_mem_entireGaussianL2Submodule alpha ha a
  · intro hx
    obtain ⟨a, hax⟩ :=
      intrinsicEntire_exists_coefficient_synthesis alpha ha
        (⟨x, hx⟩ : entireGaussianL2Submodule alpha)
    exact ⟨a, hax⟩

/-- The full intrinsically defined entire-function Gaussian L² space
is closed in the ambient weighted Gaussian L² Hilbert space. -/
theorem entireGaussianL2Submodule_isClosed
    (alpha : ℝ) (ha : 0 < alpha) :
    IsClosed (entireGaussianL2Submodule alpha :
      Set (Lp ℂ 2 (gaussianAreaMeasure alpha))) := by
  rw [← coefficientSynthesisL2_range_eq_intrinsicEntire alpha ha]
  exact coefficientSynthesisL2_range_isClosed alpha ha

/-- The closed Gaussian polynomial subspace is exactly the independently
specified analytic entire Gaussian L² subspace; no density assumption
is made, since uniqueness of genuine Gaussian moments proves this. -/
theorem gaussianPolynomialClosure_eq_fullIntrinsicEntire
    (alpha : ℝ) (ha : 0 < alpha) :
    gaussianPolynomialClosure alpha ha =
      entireGaussianL2Submodule alpha :=
  (intrinsicEntire_eq_gaussianPolynomialClosure alpha ha).symm

/-- Every intrinsically entire Gaussian L² vector is approximated in
actual ambient L² norm by finite holomorphic Gaussian polynomials.
The coefficients are genuinely square-summable, and the approximants
are the concrete normalized monomial partial sums. -/
theorem intrinsicEntire_exists_polynomialApproximation
    (alpha : ℝ) (ha : 0 < alpha)
    (x : entireGaussianL2Submodule alpha) :
    ∃ a : lp (fun _ : ℕ => ℂ) 2,
      Tendsto
        (fun n : ℕ => ∑ k ∈ Finset.range n,
          a k • normalizedMonomialL2Vector alpha ha k)
        atTop
        (𝓝 (x : Lp ℂ 2 (gaussianAreaMeasure alpha))) := by
  obtain ⟨a, hax⟩ :=
    intrinsicEntire_exists_coefficient_synthesis alpha ha x
  refine ⟨a, ?_⟩
  rw [← hax]
  exact (coefficientSynthesisL2_hasSum alpha ha a).tendsto_sum_nat

/-- A stronger functional formulation: the *entire* representative of
any intrinsic Gaussian L² class is given at every complex point by
the normalized coherent Bargmann–Fock series with ℓ² coefficients. -/
theorem intrinsicEntire_exists_pointwiseCoherentSeries
    (alpha : ℝ) (ha : 0 < alpha)
    (x : entireGaussianL2Submodule alpha) :
    ∃ a : lp (fun _ : ℕ => ℂ) 2,
      ∀ z : ℂ,
        entireRepresentative alpha x z =
          FockEvaluation.evaluation alpha ha z a := by
  obtain ⟨a, hax⟩ :=
    intrinsicEntire_exists_coefficient_synthesis alpha ha x
  have hx : x = synthesizedIntrinsicVector alpha ha a := by
    apply Subtype.ext
    exact hax.symm
  refine ⟨a, ?_⟩
  intro z
  rw [hx]
  exact congrFun (entireRepresentative_synthesized alpha ha a) z

/-- The previously kernel-certified ℓ² isometry is onto precisely the
whole closed intrinsic Gaussian entire Hilbert space, rather than only
an unspecified polynomial coefficient space. -/
theorem coefficientIntrinsicEntireEquiv_fullBargmannFock_surjective
    (alpha : ℝ) (ha : 0 < alpha) :
    Function.Surjective (coefficientIntrinsicEntireEquiv alpha ha) :=
  (coefficientIntrinsicEntireEquiv alpha ha).surjective

#print axioms GegenbauerFock.GaussianArea.coefficientSynthesisL2_range_eq_intrinsicEntire
#print axioms GegenbauerFock.GaussianArea.entireGaussianL2Submodule_isClosed
#print axioms GegenbauerFock.GaussianArea.gaussianPolynomialClosure_eq_fullIntrinsicEntire
#print axioms GegenbauerFock.GaussianArea.intrinsicEntire_exists_polynomialApproximation
#print axioms GegenbauerFock.GaussianArea.intrinsicEntire_exists_pointwiseCoherentSeries
#print axioms GegenbauerFock.GaussianArea.coefficientIntrinsicEntireEquiv_fullBargmannFock_surjective

end GegenbauerFock.GaussianArea
