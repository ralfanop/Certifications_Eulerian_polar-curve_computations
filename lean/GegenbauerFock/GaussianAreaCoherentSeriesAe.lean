import GegenbauerFock.GaussianAreaCoherentSeriesHasSum
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# V007 — genuine almost-everywhere identification of Gaussian Fock series

The same finite holomorphic polynomials converge in the Gaussian L²
norm and pointwise in the complex plane. We identify the two limits
using convergence in measure, a subsequence converging almost everywhere,
and uniqueness of pointwise limits. No polynomial density assumption
for independently given entire L² representatives is used.

This establishes that every ℓ²-synthesized Gaussian L² class admits
the actual entire coherent-state representative, and hence the
inclusion of the closed polynomial span in the intrinsic entire L²
submodule. The reverse inclusion remains a separate analytic task.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace GegenbauerFock.GaussianArea

/-- Every finite Gaussian L² monomial sum agrees almost everywhere
with the same finite sum of actual holomorphic polynomials. -/
theorem coefficientPartialSumL2_ae_polynomial
    (alpha : ℝ) (ha : 0 < alpha)
    (a : lp (fun _ : ℕ => ℂ) 2) (n : ℕ) :
    ((∑ k ∈ Finset.range n,
        a k • normalizedMonomialL2Vector alpha ha k :
          Lp ℂ 2 (gaussianAreaMeasure alpha)) : ℂ → ℂ)
      =ᵐ[gaussianAreaMeasure alpha]
        (fun z : ℂ => ∑ k ∈ Finset.range n,
          a k * normalizedMonomial alpha k z) := by
  induction n with
  | zero =>
      filter_upwards [Lp.coeFn_zero ℂ 2 (gaussianAreaMeasure alpha)] with z hz
      simpa [Finset.range_zero] using hz
  | succ n ih =>
      have hlast :
          ((a n • normalizedMonomialL2Vector alpha ha n :
              Lp ℂ 2 (gaussianAreaMeasure alpha)) : ℂ → ℂ)
            =ᵐ[gaussianAreaMeasure alpha]
              (fun z : ℂ => a n * normalizedMonomial alpha n z) := by
        filter_upwards [Lp.coeFn_smul (a n)
            (normalizedMonomialL2Vector alpha ha n),
          normalizedMonomialL2Vector_ae alpha ha n] with z hs hz
        calc
          (a n • normalizedMonomialL2Vector alpha ha n :
            Lp ℂ 2 (gaussianAreaMeasure alpha)) z =
              a n • (normalizedMonomialL2Vector alpha ha n :
                ℂ → ℂ) z := hs
          _ = a n * normalizedMonomial alpha n z := by
            rw [hz]
            simp only [smul_eq_mul]
      have hadd := Lp.coeFn_add
        (∑ k ∈ Finset.range n,
          a k • normalizedMonomialL2Vector alpha ha k)
        (a n • normalizedMonomialL2Vector alpha ha n)
      filter_upwards [ih, hlast, hadd] with z hn hlastz haddz
      simpa only [Finset.sum_range_succ, Pi.add_apply, hn, hlastz]
        using haddz

/-- The actual L² synthesis is represented almost everywhere by the
entire coherent-state power series, for every square-summable vector. -/
theorem coefficientSynthesisL2_ae_coherentEvaluation
    (alpha : ℝ) (ha : 0 < alpha)
    (a : lp (fun _ : ℕ => ℂ) 2) :
    ((coefficientSynthesisL2 alpha ha a :
        Lp ℂ 2 (gaussianAreaMeasure alpha)) : ℂ → ℂ)
      =ᵐ[gaussianAreaMeasure alpha]
        (fun z : ℂ => FockEvaluation.evaluation alpha ha z a) := by
  have hL2 : Tendsto
      (fun n : ℕ => ∑ k ∈ Finset.range n,
        a k • normalizedMonomialL2Vector alpha ha k)
      atTop (𝓝 (coefficientSynthesisL2 alpha ha a)) :=
    (coefficientSynthesisL2_hasSum alpha ha a).tendsto_sum_nat
  obtain ⟨ns, hns, hlim⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hL2).exists_seq_tendsto_ae'
  have hfinite : ∀ᵐ z ∂gaussianAreaMeasure alpha, ∀ n : ℕ,
      ((∑ k ∈ Finset.range n,
        a k • normalizedMonomialL2Vector alpha ha k :
          Lp ℂ 2 (gaussianAreaMeasure alpha)) : ℂ → ℂ) z =
      ∑ k ∈ Finset.range n,
        a k * normalizedMonomial alpha k z :=
    ae_all_iff.mpr (fun n =>
      coefficientPartialSumL2_ae_polynomial alpha ha a n)
  filter_upwards [hlim, hfinite] with z hlimz hfinz
  have hpoint : Tendsto
      (fun n : ℕ => ∑ k ∈ Finset.range n,
        a k * normalizedMonomial alpha k z)
      atTop (𝓝 (FockEvaluation.evaluation alpha ha z a)) :=
    (coefficientFockEvaluation_hasSum_normalizedMonomial alpha ha a z).tendsto_sum_nat
  have hpoint' : Tendsto
      (fun i : ℕ =>
        ((∑ k ∈ Finset.range (ns i),
          a k • normalizedMonomialL2Vector alpha ha k :
            Lp ℂ 2 (gaussianAreaMeasure alpha)) : ℂ → ℂ) z)
      atTop (𝓝 (FockEvaluation.evaluation alpha ha z a)) := by
    simpa only [hfinz] using hpoint.comp hns
  exact tendsto_nhds_unique hlimz hpoint'

/-- Every synthesized ℓ² Gaussian vector has the genuine entire
coherent-state evaluation as an almost-everywhere representative. -/
theorem coefficientSynthesisL2_mem_entireGaussianL2Submodule
    (alpha : ℝ) (ha : 0 < alpha)
    (a : lp (fun _ : ℕ => ℂ) 2) :
    coefficientSynthesisL2 alpha ha a ∈
      entireGaussianL2Submodule alpha := by
  refine ⟨(fun z : ℂ => FockEvaluation.evaluation alpha ha z a),
    FockEvaluation.differentiable_evaluation_complex alpha ha a, ?_⟩
  exact (coefficientSynthesisL2_ae_coherentEvaluation alpha ha a).symm

/-- The Gaussian closed polynomial span is contained in the
independently defined analytic entire-representative L² space. -/
theorem gaussianPolynomialClosure_le_entireGaussianL2Submodule
    (alpha : ℝ) (ha : 0 < alpha) :
    gaussianPolynomialClosure alpha ha ≤ entireGaussianL2Submodule alpha := by
  intro x hx
  have hx' : x ∈ LinearMap.range
      (coefficientSynthesisL2 alpha ha).toLinearMap := by
    rw [coefficientSynthesisL2_range_eq_closure_span alpha ha]
    exact hx
  obtain ⟨a, rfl⟩ := hx'
  exact coefficientSynthesisL2_mem_entireGaussianL2Submodule alpha ha a

#print axioms GegenbauerFock.GaussianArea.coefficientPartialSumL2_ae_polynomial
#print axioms GegenbauerFock.GaussianArea.coefficientSynthesisL2_ae_coherentEvaluation
#print axioms GegenbauerFock.GaussianArea.coefficientSynthesisL2_mem_entireGaussianL2Submodule
#print axioms GegenbauerFock.GaussianArea.gaussianPolynomialClosure_le_entireGaussianL2Submodule

end GegenbauerFock.GaussianArea
