import Mathlib
import Manuscript13.EllisParsevalTonelli20261126

/-! M13 Corollary 4.12 (75)–(76).
For an orthonormal eigenbasis of the actual real integral Gram operator
from #633, the eigenvalues are proved nonnegative and summable, with
the exact trace; the finite products converge to the determinant
expression and satisfy the strict manuscript bound. Existence of
such an eigenbasis and identification with the complex differential
resolvent are separate obligations. No arbitrary eigenvalue trace
or summability hypothesis is used.
-/
open Filter MeasureTheory
open scoped ENNReal Topology
namespace Manuscript13.EllisFredholmProduct20261127
noncomputable section
open Manuscript13.EllisGramKernelOperator20261124
open Manuscript13.EllisParsevalTonelli20261126
open Manuscript13.EllisBirman20261124 (spectralDet det_trace_specialization)

theorem eigen_diagonal (a κ : ℝ) (ha : 0 < a) (hk : 0 < κ)
    (e : HilbertBasis ℕ ℝ H) (eig : ℕ → ℝ)
    (he : ∀ i, gramOperator a κ ha hk (e i) = eig i • e i) (i : ℕ) :
    inner ℝ (gramOperator a κ ha hk (e i)) (e i) = eig i := by
  rw [he, real_inner_smul_left, real_inner_self_eq_norm_sq, e.orthonormal.norm_eq_one i]
  ring

theorem eigen_nonneg (a κ : ℝ) (ha : 0 < a) (hk : 0 < κ)
    (e : HilbertBasis ℕ ℝ H) (eig : ℕ → ℝ)
    (he : ∀ i, gramOperator a κ ha hk (e i) = eig i • e i) (i : ℕ) :
    0 ≤ eig i := by
  rw [← eigen_diagonal a κ ha hk e eig he i]
  exact gramOperator_nonneg a κ ha hk (e i)

theorem eigen_summable (a κ : ℝ) (ha : 0 < a) (hk : 0 < κ)
    (e : HilbertBasis ℕ ℝ H) (eig : ℕ → ℝ)
    (he : ∀ i, gramOperator a κ ha hk (e i) = eig i • e i) :
    Summable eig := by
  have h := gram_diagonal_summable a κ ha hk e
  simpa only [eigen_diagonal a κ ha hk e eig he] using h

theorem eigen_trace (a κ : ℝ) (ha : 0 < a) (hk : 0 < κ)
    (e : HilbertBasis ℕ ℝ H) (eig : ℕ → ℝ)
    (he : ∀ i, gramOperator a κ ha hk (e i) = eig i • e i) :
    (∑' i, eig i) = Real.pi/(4*a*κ) := by
  have h := gram_diagonal_trace a κ ha hk e
  simp_rw [eigen_diagonal a κ ha hk e eig he] at h
  rw [← ENNReal.ofReal_tsum_of_nonneg (eigen_nonneg a κ ha hk e eig he)
    (eigen_summable a κ ha hk e eig he)] at h
  exact (ENNReal.ofReal_eq_ofReal_iff
    (tsum_nonneg (eigen_nonneg a κ ha hk e eig he)) (by positivity)).1 h

theorem log_summable (eig : ℕ → ℝ) (hn : ∀ i, 0 ≤ eig i) (hs : Summable eig) :
    Summable (fun i => Real.log (1 + eig i)) := by
  apply Summable.of_nonneg_of_le
  · intro i
    exact Real.log_nonneg (by linarith [hn i])
  · intro i
    have h := Real.log_le_sub_one_of_pos (show 0 < 1 + eig i by linarith [hn i])
    linarith
  · exact hs

theorem finite_product_eq (eig : ℕ → ℝ) (hn : ∀ i, 0 ≤ eig i) (s : Finset ℕ) :
    Real.exp (∑ i ∈ s, Real.log (1 + eig i)) = ∏ i ∈ s, (1 + eig i) := by
  rw [Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i hi
  exact Real.exp_log (by linarith [hn i])

theorem hasProd_spectralDet (eig : ℕ → ℝ) (hn : ∀ i, 0 ≤ eig i)
    (hs : Summable eig) : HasProd (fun i => 1 + eig i) (spectralDet eig) := by
  have h := (Real.continuous_exp.continuousAt.tendsto).comp
    (log_summable eig hn hs).hasSum
  change Tendsto (fun s : Finset ℕ => ∏ i ∈ s, (1 + eig i))
    atTop (nhds (spectralDet eig))
  change Tendsto (fun s : Finset ℕ => Real.exp (∑ i ∈ s, Real.log (1 + eig i)))
    atTop (nhds (spectralDet eig)) at h
  simpa only [finite_product_eq eig hn] using h

theorem gram_eigen_product (a κ : ℝ) (ha : 0 < a) (hk : 0 < κ)
    (e : HilbertBasis ℕ ℝ H) (eig : ℕ → ℝ)
    (he : ∀ i, gramOperator a κ ha hk (e i) = eig i • e i) :
    HasProd (fun i => 1 + eig i) (spectralDet eig) ∧
      1 < spectralDet eig ∧ spectralDet eig ≤ Real.exp (Real.pi/(4*a*κ)) := by
  exact ⟨hasProd_spectralDet eig (eigen_nonneg a κ ha hk e eig he)
    (eigen_summable a κ ha hk e eig he),
    det_trace_specialization a κ ha hk eig (eigen_nonneg a κ ha hk e eig he)
      (eigen_summable a κ ha hk e eig he) (eigen_trace a κ ha hk e eig he)⟩

end
end Manuscript13.EllisFredholmProduct20261127
#print axioms Manuscript13.EllisFredholmProduct20261127.eigen_diagonal
#print axioms Manuscript13.EllisFredholmProduct20261127.eigen_nonneg
#print axioms Manuscript13.EllisFredholmProduct20261127.eigen_summable
#print axioms Manuscript13.EllisFredholmProduct20261127.eigen_trace
#print axioms Manuscript13.EllisFredholmProduct20261127.log_summable
#print axioms Manuscript13.EllisFredholmProduct20261127.finite_product_eq
#print axioms Manuscript13.EllisFredholmProduct20261127.hasProd_spectralDet
#print axioms Manuscript13.EllisFredholmProduct20261127.gram_eigen_product
