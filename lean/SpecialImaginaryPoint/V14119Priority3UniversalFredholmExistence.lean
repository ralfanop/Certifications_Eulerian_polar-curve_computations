import SpecialImaginaryPoint.V14119Priority3UniversalCompressionTraceNorm
import SpecialImaginaryPoint.V14119Priority3DenseUniformCauchy
import SpecialImaginaryPoint.V14119Priority3ExpTraceNormEquicont

/-!
# Priority 3 — constructive universal CFC Schatten-S₁ Fredholm determinant

For EVERY genuine CFC-S₁ Hilbert operator T, possibly nonnormal,
nonnuclear-diagonal and nonselfadjoint, consider its genuine N×N
Hilbert compression Fredholm determinant D_N(T,z).

The certified finite-rank sector enjoys pointwise D_N convergence,
is dense in the true CFC S₁ trace norm, and the sharp uniform-in-N
trace-norm perturbation estimate implies pointwise equicontinuity.
The separately certified dense-equicontinuous complex Cauchy theorem
then proves D_N(T,z) converges for EVERY T and z.

We use the unique complex limit to define the ACTUAL universal
Fredholm determinant, and prove:
* finite Hilbert compressions converge to it;
* agreement with the intrinsic finite-rank Gram determinant;
* sharp dimension-free true CFC S₁ perturbation bound on ALL S₁;
* normalization at z=0.

The spectral-parameter holomorphy is NOT yet claimed here; it is
the final remaining analytic obligation after existence.
-/

noncomputable section

namespace Manuscript14Priority3.UniversalFredholmExistence

open Filter Topology
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.NuclearRankOne
open Manuscript14Priority3.FiniteRankFredholm
open Manuscript14Priority3.FiniteNuclearFredholm
open Manuscript14Priority3.FinsetNuclearReindex
open Manuscript14Priority3.UniversalCompressionTraceNorm
open Manuscript14Priority3.DenseUniformCauchy
open Manuscript14Priority3.ExpTraceNormEquicont

/-- Genuine finite-nuclear subset of the actual CFC Schatten-S₁ space,
using the exact canonical finiteNuclear m presentation. -/
def finiteSector : Set (ProbabilisticTheory.TraceClass H) :=
  {T | ∃ (m : ℕ) (u v : Fin m → H), T = finiteNuclear m u v}

/-- This finite-nuclear sector is dense in the full CFC-S₁ Banach
norm. No matrix compression or weak-topology approximation is used. -/
theorem finiteSector_dense : Dense finiteSector := by
  apply dense_iff_closure_eq.mpr
  apply Set.eq_univ_iff_forall.mpr
  intro T
  obtain ⟨w, u, v, _hcost, hlim, _hmass⟩ :=
    traceClass_exists_optimal_fin_presentations T
  apply mem_closure_of_tendsto hlim
  exact Filter.Eventually.of_forall
    (fun s : Finset w => (⟨s.card, finsetVectors s u,
        finsetVectors s v, rfl⟩ :
      finiteNuclear s.card (finsetVectors s u)
        (finsetVectors s v) ∈ finiteSector))

/-- Finite-rank genuine Hilbert-compression determinants converge
by the kernel-certified finite nuclear intrinsic Gram result. -/
theorem finiteDeterminant_cauchy_on_finiteSector
    (z : ℂ) (T : ProbabilisticTheory.TraceClass H)
    (hT : T ∈ finiteSector) :
    CauchySeq (fun N : ℕ => finiteDeterminant N T z) := by
  obtain ⟨m, u, v, hT⟩ := hT
  subst T
  exact (finiteNuclear_det_tendsto m u v z).cauchySeq

/-- Universal two-point estimate for all actual CFC-S₁ maps,
with a slightly enlarged exponential envelope to transform
the one-sided sharp increment estimate into a symmetrical
equicontinuity estimate. No dependence on N. -/
theorem finiteDeterminant_two_point_exp_bound
    (N : ℕ) (T S : ProbabilisticTheory.TraceClass H) (z : ℂ) :
    ‖finiteDeterminant N T z - finiteDeterminant N S z‖ ≤
      ((2 * ‖z‖) * ‖T - S‖) *
        Real.exp ((2 * ‖z‖) * (‖T‖ + ‖S‖)) := by
  have h := finiteDeterminant_global_traceNorm_perturbation
    N S (T - S) z
  have hadd : S + (T - S) = T := by abel
  rw [hadd] at h
  have htri : ‖T - S‖ ≤ ‖T‖ + ‖S‖ := norm_sub_le T S
  have hnonnegT : 0 ≤ ‖T‖ := norm_nonneg _
  have hnonnegS : 0 ≤ ‖S‖ := norm_nonneg _
  have hlin : ‖S‖ + ‖T - S‖ ≤
      2 * (‖T‖ + ‖S‖) := by linarith
  have hscale := mul_le_mul_of_nonneg_left hlin (norm_nonneg z)
  have hExp : Real.exp (‖z‖ * (‖S‖ + ‖T - S‖)) ≤
      Real.exp ((2 * ‖z‖) * (‖T‖ + ‖S‖)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [hscale]
  have hfactor : (‖z‖ * ‖T - S‖) ≤
      (2 * ‖z‖) * ‖T - S‖ := by
    nlinarith [mul_nonneg (norm_nonneg z) (norm_nonneg (T - S))]
  calc
    ‖finiteDeterminant N T z - finiteDeterminant N S z‖ ≤
        (‖z‖ * ‖T - S‖) *
          Real.exp (‖z‖ * (‖S‖ + ‖T - S‖)) := h
    _ ≤ (‖z‖ * ‖T - S‖) *
          Real.exp ((2 * ‖z‖) * (‖T‖ + ‖S‖)) :=
        mul_le_mul_of_nonneg_left hExp
          (mul_nonneg (norm_nonneg z) (norm_nonneg (T - S)))
    _ ≤ ((2 * ‖z‖) * ‖T - S‖) *
          Real.exp ((2 * ‖z‖) * (‖T‖ + ‖S‖)) :=
        mul_le_mul_of_nonneg_right hfactor (Real.exp_pos _).le

/-- The whole sequence of actual Hilbert compression determinants
is Cauchy, for EVERY CFC-S₁ operator and EVERY complex z.
The proof uses actual density and N-uniform equicontinuity. -/
theorem finiteDeterminant_cauchy_everywhere
    (z : ℂ) (T : ProbabilisticTheory.TraceClass H) :
    CauchySeq (fun N : ℕ => finiteDeterminant N T z) := by
  have hequi :=
    equicontinuity_of_exponential_norm_perturbation
      (fun N (X : ProbabilisticTheory.TraceClass H) =>
        finiteDeterminant N X z)
      (2 * ‖z‖) (by positivity)
      (fun N X Y => finiteDeterminant_two_point_exp_bound N X Y z)
  exact cauchySeq_everywhere_of_dense_equicontinuous
    finiteSector finiteSector_dense
    (fun N (X : ProbabilisticTheory.TraceClass H) =>
      finiteDeterminant N X z)
    (finiteDeterminant_cauchy_on_finiteSector z)
    hequi T

/-- Every actual CFC Schatten-S₁ operator admits a genuine complex
finite-Hilbert-compression determinant limit for every z. -/
theorem finiteDeterminant_complex_limit_exists
    (T : ProbabilisticTheory.TraceClass H) (z : ℂ) :
    ∃ L : ℂ, Tendsto
      (fun N : ℕ => finiteDeterminant N T z)
      atTop (𝓝 L) :=
  cauchySeq_tendsto_of_complete
    (finiteDeterminant_cauchy_everywhere z T)

/-- The universal Fredholm determinant on the ENTIRE genuine
CFC Schatten-S₁ ideal, defined as the true complex limit of
the actual finite Hilbert compression determinants. -/
def fredholmDet (T : ProbabilisticTheory.TraceClass H) (z : ℂ) : ℂ :=
  Classical.choose (finiteDeterminant_complex_limit_exists T z)

/-- The defining limit is certified for all trace-class maps,
including nonnormal and nonselfadjoint maps. -/
theorem finiteDeterminant_tendsto_fredholmDet
    (T : ProbabilisticTheory.TraceClass H) (z : ℂ) :
    Tendsto (fun N : ℕ => finiteDeterminant N T z)
      atTop (𝓝 (fredholmDet T z)) :=
  Classical.choose_spec (finiteDeterminant_complex_limit_exists T z)

/-- Agreement with the existing intrinsic finite-rank Gram Fredholm
determinant, independently of the nuclear presentation. -/
theorem fredholmDet_finiteNuclear (m : ℕ)
    (u v : Fin m → H) (z : ℂ) :
    fredholmDet (finiteNuclear m u v) z =
      Matrix.det (1 + z • gram m u v) := by
  exact tendsto_nhds_unique
    (finiteDeterminant_tendsto_fredholmDet
      (finiteNuclear m u v) z)
    (finiteNuclear_det_tendsto m u v z)

/-- The SHARP dimension-independent true trace-norm perturbation
bound for the UNIVERSAL genuine CFC-S₁ Fredholm determinant,
for arbitrary nonnormal trace-class Hilbert operators. -/
theorem fredholmDet_add_traceNorm_bound
    (T R : ProbabilisticTheory.TraceClass H) (z : ℂ) :
    ‖fredholmDet (T + R) z - fredholmDet T z‖ ≤
      (‖z‖ * ‖R‖) * Real.exp (‖z‖ * (‖T‖ + ‖R‖)) := by
  have ht :
      Tendsto (fun N : ℕ =>
        finiteDeterminant N (T + R) z -
          finiteDeterminant N T z) atTop
        (𝓝 (fredholmDet (T + R) z - fredholmDet T z)) :=
    (finiteDeterminant_tendsto_fredholmDet (T + R) z).sub
      (finiteDeterminant_tendsto_fredholmDet T z)
  exact le_of_tendsto ht.norm <|
    Filter.Eventually.of_forall
      (fun N => finiteDeterminant_global_traceNorm_perturbation N T R z)

/-- Fredholm normalization at spectral parameter zero on ALL S₁. -/
theorem fredholmDet_zero
    (T : ProbabilisticTheory.TraceClass H) :
    fredholmDet T 0 = 1 := by
  have hunit : ∀ N : ℕ, finiteDeterminant N T 0 = 1 := by
    intro N
    simp [finiteDeterminant]
  have hconst : Tendsto
      (fun N : ℕ => finiteDeterminant N T 0)
      atTop (𝓝 (1 : ℂ)) := by
    simpa only [hunit] using (tendsto_const_nhds : Tendsto
      (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 1))
  exact tendsto_nhds_unique
    (finiteDeterminant_tendsto_fredholmDet T 0)
    hconst

#print axioms Manuscript14Priority3.UniversalFredholmExistence.finiteSector_dense
#print axioms Manuscript14Priority3.UniversalFredholmExistence.finiteDeterminant_cauchy_on_finiteSector
#print axioms Manuscript14Priority3.UniversalFredholmExistence.finiteDeterminant_two_point_exp_bound
#print axioms Manuscript14Priority3.UniversalFredholmExistence.finiteDeterminant_cauchy_everywhere
#print axioms Manuscript14Priority3.UniversalFredholmExistence.finiteDeterminant_complex_limit_exists
#print axioms Manuscript14Priority3.UniversalFredholmExistence.finiteDeterminant_tendsto_fredholmDet
#print axioms Manuscript14Priority3.UniversalFredholmExistence.fredholmDet_finiteNuclear
#print axioms Manuscript14Priority3.UniversalFredholmExistence.fredholmDet_add_traceNorm_bound
#print axioms Manuscript14Priority3.UniversalFredholmExistence.fredholmDet_zero

end Manuscript14Priority3.UniversalFredholmExistence
