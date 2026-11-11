import SpecialImaginaryPoint.V14119Priority3FiniteCompressionTwoFamilyBound
import SpecialImaginaryPoint.V14119Priority3FinsetNuclearReindex
import SpecialImaginaryPoint.V14119Priority3TwoNetBoundLimit

/-!
# Priority 3 — UNCONDITIONAL true CFC-S₁ perturbation of every genuine Hilbert compression determinant

This theorem uses the kernel-certified:
* sharp dimension-free finite-nuclear perturbation of actual N-dimensional
  Hilbert compression determinants, valid for any N;
* a canonical nuclear representation of EVERY CFC Schatten-S₁
  map with true optimal total nuclear mass and a directed net of
  finite Fin m presentations with each mass <= the actual trace norm;
* a rigorous two-independent-net limit lemma for continuous
  scalar functionals.

Consequently, for EVERY actual CFC-S₁ Hilbert operator T,R and EVERY
compression dimension N (not just finite-rank operators),
  |D_N(T+R,z)-D_N(T,z)|
    <= |z| ||R||_1 exp(|z|( ||T||_1+||R||_1)).
This is unconditional, dimension-independent, complex, nonnormal,
and nonselfadjoint. It DOES NOT yet assert existence of a universal
infinite determinant: that requires convergence of D_N(T,z) as N→∞
and holomorphy of the resulting limit.
-/

set_option maxHeartbeats 2000000

noncomputable section

namespace Manuscript14Priority3.UniversalCompressionTraceNorm

open Filter Topology
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.NuclearRankOne
open Manuscript14Priority3.FiniteRankFredholm
open Manuscript14Priority3.FiniteNuclearFredholm
open Manuscript14Priority3.FiniteCompressionTwoFamilyBound
open Manuscript14Priority3.FinsetNuclearReindex
open Manuscript14Priority3.TwoNetBoundLimit

/-- SHARP, true CFC Schatten-S₁ trace-norm perturbation
inequality for the genuine finite Hilbert compression determinant,
uniformly in N, without finite optimality hypotheses. -/
theorem finiteDeterminant_global_traceNorm_perturbation
    (N : ℕ) (T R : ProbabilisticTheory.TraceClass H) (z : ℂ) :
    ‖finiteDeterminant N (T + R) z - finiteDeterminant N T z‖ ≤
      (‖z‖ * ‖R‖) * Real.exp (‖z‖ * (‖T‖ + ‖R‖)) := by
  obtain ⟨w, u, v, _hcost, hlimT, hmassT⟩ :=
    traceClass_exists_optimal_fin_presentations T
  obtain ⟨q, a, d, _hcostR, hlimR, hmassR⟩ :=
    traceClass_exists_optimal_fin_presentations R
  let A : Finset w → ProbabilisticTheory.TraceClass H :=
    fun s => finiteNuclear s.card (finsetVectors s u) (finsetVectors s v)
  let B : Finset q → ProbabilisticTheory.TraceClass H :=
    fun t => finiteNuclear t.card (finsetVectors t a) (finsetVectors t d)
  have hA : Tendsto A atTop (𝓝 T) := hlimT
  have hB : Tendsto B atTop (𝓝 R) := hlimR
  have hpair (s : Finset w) (t : Finset q) :
      ‖finiteDeterminant N (A s + B t) z -
        finiteDeterminant N (A s) z‖ ≤
        (‖z‖ * ‖R‖) * Real.exp (‖z‖ * (‖T‖ + ‖R‖)) := by
    let MA : ℝ := ∑ i : Fin s.card,
      ‖finsetVectors s u i‖ * ‖finsetVectors s v i‖
    let MB : ℝ := ∑ j : Fin t.card,
      ‖finsetVectors t a j‖ * ‖finsetVectors t d j‖
    have hmA : MA ≤ ‖T‖ := hmassT s
    have hmB : MB ≤ ‖R‖ := hmassR t
    have hbase : ‖finiteDeterminant N (A s + B t) z -
        finiteDeterminant N (A s) z‖ ≤
        (‖z‖ * MB) * Real.exp (‖z‖ * (MA + MB)) :=
      finiteDeterminant_two_family_norm_le_exp
        N s.card t.card
        (finsetVectors s u) (finsetVectors s v)
        (finsetVectors t a) (finsetVectors t d) z
    have hpref : ‖z‖ * MB ≤ ‖z‖ * ‖R‖ :=
      mul_le_mul_of_nonneg_left hmB (norm_nonneg z)
    have hexp : Real.exp (‖z‖ * (MA + MB)) ≤
        Real.exp (‖z‖ * (‖T‖ + ‖R‖)) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left (add_le_add hmA hmB) (norm_nonneg z)
    calc
      ‖finiteDeterminant N (A s + B t) z -
        finiteDeterminant N (A s) z‖ ≤
          (‖z‖ * MB) * Real.exp (‖z‖ * (MA + MB)) := hbase
      _ ≤ (‖z‖ * ‖R‖) * Real.exp (‖z‖ * (MA + MB)) :=
        mul_le_mul_of_nonneg_right hpref (Real.exp_pos _).le
      _ ≤ (‖z‖ * ‖R‖) * Real.exp (‖z‖ * (‖T‖ + ‖R‖)) :=
        mul_le_mul_of_nonneg_left hexp
          (mul_nonneg (norm_nonneg z) (norm_nonneg R))
  exact continuous_complex_two_net_perturbation_bound
    (fun X : ProbabilisticTheory.TraceClass H => finiteDeterminant N X z)
    (finiteDeterminant_continuous N z)
    A B T R hA hB
    ((‖z‖ * ‖R‖) * Real.exp (‖z‖ * (‖T‖ + ‖R‖)))
    hpair

#print axioms Manuscript14Priority3.UniversalCompressionTraceNorm.finiteDeterminant_global_traceNorm_perturbation

end Manuscript14Priority3.UniversalCompressionTraceNorm
