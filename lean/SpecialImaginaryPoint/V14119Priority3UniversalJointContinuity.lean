import SpecialImaginaryPoint.V14119Priority3UniversalFredholmEntire
import SpecialImaginaryPoint.V14119Priority3UniversalTraceNormContinuity
import SpecialImaginaryPoint.V14119Priority3SpectralEquicontinuity

/-!
# Priority 3 — joint CFC-S₁ / complex-spectral continuity and zero-free neighborhood

The universal genuine Hilbert trace-class Fredholm determinant is
already kernel-certified to be continuous in the TRUE Schatten-S₁ norm
for fixed z and entire in z for fixed T. This module strengthens both
separate statements by proving:
* the sharp *spectral parameter* increment estimate on the actual
  infinite determinant, by taking the genuine compression limit;
* joint continuity of (T,z) ↦ det(I+zT) on S₁(H)×ℂ;
* a certified zero-free criterion near the spectral origin.

There is no normality, selfadjointness, positivity, finite-rank,
invertibility, or exact finite optimality assumption. These are
operatorial, not merely scalar Gram, results.
-/

noncomputable section

namespace Manuscript14Priority3.UniversalJointContinuity

open Filter Topology
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.FiniteRankFredholm
open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.SpectralEquicontinuity
open Manuscript14Priority3.UniversalTraceNormContinuity

/-- The sharp dimension-independent spectral parameter perturbation
bound survives the genuine infinite Hilbert compression limit. -/
theorem fredholmDet_spectral_diff_norm_le
    (T : ProbabilisticTheory.TraceClass H) (z w : ℂ) :
    ‖fredholmDet T z - fredholmDet T w‖ ≤
      (‖z - w‖ * ‖T‖) *
        Real.exp ((‖w‖ + ‖z - w‖) * ‖T‖) := by
  have hlim :
      Tendsto (fun N : ℕ =>
        ‖finiteDeterminant N T z - finiteDeterminant N T w‖)
        atTop (𝓝 (‖fredholmDet T z - fredholmDet T w‖)) :=
    ((finiteDeterminant_tendsto_fredholmDet T z).sub
      (finiteDeterminant_tendsto_fredholmDet T w)).norm
  exact le_of_tendsto hlim (Filter.Eventually.of_forall
    (fun N : ℕ => finiteDeterminant_spectral_diff_norm_le N T z w))

/-- JOINT norm topology: the universal CFC-S₁ Fredholm determinant
is continuous simultaneously in the trace-class operator and the
complex spectral parameter, not merely separately continuous. -/
theorem fredholmDet_joint_continuous :
    Continuous (fun p : ProbabilisticTheory.TraceClass H × ℂ =>
      fredholmDet p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro ⟨T, z⟩
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  let φ : ProbabilisticTheory.TraceClass H × ℂ → ℝ := fun p =>
    (‖p.2 - z‖ * ‖p.1‖) *
      Real.exp ((‖z‖ + ‖p.2 - z‖) * ‖p.1‖) +
    (‖z‖ * ‖p.1 - T‖) *
      Real.exp (‖z‖ * (‖T‖ + ‖p.1 - T‖))
  have htw : Continuous (fun p : ProbabilisticTheory.TraceClass H × ℂ =>
      ‖p.2 - z‖) :=
    continuous_norm.comp (continuous_snd.sub continuous_const)
  have htn : Continuous (fun p : ProbabilisticTheory.TraceClass H × ℂ =>
      ‖p.1‖) :=
    continuous_norm.comp continuous_fst
  have htm : Continuous (fun p : ProbabilisticTheory.TraceClass H × ℂ =>
      ‖p.1 - T‖) :=
    continuous_norm.comp (continuous_fst.sub continuous_const)
  have ha : Continuous (fun p : ProbabilisticTheory.TraceClass H × ℂ =>
      (‖p.2 - z‖ * ‖p.1‖) *
        Real.exp ((‖z‖ + ‖p.2 - z‖) * ‖p.1‖)) :=
    (htw.mul htn).mul
      (Real.continuous_exp.comp
        ((continuous_const.add htw).mul htn))
  have hb : Continuous (fun p : ProbabilisticTheory.TraceClass H × ℂ =>
      (‖z‖ * ‖p.1 - T‖) *
        Real.exp (‖z‖ * (‖T‖ + ‖p.1 - T‖))) :=
    (continuous_const.mul htm).mul
      (Real.continuous_exp.comp
        (continuous_const.mul (continuous_const.add htm)))
  have hφ : Continuous φ := ha.add hb
  have hφzero : φ (T, z) = 0 := by simp [φ]
  have hopen : IsOpen {p : ProbabilisticTheory.TraceClass H × ℂ | φ p < ε} :=
    isOpen_lt hφ continuous_const
  have hp : (T, z) ∈
      {p : ProbabilisticTheory.TraceClass H × ℂ | φ p < ε} := by
    change φ (T, z) < ε
    rw [hφzero]
    exact hε
  obtain ⟨δ, hδ, hball⟩ :=
    (Metric.isOpen_iff.mp hopen) (T, z) hp
  refine ⟨δ, hδ, ?_⟩
  intro ⟨S, w⟩ hSW
  have hballSW : (S, w) ∈ Metric.ball (T, z) δ := by
    change dist (S, w) (T, z) < δ
    simpa only [dist_comm] using hSW
  have hsmall : φ (S, w) < ε := hball hballSW
  have hspec := fredholmDet_spectral_diff_norm_le S w z
  have htrace := fredholmDet_add_traceNorm_bound T (S - T) z
  have hadd : T + (S - T) = S := by abel
  rw [hadd] at htrace
  have hsum :
      ‖fredholmDet S w - fredholmDet T z‖ ≤ φ (S, w) := by
    calc
      ‖fredholmDet S w - fredholmDet T z‖ =
          ‖(fredholmDet S w - fredholmDet S z) +
            (fredholmDet S z - fredholmDet T z)‖ := by
        congr 1
        ring
      _ ≤ ‖fredholmDet S w - fredholmDet S z‖ +
          ‖fredholmDet S z - fredholmDet T z‖ := norm_add_le _ _
      _ ≤ φ (S, w) := by
        exact add_le_add hspec htrace
  calc
    dist (fredholmDet S w) (fredholmDet T z) =
        ‖fredholmDet S w - fredholmDet T z‖ :=
      dist_eq_norm (fredholmDet S w) (fredholmDet T z)
    _ ≤ φ (S, w) := hsum
    _ < ε := hsmall

/-- Nonvanishing of the universal complex Fredholm determinant in
a precise trace-norm controlled neighborhood of z=0. -/
theorem fredholmDet_ne_zero_of_small_spectral_mass
    (T : ProbabilisticTheory.TraceClass H) (z : ℂ)
    (hsmall : (‖z‖ * ‖T‖) *
        Real.exp (‖z‖ * ‖T‖) < 1) :
    fredholmDet T z ≠ 0 := by
  have hdiff := fredholmDet_spectral_diff_norm_le T z 0
  rw [fredholmDet_zero] at hdiff
  simp only [sub_zero, norm_zero, zero_add] at hdiff
  intro hz
  rw [hz] at hdiff
  norm_num at hdiff
  rw [ProbabilisticTheory.TraceClass.norm_eq_genuineTraceNorm] at hsmall
  exact (not_lt_of_ge hdiff) hsmall

#print axioms Manuscript14Priority3.UniversalJointContinuity.fredholmDet_spectral_diff_norm_le
#print axioms Manuscript14Priority3.UniversalJointContinuity.fredholmDet_joint_continuous
#print axioms Manuscript14Priority3.UniversalJointContinuity.fredholmDet_ne_zero_of_small_spectral_mass

end Manuscript14Priority3.UniversalJointContinuity
