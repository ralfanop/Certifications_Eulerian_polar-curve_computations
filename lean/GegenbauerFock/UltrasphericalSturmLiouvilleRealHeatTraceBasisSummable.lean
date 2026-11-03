import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatLimitHilbertCoordinates
import GegenbauerFock.UltrasphericalSturmLiouvilleResolventRealSchattenBasis
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# V007 — heat spectral summability and actual real-L² basis trace

At strictly positive time s, the Gegenbauer heat multipliers

  exp(-s n(n+2 lambda))

are summable for every lambda>0. The basic bound n<=n(n+2lambda)
for each integer n>=0 reduces summability to an exponential geometric
series. The very same multipliers are the diagonal inner products of
the ACTUAL strongly constructed heat operator on the complete
orthonormal real weighted-L² Gegenbauer basis.

We certify the actual-operator positive trace summability and the
actual-basis Hilbert–Schmidt criterion. These named basis criteria
are not silently identified with an independently defined Schatten
ideal; such an identification would require its own bridge.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory InnerProductSpace

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- The Gegenbauer eigenfrequency dominates its degree when lambda>0. -/
theorem sturmHeatFrequency_ge_degree
    (lam : ℝ) (hlam : 0 < lam) (n : ℕ) :
    (n : ℝ) ≤ (n : ℝ) * ((n : ℝ) + 2 * lam) := by
  by_cases hn : n = 0
  · subst n
    norm_num
  · have hnNat : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hnOne : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnNat
    have hnPos : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hfactor : (1 : ℝ) ≤ (n : ℝ) + 2 * lam := by
      linarith
    calc
      (n : ℝ) = (n : ℝ) * 1 := by ring
      _ ≤ (n : ℝ) * ((n : ℝ) + 2 * lam) :=
        mul_le_mul_of_nonneg_left hfactor hnPos

/-- Every strictly positive-time heat multiplier series is summable. -/
theorem sturmRealHeat_spectral_multiplier_summable
    (lam s : ℝ) (hlam : 0 < lam) (hs : 0 < s) :
    Summable (fun n : ℕ =>
      Real.exp (-s * ((n : ℝ) * ((n : ℝ) + 2 * lam)))) := by
  exact Real.summable_exp_nat_mul_of_ge (neg_lt_zero.mpr hs)
    (fun n => sturmHeatFrequency_ge_degree lam hlam n)

/-- Nonnegative heat eigenvalues bounded by one at nonnegative time. -/
theorem sturmRealHeat_spectral_multiplier_mem_unit
    (lam s : ℝ) (hlam : 0 < lam) (hs : 0 ≤ s) (n : ℕ) :
    0 ≤ Real.exp (-s * ((n : ℝ) * ((n : ℝ) + 2 * lam))) ∧
    Real.exp (-s * ((n : ℝ) * ((n : ℝ) + 2 * lam))) ≤ 1 := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hf : 0 ≤ ((n : ℝ) + 2 * lam) := by linarith
  have hw : 0 ≤ (n : ℝ) * ((n : ℝ) + 2 * lam) := mul_nonneg hn hf
  have harg : -s * ((n : ℝ) * ((n : ℝ) + 2 * lam)) ≤ 0 := by
    nlinarith [mul_nonneg hs hw]
  refine ⟨(Real.exp_pos _).le, ?_⟩
  have he := Real.exp_le_exp.mpr harg
  simpa only [Real.exp_zero] using he

/-- The exact real trace diagonal of the actual full-L² heat operator. -/
theorem sturmRealHeat_actual_basis_inner_diagonal
    (lam s : ℝ) (hlam : 0 < lam) (hs : 0 ≤ s) (n : ℕ) :
    inner ℝ
      ((sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam) n)
      (sturmRealHeatLimitCLM lam hlam s hs
        ((sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam) n)) =
    Real.exp (-s * ((n : ℝ) * ((n : ℝ) + 2 * lam))) := by
  let b := sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam
  have heig :
      sturmRealHeatLimitCLM lam hlam s hs (b n) =
        Real.exp (-s * ((n : ℝ) * ((n : ℝ) + 2 * lam))) • b n := by
    exact sturmRealHeatLimitCLM_normalized_Gegenbauer_eigen lam hlam s hs n
  have hnorm : ‖b n‖ = 1 := b.orthonormal.norm_eq_one n
  change inner ℝ (b n) (sturmRealHeatLimitCLM lam hlam s hs (b n)) = _
  rw [heig, real_inner_smul_right, real_inner_self_eq_norm_sq, hnorm]
  ring

/-- The ACTUAL heat operator meets the real positive-S1 basis criterion. -/
theorem sturmRealHeat_positive_trace_diagonal_summable
    (lam s : ℝ) (hlam : 0 < lam) (hs : 0 < s) :
    IsRealPositiveTraceSummableOnBasis
      (sturmRealHeatLimitCLM lam hlam s (le_of_lt hs))
      (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam) := by
  unfold IsRealPositiveTraceSummableOnBasis
  exact (sturmRealHeat_spectral_multiplier_summable lam s hlam hs).congr
    (fun n =>
      (sturmRealHeat_actual_basis_inner_diagonal lam s hlam
        (le_of_lt hs) n).symm)

/-- Positive-time heat spectral multipliers have summable squares. -/
theorem sturmRealHeat_spectral_multiplier_sq_summable
    (lam s : ℝ) (hlam : 0 < lam) (hs : 0 < s) :
    Summable (fun n : ℕ =>
      (Real.exp (-s * ((n : ℝ) * ((n : ℝ) + 2 * lam)))) ^ 2) := by
  let beta : ℕ → ℝ := fun n =>
    Real.exp (-s * ((n : ℝ) * ((n : ℝ) + 2 * lam)))
  have hsum : Summable beta :=
    sturmRealHeat_spectral_multiplier_summable lam s hlam hs
  have hpoint (n : ℕ) : beta n ^ 2 ≤ beta n := by
    obtain ⟨hzero, hone⟩ :=
      sturmRealHeat_spectral_multiplier_mem_unit lam s hlam hs.le n
    have hprod : 0 ≤ beta n * (1 - beta n) :=
      mul_nonneg hzero (sub_nonneg.mpr hone)
    nlinarith
  exact Summable.of_nonneg_of_le
    (fun n => sq_nonneg (beta n)) hpoint hsum

/-- The squared L² norm of the actual heat image of any unit basis mode. -/
theorem sturmRealHeat_actual_basis_norm_sq
    (lam s : ℝ) (hlam : 0 < lam) (hs : 0 ≤ s) (n : ℕ) :
    ‖sturmRealHeatLimitCLM lam hlam s hs
      ((sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam) n)‖ ^ 2 =
    (Real.exp (-s * ((n : ℝ) * ((n : ℝ) + 2 * lam)))) ^ 2 := by
  let b := sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam
  have heig :
      sturmRealHeatLimitCLM lam hlam s hs (b n) =
        Real.exp (-s * ((n : ℝ) * ((n : ℝ) + 2 * lam))) • b n := by
    exact sturmRealHeatLimitCLM_normalized_Gegenbauer_eigen lam hlam s hs n
  have hnorm : ‖b n‖ = 1 := b.orthonormal.norm_eq_one n
  change ‖sturmRealHeatLimitCLM lam hlam s hs (b n)‖ ^ 2 = _
  rw [heig, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    hnorm, mul_one]

/-- The ACTUAL positive-time heat operator meets the real S2 basis
Hilbert–Schmidt criterion on the complete weighted-real-L² basis. -/
theorem sturmRealHeat_isHS_on_actual_basis
    (lam s : ℝ) (hlam : 0 < lam) (hs : 0 < s) :
    IsRealHilbertSchmidtOnBasis
      (sturmRealHeatLimitCLM lam hlam s (le_of_lt hs))
      (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam) := by
  unfold IsRealHilbertSchmidtOnBasis
  exact (sturmRealHeat_spectral_multiplier_sq_summable lam s hlam hs).congr
    (fun n => (sturmRealHeat_actual_basis_norm_sq lam s hlam
      (le_of_lt hs) n).symm)

/-- The actual heat diagonal trace series equals the spectral multiplier
series, for every positive time. -/
theorem sturmRealHeat_actual_basis_trace_eq_spectral_series
    (lam s : ℝ) (hlam : 0 < lam) (hs : 0 < s) :
    (∑' n : ℕ, inner ℝ
      ((sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam) n)
      (sturmRealHeatLimitCLM lam hlam s (le_of_lt hs)
        ((sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam) n))) =
    ∑' n : ℕ, Real.exp (-s * ((n : ℝ) * ((n : ℝ) + 2 * lam))) := by
  apply tsum_congr
  intro n
  exact sturmRealHeat_actual_basis_inner_diagonal lam s hlam
    (le_of_lt hs) n

#print axioms GegenbauerFock.Ultraspherical.sturmRealHeat_spectral_multiplier_summable
#print axioms GegenbauerFock.Ultraspherical.sturmRealHeat_positive_trace_diagonal_summable
#print axioms GegenbauerFock.Ultraspherical.sturmRealHeat_isHS_on_actual_basis
#print axioms GegenbauerFock.Ultraspherical.sturmRealHeat_actual_basis_trace_eq_spectral_series

end GegenbauerFock.Ultraspherical
