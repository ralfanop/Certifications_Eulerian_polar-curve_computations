import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatFockGramTraceObstruction

/-!
# V007 — an entire positive-time no-go interval for actual heat/Fock Gram

For lambda=1/2, alpha=1, the genuine complex Fock Gram trace is <11/10.
The actual real Legendre heat trace is >=9/5 at every 0<s<=1/10,
by monotonicity of positive heat multipliers and the already certified
two-mode lower bound at time 1/10. Therefore no real-linear map can
both preserve complete normalized eigenbases and intertwine the actual
operators, throughout this nonempty interval.

This does not exclude weaker maps or all other positive times.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory InnerProductSpace

private abbrev HR (lam : ℝ) := Lp ℝ 2 (measure lam)
private abbrev HC (lam : ℝ) := Lp ℂ 2 (measure lam)

/-- Positive heat trace monotonicity extends the 9/5 lower bound
from s=1/10 to every 0<s<=1/10. -/
theorem legendre_heat_smallTime_trace_ge_nine_fifths
    (s : ℝ) (hs : 0 < s) (hsmax : s ≤ 1 / 10) :
    (9 / 5 : ℝ) ≤
      ∑' n : ℕ,
        Real.exp (-s * ((n : ℝ) * ((n : ℝ) + 2 * (1 / 2 : ℝ)))) := by
  let omega : ℕ → ℝ := fun n => (n : ℝ) * ((n : ℝ) + 1)
  let betaS : ℕ → ℝ := fun n => Real.exp (-s * omega n)
  let betaFixed : ℕ → ℝ := fun n =>
    Real.exp (-(1 / 10 : ℝ) * omega n)
  have hsS : Summable betaS := by
    simpa [betaS, omega] using
      (sturmRealHeat_spectral_multiplier_summable
        (1 / 2) s (by norm_num) hs)
  have hsFixed : Summable betaFixed := by
    simpa [betaFixed, omega] using
      (sturmRealHeat_spectral_multiplier_summable
        (1 / 2) (1 / 10) (by norm_num) (by norm_num))
  have hpoint (n : ℕ) : betaFixed n ≤ betaS n := by
    have hn : 0 ≤ omega n := by
      dsimp [omega]
      positivity
    have hdiff : 0 ≤ ((1 / 10 : ℝ) - s) * omega n :=
      mul_nonneg (by linarith) hn
    have harg : -(1 / 10 : ℝ) * omega n ≤ -s * omega n := by
      nlinarith
    exact Real.exp_monotone harg
  have hmon :
      (∑' n : ℕ, betaFixed n) ≤ (∑' n : ℕ, betaS n) :=
    hsFixed.tsum_le_tsum hpoint hsS
  have hstart : (9 / 5 : ℝ) ≤ ∑' n : ℕ, betaFixed n := by
    simpa [betaFixed, omega] using
      legendre_heat_trace_one_tenth_ge_nine_fifths
  have hresult : (9 / 5 : ℝ) ≤ ∑' n : ℕ, betaS n :=
    hstart.trans hmon
  simpa [betaS, omega] using hresult

/-- No basis-preserving real-linear intertwiner from the actual
Legendre heat H_s to the actual complex Fock Gram G_(1/2,1)
for ANY 0<s<=1/10. -/
theorem no_legendre_heat_small_positive_time_to_fock_gram_basis_intertwiner
    (s : ℝ) (hs : 0 < s) (hsmax : s ≤ 1 / 10) :
    ¬ ∃ (bC : HilbertBasis ℕ ℂ (HC (1 / 2)))
        (J : HR (1 / 2) →ₗ[ℝ] HC (1 / 2)),
        (∀ n : ℕ,
          J ((sturmMonicEigenCandidate_realL2_hilbertBasis
            (1 / 2) (by norm_num)) n) = bC n) ∧
        (∀ f : HR (1 / 2),
          GegenbauerFock.GeneralUltrasphericalFock.gram
              (1 / 2) 1 (by norm_num) (by norm_num) (J f) =
            J (sturmRealHeatLimitCLM
              (1 / 2) (by norm_num) s (le_of_lt hs) f)) := by
  have hLow := legendre_heat_smallTime_trace_ge_nine_fifths s hs hsmax
  have hUp := eulerian_half_one_fock_gram_trace_lt_eleven_tenths
  have hgap :
      (∑' n : ℕ,
        Real.exp (-s *
          ((n : ℝ) * ((n : ℝ) + 2 * (1 / 2 : ℝ))))) ≠
        KummerCoefficients.kummerSeries (1 / 2) (1 / 4) :=
    ne_of_gt (lt_of_lt_of_le (lt_trans hUp (by norm_num)) hLow)
  exact no_heat_fockGram_basis_intertwiner_of_trace_gap
    (1 / 2) 1 s (by norm_num) (by norm_num) hs
    (by simpa only [mul_one] using hgap)

#print axioms GegenbauerFock.Ultraspherical.legendre_heat_smallTime_trace_ge_nine_fifths
#print axioms GegenbauerFock.Ultraspherical.no_legendre_heat_small_positive_time_to_fock_gram_basis_intertwiner

end GegenbauerFock.Ultraspherical
