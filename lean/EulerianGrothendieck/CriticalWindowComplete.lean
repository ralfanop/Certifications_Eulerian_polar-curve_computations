import CriticalWindowCorrelation
import CriticalWindowLocalUniform

/-! Joint kernel closure of the M12 critical-window norm, vacuum and
finite-order correlation laws. The compact-uniform norm hypothesis of the
transfer module is discharged by the actual DCT proof. The manuscript's
quarter-power and square-root scales are identified explicitly. -/
namespace M12CriticalComplete
open Filter MeasureTheory ProbabilityTheory Finset
open scoped Topology BigOperators
open M12CriticalPointwise M12CriticalDCT M12CriticalUniform
open M12CriticalVacuum M12CriticalCorrelation
open EulerianGrothendieck EulerianGrothendieck.Fock
set_option maxHeartbeats 2000000

theorem uniformNorm_proved : UniformNorm := by
  intro L hL eps heps
  exact locally_uniform_Fock L hL eps heps

theorem scale_inv_eq_rpow (M : ℕ) :
    (scale M)⁻¹ = (M:ℝ)^(1/4:ℝ) := by
  rw [scale, inv_inv, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
    ← Real.rpow_mul (Nat.cast_nonneg M)] <;> norm_num

theorem scale_sq_eq_inv_sqrt (M : ℕ) :
    scale M ^ 2 = (Real.sqrt (M:ℝ))⁻¹ := by
  rw [scale, inv_pow, Real.sq_sqrt (Real.sqrt_nonneg _)]

noncomputable def c (M : ℕ) (lam : ℝ) : ℝ :=
  1/12+lam/Real.sqrt (M:ℝ)

theorem c_eq (M : ℕ) (lam : ℝ) :
    c M lam = 1/12+lam*scale M^2 := by
  simp only [c, scale_sq_eq_inv_sqrt, div_eq_mul_inv]

theorem eventual_c_pos (L : ℝ) (hL : 0 ≤ L) :
    ∀ᶠ M : ℕ in atTop, ∀ lam : ℝ, |lam| ≤ L → 0 < c M lam * (M:ℝ) := by
  filter_upwards [eventual_scale_conditions L hL] with M hS
  rcases hS with ⟨hM,hsmall,_⟩
  intro lam hlam
  have hl : -L ≤ lam := by linarith [neg_abs_le lam]
  have hc : 0 < (1/12:ℝ)+lam*scale M^2 := by
    nlinarith only [hsmall,mul_le_mul_of_nonneg_right hl (sq_nonneg (scale M))]
  rw [c_eq]
  exact mul_pos hc (by exact_mod_cast hM)

section Probability
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i))
variable (hind : iIndepFun U μ) (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw)
include hU hind hlaw

/- The actual probability partition function, in the notation of M12. -/
omit hU hind hlaw in
noncomputable def N (M : ℕ) (a : ℝ) : ℝ :=
  ∫ xy, Real.exp ((∑ i ∈ range M, U i xy.1) *
    (∑ i ∈ range M, U i xy.2) / a) ∂μ.prod μ

theorem locally_uniform_probability (L : ℝ) (hL : 0 ≤ L) (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ M : ℕ in atTop, ∀ lam : ℝ, |lam| ≤ L →
      |N (μ := μ) U M (c M lam*(M:ℝ)) / (M:ℝ)^(1/4:ℝ) - Fcrit lam| < eps := by
  filter_upwards [locally_uniform_Fock L hL eps heps,eventual_c_pos L hL] with M hM hp
  intro lam hlam
  have hn : N (μ := μ) U M (c M lam*(M:ℝ)) =
      M12CriticalAssembly.originalFockNorm M (c M lam*(M:ℝ)) :=
    (original_eq_probability U hU hind hlaw M (hp lam hlam)).symm
  rw [hn, c_eq, ← scale_inv_eq_rpow, div_eq_mul_inv, inv_inv]
  rw [mul_comm (M12CriticalAssembly.originalFockNorm M _) (scale M)]
  exact hM lam hlam

theorem locally_uniform_vacuum (L : ℝ) (hL : 0 ≤ L) (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ M : ℕ in atTop, ∀ lam : ℝ, |lam| ≤ L →
      |(M:ℝ)^(1/4:ℝ)*fockVacuumProbability (c M lam*(M:ℝ)) M-(Fcrit lam)⁻¹| < eps := by
  filter_upwards [uniform_vacuum_of_norm U hU hind hlaw uniformNorm_proved L hL eps heps]
    with M hM
  intro lam hlam
  rw [← scale_inv_eq_rpow, c_eq]
  exact (hM lam hlam).2

theorem locally_uniform_correlation (L : ℝ) (hL : 0 ≤ L) (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ M : ℕ in atTop, ∀ lam : ℝ, |lam| ≤ L →
      |(M:ℝ)^(1/4:ℝ)*
        (bilinearRatio (Real.sqrt (fockVacuumProbability (c M lam*(M:ℝ)) M)) eulerianPhase-1)
        -1/(2*(Real.pi^2+1)*Fcrit lam)| < eps := by
  have hcoeff (lam : ℝ) : C*(Fcrit lam)⁻¹ = 1/(2*(Real.pi^2+1)*Fcrit lam) := by
    unfold C
    rw [one_div, ← mul_inv, ← one_div]
  filter_upwards [uniform_correlation_of_norm U hU hind hlaw uniformNorm_proved L hL eps heps]
    with M hM
  intro lam hlam
  rw [← scale_inv_eq_rpow,c_eq,← hcoeff]
  exact hM lam hlam

theorem critical_constant_vacuum :
    Tendsto (fun M : ℕ => (M:ℝ)^(1/4:ℝ)*fockVacuumProbability ((M:ℝ)/12) M)
      atTop (𝓝 (4*Real.sqrt Real.pi/((40:ℝ)^(1/4:ℝ)*Real.Gamma (1/4)))) := by
  have h := actual_vacuum_at_critical U hU hind hlaw
  have hcoeff :
      ((40:ℝ)^(1/4:ℝ)*Real.Gamma (1/4)/(4*Real.sqrt Real.pi))⁻¹ =
      4*Real.sqrt Real.pi/((40:ℝ)^(1/4:ℝ)*Real.Gamma (1/4)) := by
    rw [inv_div]
  rw [hcoeff] at h
  simpa only [scale_inv_eq_rpow] using h

theorem critical_constant_correlation :
    Tendsto (fun M : ℕ => (M:ℝ)^(1/4:ℝ)*
      (bilinearRatio (Real.sqrt (fockVacuumProbability ((M:ℝ)/12) M)) eulerianPhase-1))
      atTop (𝓝 (2*Real.sqrt Real.pi/
        ((Real.pi^2+1)*(40:ℝ)^(1/4:ℝ)*Real.Gamma (1/4)))) := by
  simpa only [scale_inv_eq_rpow] using actual_correlation_at_critical U hU hind hlaw

end Probability
end M12CriticalComplete

#print axioms M12CriticalComplete.uniformNorm_proved
#print axioms M12CriticalComplete.scale_inv_eq_rpow
#print axioms M12CriticalComplete.scale_sq_eq_inv_sqrt
#print axioms M12CriticalComplete.c_eq
#print axioms M12CriticalComplete.eventual_c_pos
#print axioms M12CriticalComplete.locally_uniform_probability
#print axioms M12CriticalComplete.locally_uniform_vacuum
#print axioms M12CriticalComplete.locally_uniform_correlation
#print axioms M12CriticalComplete.critical_constant_vacuum
#print axioms M12CriticalComplete.critical_constant_correlation
