import Bridge.Mellin

/-!
# Section 7: the Malmsten integral and the Eulerian quotient

Manuscript V173, Proposition 7.1 and eqs. (164)–(169).

Input (cited, not re-proved): Blagouchine's evaluation [Ramanujan J. 35 (2014), p. 33, Eq. (16)]
`T_{π/2}(1) = ∫_0^∞ log(1+u²)/cosh(πu/2) du = 2 log(4/π)`.

Proved here:
* (165) the Malmsten kernel is the Eulerian quotient: `r_E(iπu)/r_E(2iπu) = q_E(πu/2) = sech(πu/2)`,
  so `T_{π/2}(1) = ∫ log(1+u²) q_E(πu/2) du = 2 log(2 r_E(π))` with `r_E(π) = 2/π`;
* (166)–(167): `T = 2 log(2/∛I₂)` and `d_E = exp(3T/2)/8` with `I₂ = ∫ t² q_E = π³/8` and `d_E = 8/π³`;
* (169) is the restatement `∫ (1 - q_E)/t² = 2 β(2) r_E(π)` of the cited value `(4/π)β(2)` (Abdulsalam).
-/

open Real MeasureTheory Set

namespace EulerianBridge.Malmsten

open EulerianBridge.Mellin

/-- The Malmsten integral `T_{π/2}(1)`. -/
noncomputable def T : ℝ := ∫ u in Ioi (0:ℝ), log (1 + u ^ 2) / cosh (π * u / 2)

/-- Blagouchine's evaluation, as a cited hypothesis. -/
def Blagouchine : Prop := T = 2 * log (4 / π)

/-- `r_E(π) = 2/π`. -/
noncomputable def rEpi : ℝ := 2 / π

/-- The endpoint determinant of the fixed parametrisation, `d_E = 8/π³` (eq. (12)). -/
noncomputable def dE : ℝ := 8 / π ^ 3

/-- (165): the kernel is `q_E(πu/2)`. -/
theorem kernel_eq_qE (u : ℝ) : 1 / cosh (π * u / 2) = qE (π * u / 2) := by
  rw [(qE_eq_sech _).1, sech]

theorem T_eq_qE : T = ∫ u in Ioi (0:ℝ), log (1 + u ^ 2) * qE (π * u / 2) := by
  unfold T
  refine setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
  rw [← kernel_eq_qE, mul_one_div]

/-- Proposition 7.1, (165): `T = 2 log(2 r_E(π))`. -/
theorem T_eq_log (h : Blagouchine) : T = 2 * log (2 * rEpi) := by
  rw [h, rEpi]; congr 2; ring

/-- Proposition 7.1, (166)–(167), with `I₂ = π³/8` proved in `Bridge.Mellin.moment_two`. -/
theorem T_I2_dE (h : Blagouchine) :
    let I₂ := ∫ t in Ioi (0:ℝ), t ^ 2 * qE t
    T = 2 * log (2 / I₂ ^ ((1:ℝ) / 3)) ∧ dE = (1 / 8) * exp ((3 / 2) * T) := by
  intro I₂
  have hI : I₂ = π ^ 3 / 8 := by
    exact moment_two.1.trans moment_two.2
  have hp : 0 < π := pi_pos
  have hcube : (π ^ 3 / 8) ^ ((1:ℝ) / 3) = π / 2 := by
    rw [show π ^ 3 / 8 = (π / 2) ^ (3:ℕ) by ring, ← rpow_natCast, ← rpow_mul (by positivity)]
    norm_num
  refine ⟨?_, ?_⟩
  · rw [hI, hcube, h]; congr 2; field_simp; ring
  · rw [h, dE, show (3:ℝ) / 2 * (2 * log (4 / π)) = 3 * log (4 / π) by ring, ← log_rpow (by positivity),
      exp_log (by positivity)]
    rw [show ((3:ℝ)) = ((3:ℕ):ℝ) by norm_num, rpow_natCast]
    field_simp
    ring

/-- (169): the cited value `∫_0^∞ (1 - sech t)/t² dt = (4/π) β(2)` (Abdulsalam) restated with `q_E`
and `r_E(π)`. -/
theorem catalan_q (hA : ∫ t in Ioi (0:ℝ), (1 - sech t) / t ^ 2 = 4 / π * dirichletBeta 2) :
    ∫ t in Ioi (0:ℝ), (1 - qE t) / t ^ 2 = 2 * dirichletBeta 2 * rEpi := by
  have : ∫ t in Ioi (0:ℝ), (1 - qE t) / t ^ 2 = ∫ t in Ioi (0:ℝ), (1 - sech t) / t ^ 2 := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    rw [(qE_eq_sech t).1]
  rw [this, hA, rEpi]; ring

end EulerianBridge.Malmsten
