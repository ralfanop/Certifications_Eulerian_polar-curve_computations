import Mathlib
import Manuscript13.CrossThroatLemniscate20261126

/-! M12 §9.13. Reuse actual quartic and lemniscate integrals already verified
in CriticalWindowGammaVacuum and CrossThroatLemniscate. The remaining classical
Connon evaluation and identification of the derivatives of the pole-cancelled
Hurwitz function and Eulerian Mellin transform are explicit premises, not axioms.
No claim that those analytic inputs have themselves been formalized here. -/
namespace M12.QuarticStieltjes
noncomputable section
open Manuscript13.CrossThroatElliptic20261125 (criticalF0 criticalF0_gamma)
open Manuscript13.CrossThroatLemniscate20261126 (lemPeriod lem_gamma_of_beta critical_gamma_exact)

def quarticLog : ℝ := Real.log (5*Real.pi/(8*criticalF0^4))
def quarterGamma : ℝ := Real.Gamma (1/4)

theorem actual_lemniscate_bridge :
    lemPeriod = Real.sqrt (Real.pi/5)*criticalF0^2 := by
  rw [lem_gamma_of_beta, critical_gamma_exact]

theorem quarterGamma_pos : 0 < quarterGamma := Real.Gamma_pos_of_pos (by norm_num)

theorem critical_pos : 0 < criticalF0 := by
  rw [criticalF0_gamma]
  exact M12CriticalGamma.critical_constant_pos

theorem critical_fourth :
    criticalF0^4 = 5*quarterGamma^4/(32*Real.pi^2) := by
  rw [criticalF0_gamma]
  have h40 : ((40:ℝ)^(1/4:ℝ))^4 = 40 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 40)]
    norm_num
  have hp : (Real.sqrt Real.pi)^4 = Real.pi^2 := by
    rw [show (4:ℕ)=2*2 by decide,pow_mul,Real.sq_sqrt Real.pi_pos.le]
  rw [div_pow,mul_pow,h40,mul_pow,hp]
  unfold quarterGamma
  field_simp [Real.pi_ne_zero]
  <;> ring

theorem quartic_ratio :
    5*Real.pi/(8*criticalF0^4) = 4*Real.pi^3/quarterGamma^4 := by
  rw [critical_fourth]
  field_simp [Real.pi_ne_zero,quarterGamma_pos.ne']
  <;> ring

theorem quartic_log_expansion :
    quarticLog = Real.log 4 + 3*Real.log Real.pi - 4*Real.log quarterGamma := by
  unfold quarticLog
  rw [quartic_ratio,Real.log_div (by positivity) (pow_ne_zero _ quarterGamma_pos.ne'),
    Real.log_mul (by norm_num) (pow_ne_zero _ Real.pi_ne_zero),Real.log_pow,Real.log_pow]
  norm_num

theorem log_four : Real.log (4:ℝ) = 2*Real.log 2 := by
  rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]
  norm_num

theorem stieltjes_ratio_log :
    Real.log (5*Real.pi/(2*criticalF0^4)) = Real.log 4 + quarticLog := by
  unfold quarticLog
  rw [← Real.log_mul (by norm_num) (by positivity [critical_pos])]
  congr 1
  ring

/-- Transfer of Connon's classical evaluation (explicit hypothesis). -/
theorem connon_quartic (g d : ℝ)
    (h : d = -Real.pi*(g+4*Real.log 2+3*Real.log Real.pi-4*Real.log quarterGamma)) :
    d = -Real.pi*(g+Real.log (5*Real.pi/(2*criticalF0^4))) := by
  rw [h,stieltjes_ratio_log,quartic_log_expansion,log_four]
  ring

/-- Differentiation of the actual factor 4^{-s}; H is the regularized
Hurwitz difference once its value and derivative have been identified. -/
theorem beta_factor_derivative (H : ℝ → ℝ) (d : ℝ)
    (h0 : H 1 = Real.pi) (h1 : HasDerivAt H (-d) 1) :
    HasDerivAt (fun s => Real.exp (-s*Real.log 4)*H s)
      ((-Real.log 4*Real.pi-d)/4) 1 := by
  have he : HasDerivAt (fun s : ℝ => -s*Real.log 4) (-Real.log 4) 1 := by
    convert (hasDerivAt_id (1:ℝ)).neg.mul_const (Real.log 4) using 1 <;> simp
  have hf := he.exp.mul h1
  have hx : Real.exp (-(1:ℝ)*Real.log 4) = 1/4 := by
    rw [neg_one_mul,Real.exp_neg,Real.exp_log (by norm_num : (0:ℝ)<4)]
    norm_num
  convert hf using 1
  rw [hx,h0]
  ring

theorem beta_logarithmic_derivative (g d : ℝ)
    (h : d = -Real.pi*(g+4*Real.log 2+3*Real.log Real.pi-4*Real.log quarterGamma)) :
    -Real.log 4-d/Real.pi = g+quarticLog := by
  rw [connon_quartic g d h,stieltjes_ratio_log]
  field_simp [Real.pi_ne_zero]
  <;> ring

/-- The product rule used for the differentiated Mellin identity. Gamma
derivative at 1 and the beta derivative remain explicit analytic inputs. -/
theorem mellin_product_derivative (beta : ℝ → ℝ) (g : ℝ)
    (hG : HasDerivAt Real.Gamma (-g) 1)
    (hb0 : beta 1 = Real.pi/4)
    (hb : HasDerivAt beta ((Real.pi/4)*(g+quarticLog)) 1) :
    HasDerivAt (fun s => 2*Real.Gamma s*beta s)
      (Real.pi/2*quarticLog) 1 := by
  have h := (hG.const_mul 2).mul hb
  convert h using 1
  rw [Real.Gamma_one,hb0]
  ring

theorem mellin_normalization (m : ℝ)
    (h : m = Real.pi/2*quarticLog) : 2/Real.pi*m = quarticLog := by
  rw [h]
  field_simp [Real.pi_ne_zero]

#print axioms actual_lemniscate_bridge
#print axioms quarterGamma_pos
#print axioms critical_pos
#print axioms critical_fourth
#print axioms quartic_ratio
#print axioms quartic_log_expansion
#print axioms log_four
#print axioms stieltjes_ratio_log
#print axioms connon_quartic
#print axioms beta_factor_derivative
#print axioms beta_logarithmic_derivative
#print axioms mellin_product_derivative
#print axioms mellin_normalization
end
end M12.QuarticStieltjes
