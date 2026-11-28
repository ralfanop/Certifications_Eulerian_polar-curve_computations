import Mathlib
import Manuscript17.CassiniChartGeometry20261127

noncomputable section
namespace Manuscript17.CassiniIntrinsicCurvature

open Set
open Manuscript17.CassiniChartGeometry

/-! Direct intrinsic curvature computation in the orthogonal altitude
chart. The coordinate formula for the Levi-Civita connection and Riemann
tensor is the classical definition; no conformal curvature law is used. -/

def E (u : ℝ) := u^2 / ((2-u^2)^2*(1-u^2))
def G (u : ℝ) := u^2*(1-u^2)/(2-u^2)^2
def Eprime (u : ℝ) :=
  (2*u*((2-u^2)^2*(1-u^2)) -
    u^2*((-4*u*(2-u^2))*(1-u^2)+(2-u^2)^2*(-2*u))) /
      ((2-u^2)^2*(1-u^2))^2
def Gprime (u : ℝ) := 2*u*(2-3*u^2)/(2-u^2)^3

theorem coefficients (u p : ℝ) (hu : u ∈ Ioo (0:ℝ) 1) :
    metricUU u p = E u ∧ metricPP u p = G u ∧ metricUP u p = 0 := by
  obtain ⟨h1,h2,h3⟩ := metric_components u p hu
  refine ⟨?_,?_,h3⟩
  · rw [h1]
    unfold scale E
    rw [div_pow,div_div]
  · rw [h2]
    unfold scale G
    rw [div_pow]
    ring

theorem E_deriv (u : ℝ) (hu : u ∈ Ioo (0:ℝ) 1) :
    HasDerivAt E (Eprime u) u := by
  have hq : 0 < 1-u^2 := qpos u hu
  have hd : 0 < 2-u^2 := by linarith
  have hp := hasDerivAt_pow 2 u
  have ha := (hasDerivAt_const u (2:ℝ)).sub hp
  have hb := (hasDerivAt_const u (1:ℝ)).sub hp
  have hc := (ha.pow 2).mul hb
  have he := hp.div hc (mul_ne_zero (pow_ne_zero _ hd.ne') hq.ne')
  convert he using 1
  · rfl
  · simp [Eprime]
    ring

theorem G_deriv (u : ℝ) (hu : u ∈ Ioo (0:ℝ) 1) :
    HasDerivAt G (Gprime u) u := by
  have hd : 0 < 2-u^2 := by linarith [qpos u hu]
  have hp := hasDerivAt_pow 2 u
  have ha := (hasDerivAt_const u (2:ℝ)).sub hp
  have hb := (hasDerivAt_const u (1:ℝ)).sub hp
  have h := (hp.mul hb).div (ha.pow 2) (pow_ne_zero _ hd.ne')
  convert h using 1
  · rfl
  · simp [Gprime]
    field_simp [hd.ne']
    <;> ring

def gamma111 (u : ℝ) := deriv E u/(2*E u)
def gamma122 (u : ℝ) := -deriv G u/(2*E u)
def gamma212 (u : ℝ) := deriv G u/(2*G u)

def gamma122Explicit (u : ℝ) := -(2-3*u^2)*(1-u^2)/(u*(2-u^2))
def gamma122Prime (u : ℝ) :=
  (((6*u)*(1-u^2)+(2-3*u^2)*(2*u))*(u*(2-u^2)) -
    (-(2-3*u^2)*(1-u^2))*(2-3*u^2)) / (u*(2-u^2))^2

theorem gamma122_eq (u : ℝ) (hu : u ∈ Ioo (0:ℝ) 1) :
    gamma122 u = gamma122Explicit u := by
  have hq : 0 < 1-u^2 := qpos u hu
  have hd : 0 < 2-u^2 := by linarith
  unfold gamma122 gamma122Explicit
  rw [(G_deriv u hu).deriv]
  unfold Gprime E
  field_simp [hu.1.ne',hq.ne',hd.ne']
  <;> ring

theorem gamma122_explicit_deriv (u : ℝ) (hu : u ∈ Ioo (0:ℝ) 1) :
    HasDerivAt gamma122Explicit (gamma122Prime u) u := by
  have hd : 0 < 2-u^2 := by linarith [qpos u hu]
  have hp := hasDerivAt_pow 2 u
  have ha := (hasDerivAt_const u (2:ℝ)).sub (hp.const_mul 3)
  have hb := (hasDerivAt_const u (1:ℝ)).sub hp
  have hc := (hasDerivAt_const u (2:ℝ)).sub hp
  have h := (ha.neg.mul hb).div ((hasDerivAt_id u).mul hc)
    (mul_ne_zero hu.1.ne' hd.ne')
  convert h using 1
  · rfl
  · simp [gamma122Prime]
    ring

theorem gamma122_derivative (u : ℝ) (hu : u ∈ Ioo (0:ℝ) 1) :
    deriv gamma122 u = gamma122Prime u := by
  have h : gamma122 =ᶠ[nhds u] gamma122Explicit := by
    filter_upwards [isOpen_Ioo.mem_nhds hu] with v hv
    exact gamma122_eq v hv
  exact h.deriv_eq.trans (gamma122_explicit_deriv u hu).deriv

/-- R^u_{pup}/g_pp in the diagonal coordinate metric. -/
def curvature (u : ℝ) :=
  (deriv gamma122 u + gamma111 u*gamma122 u -
      gamma122 u*gamma212 u)/G u

theorem intrinsic_curvature (u : ℝ) (hu : u ∈ Ioo (0:ℝ) 1) :
    curvature u = 3+4/u^4 := by
  have hq : 0 < 1-u^2 := qpos u hu
  have hd : 0 < 2-u^2 := by linarith
  unfold curvature
  rw [gamma122_derivative u hu, gamma122_eq u hu]
  unfold gamma111 gamma212
  rw [(E_deriv u hu).deriv,(G_deriv u hu).deriv]
  unfold gamma122Prime gamma122Explicit Eprime Gprime E G
  field_simp [hu.1.ne',hq.ne',hd.ne']
  <;> ring

theorem agrees_conformal_computation (u : ℝ) (hu : u ∈ Ioo (0:ℝ) 1) :
    curvature u = chartCurvature u := by
  rw [intrinsic_curvature u hu,chart_curvature u hu]

#print axioms coefficients
#print axioms E_deriv
#print axioms G_deriv
#print axioms gamma122_eq
#print axioms gamma122_explicit_deriv
#print axioms gamma122_derivative
#print axioms intrinsic_curvature
#print axioms agrees_conformal_computation
end Manuscript17.CassiniIntrinsicCurvature
