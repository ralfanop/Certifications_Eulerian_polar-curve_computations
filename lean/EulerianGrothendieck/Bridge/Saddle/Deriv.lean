import Bridge.Saddle.Represent

/-!
# Lemma 5.5, part 14: the function `log g_M + MI - ½ log(M/(2πv)) - η/M` and its two derivatives

Definitions as in the manuscript (Section 5): `g_M(x) = M w_M(Mx)`, `s(x) = I'(x)` (`UL.Ip`),
`I(x) = s(x)x - Λ(s(x))`, `v(x) = Λ''(s(x))`, `η(x) = η(s(x))`.
At every `|x| < 1/2` with `w_M(Mx) > 0`:
* `hasDerivAt_EM`: `E' = M w'/w (Mx) + M s + (½ log v)' - η'/M` (`E1`);
* `hasDerivAt_E1`: `E'' = M²(w''/w - (w'/w)²)(Mx) + M/v + (½ log v)'' - η''/M` (`E2`).
-/

open MeasureTheory Set Complex Filter Topology Metric
open scoped Nat

namespace EulerianBridge.Saddle

/-- `g_M(x) = M w_M(Mx)`, the density of `S_M/M`. -/
noncomputable def gM (M : ℕ) (x : ℝ) : ℝ := M * w M (M * x)

/-- The Cramér rate function `I(x) = s(x)x - Λ(s(x))`, eq. (56). -/
noncomputable def Irate (x : ℝ) : ℝ := UL.Ip x * x - Lr (UL.Ip x)

/-- `v(x) = Λ''(s(x))`. -/
noncomputable def vx (x : ℝ) : ℝ := κ 2 (UL.Ip x)

/-- `η(x)` of eq. (67). -/
noncomputable def etaX (x : ℝ) : ℝ := etaS (UL.Ip x)

/-- The quantity estimated in (68). -/
noncomputable def EM (M : ℕ) (x : ℝ) : ℝ :=
  Real.log (gM M x) + M * Irate x - 1 / 2 * Real.log (M / (2 * Real.pi * vx x)) - etaX x / M

/-- The first derivative of `EM`. -/
noncomputable def E1 (M : ℕ) (x : ℝ) : ℝ :=
  M * (deriv (w M) (M * x) / w M (M * x)) + M * UL.Ip x + L1 (UL.Ip x) - eta1 (UL.Ip x) / M

/-- The second derivative of `EM`. -/
noncomputable def E2 (M : ℕ) (x : ℝ) : ℝ :=
  (M:ℝ) ^ 2 * (deriv (deriv (w M)) (M * x) / w M (M * x) - (deriv (w M) (M * x) / w M (M * x)) ^ 2) +
    M / κ 2 (UL.Ip x) + L2 (UL.Ip x) - eta2 (UL.Ip x) / M

theorem hasDerivAt_comp_Ip {F : ℝ → ℝ} {F' : ℝ → ℝ} (hF : ∀ s, HasDerivAt F (F' s) s)
    {x : ℝ} (hx : x ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2)) :
    HasDerivAt (fun y => F (UL.Ip y)) (F' (UL.Ip x) / κ 2 (UL.Ip x)) x := by
  have h := (hF (UL.Ip x)).comp x (hasDerivAt_Ip hx)
  rw [div_eq_mul_inv]
  exact h

theorem hasDerivAt_Irate {x : ℝ} (hx : x ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2)) :
    HasDerivAt Irate (UL.Ip x) x := by
  have hI := hasDerivAt_Ip hx
  have hL := hasDerivAt_comp_Ip (F := Lr) (F' := κ 1) (fun s => by
    have := hasDerivAt_κ 0 s; rwa [show κ 0 = Lr by funext t; exact κ_zero_eq t] at this) hx
  have h := (hI.mul (hasDerivAt_id x)).sub hL
  convert h using 1
  rw [Lp_Ip' hx]
  have hk := κ2_ne (UL.Ip x)
  simp only [id]
  try field_simp
  try ring

theorem log_ratio_eq {M : ℕ} (hM : 1 ≤ M) (x : ℝ) :
    Real.log (M / (2 * Real.pi * vx x)) = Real.log M - Real.log (2 * Real.pi) - Real.log (vx x) := by
  have hv : 0 < vx x := κ_two_pos _
  have hMpos : (0:ℝ) < M := by exact_mod_cast hM
  rw [Real.log_div hMpos.ne' (by positivity), Real.log_mul (by positivity) hv.ne']; ring

theorem hasDerivAt_logv {x : ℝ} (hx : x ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2)) :
    HasDerivAt (fun y => Real.log (vx y)) (2 * L1 (UL.Ip x)) x := by
  have h := hasDerivAt_comp_Ip (F := fun s => Real.log (κ 2 s)) (F' := fun s => κ 3 s / κ 2 s)
    (fun s => (hasDerivAt_κ 2 s).log (κ2_ne s)) hx
  convert h using 1
  have hk := κ2_ne (UL.Ip x)
  simp only [L1]
  try field_simp
  try ring

theorem hasDerivAt_gM {M : ℕ} (hM : 3 ≤ M) (x : ℝ) :
    HasDerivAt (gM M) ((M:ℝ) * (deriv (w M) (M * x) * M)) x := by
  have hw := (hasDerivAt_w M hM 0 (M * x))
  rw [← hw.deriv] at hw
  have h1 : HasDerivAt (fun y : ℝ => (M:ℝ) * y) M x := by
    simpa using (hasDerivAt_id x).const_mul (M:ℝ)
  have h2 := hw.comp x h1
  exact h2.const_mul (M:ℝ)

theorem hasDerivAt_EM {M : ℕ} (hM : 4 ≤ M) {x : ℝ} (hx : x ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2))
    (hw : 0 < w M (M * x)) : HasDerivAt (EM M) (E1 M x) x := by
  have hM1 : 1 ≤ M := by omega
  have hMpos : (0:ℝ) < M := by exact_mod_cast hM1
  have hg : gM M x ≠ 0 := by unfold gM; positivity
  have h1 := (hasDerivAt_gM (by omega : 3 ≤ M) x).log hg
  have h2 := (hasDerivAt_Irate hx).const_mul (M:ℝ)
  have h3 := hasDerivAt_logv hx
  have h4 := hasDerivAt_comp_Ip (F := etaS) (F' := etaS1) hasDerivAt_etaS hx
  have heq : EM M = fun y => Real.log (gM M y) + M * Irate y -
      1 / 2 * (Real.log M - Real.log (2 * Real.pi) - Real.log (vx y)) - etaS (UL.Ip y) / M := by
    funext y; unfold EM etaX; rw [log_ratio_eq hM1]
  rw [heq]
  have h := ((h1.add h2).sub (((h3.neg.add_const (Real.log M - Real.log (2 * Real.pi))).const_mul
    (1 / 2 : ℝ)))).sub (h4.div_const (M:ℝ))
  convert h using 1
  · funext y; simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply]; ring
  · unfold E1 eta1
    simp only [gM]
    have hk := κ2_ne (UL.Ip x)
    field_simp
    ring

theorem hasDerivAt_E1 {M : ℕ} (hM : 4 ≤ M) {x : ℝ} (hx : x ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2))
    (hw : 0 < w M (M * x)) : HasDerivAt (E1 M) (E2 M x) x := by
  have hM4 : (4:ℝ) ≤ M := by exact_mod_cast hM
  have hMpos : (0:ℝ) < M := by linarith
  have hlin : HasDerivAt (fun y : ℝ => (M:ℝ) * y) M x := by
    simpa using (hasDerivAt_id x).const_mul (M:ℝ)
  have hw0 := hasDerivAt_w M (by omega) 0 (M * x)
  rw [← hw0.deriv] at hw0
  have hw1 := hasDerivAt_deriv_w M hM 0 (M * x)
  rw [← hw1.deriv] at hw1
  have ha := hw1.comp x hlin
  have hb := hw0.comp x hlin
  have hq := (ha.div hb hw.ne').const_mul (M:ℝ)
  have hI := (hasDerivAt_Ip hx).const_mul (M:ℝ)
  have hL := hasDerivAt_comp_Ip (F := L1) (F' := fun s => (κ 4 s * κ 2 s - 2 * κ 3 s ^ 2) / (2 * κ 2 s ^ 3))
    hasDerivAt_L1 hx
  have he := hasDerivAt_comp_Ip (F := eta1)
    (F' := fun s => (etaS2 s * κ 2 s - etaS1 s * κ 3 s) / κ 2 s ^ 2) hasDerivAt_eta1 hx
  have h := ((hq.add hI).add hL).sub (he.div_const (M:ℝ))
  convert h using 1
  all_goals first
    | (funext y; simp only [E1, Function.comp, Pi.add_apply, Pi.sub_apply])
    | (unfold E2 L2 eta2
       have hk := κ2_ne (UL.Ip x)
       simp only [Function.comp]
       field_simp
       try ring)

end EulerianBridge.Saddle
