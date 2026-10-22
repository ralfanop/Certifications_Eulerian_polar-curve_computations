/-
Uniform Lanczos note: the concrete cumulant function of Uniform[-1/2,1/2].

`Λ(s) = log(sinh(s/2)/(s/2))`, so `Λ'(s) = 1/2 + 1/(eˢ - 1) - 1/s` (`= ½ coth(s/2) - 1/s`) and
`Λ''(s) = 1/s² - eˢ/(eˢ - 1)² = 1/s² - 1/(4 sinh²(s/2))`.  We work with `Lp = Λ'` (set to `0`
at `s = 0`, its limit) and `Lpp = Λ''` (used only for `s ≠ 0`).  Proved here, with no `sorry`:
* `Lp_odd`, `Lp_pos`, `Lp_le_quarter` (`0 < Λ'(s) ≤ s/4` for `s > 0`), `Lp_lt_half`,
  `half_sub_inv_lt_Lp` (`1/2 - 1/s < Λ'(s)`), `Lp_le_half_sub` (`Λ'(s) ≤ 1/2 - 1/(s+2)`);
* `hasDerivAt_Lp` (`Λ'' = Lpp` off `0`), `Lpp_pos`, `Lpp_le_quarter` (`0 < Λ'' ≤ 1/4` for `s > 0`);
* `Lp_strictMono`, `Lp_continuous`, `Lp_slope` (`Λ'(σ') - Λ'(σ) ≤ (σ' - σ)/4` for `0 ≤ σ ≤ σ'`),
  `abs_Lp_lt_half`, `Lp_surj`: `Λ'` is an increasing homeomorphism `ℝ → (-1/2, 1/2)`;
* the inverse `Ip = I'` (`Λ'(I'(x)) = x`) on `(-1/2, 1/2)`: `Lp_Ip`, `Ip_Lp`, `Ip_strictMonoOn`,
  `Ip_continuousOn`, `Ip_zero`, `Ip_nonneg`, `Ip_slope` (`I'(y') - I'(y) ≥ 4(y' - y)`, i.e. `I'' ≥ 4`),
  `Ip_lower` (`I'(y) ≥ 1/(1/2 - y) - 2`).
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.Order.IntermediateValue

open Real Set Filter Topology

namespace UniformLanczos

/-! ### Two elementary hyperbolic inequalities -/

/-- `sinh u < u cosh u` for `u > 0` (i.e. `tanh u < u`). -/
theorem sinh_lt_mul_cosh {u : ℝ} (hu : 0 < u) : sinh u < u * cosh u := by
  let g : ℝ → ℝ := fun u => u * cosh u - sinh u
  have hd : ∀ x, HasDerivAt g (x * sinh x) x := by
    intro x
    have := ((hasDerivAt_id x).mul (hasDerivAt_cosh x)).sub (hasDerivAt_sinh x)
    convert this using 1
    · funext y; simp [g]
    · simp only [id, one_mul]; ring
  have hmono : StrictMonoOn g (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · exact (continuous_id.mul continuous_cosh |>.sub continuous_sinh).continuousOn
    · intro x hx
      rw [interior_Ici] at hx
      rw [(hd x).deriv]
      exact mul_pos hx (sinh_pos_iff.mpr hx)
  have := hmono ((Set.mem_Ici.mpr le_rfl)) (le_of_lt hu : (0:ℝ) ≤ u) hu
  simp [g] at this
  linarith

/-- `u cosh u - sinh u ≤ u² sinh u` for `u ≥ 0`. -/
theorem mul_cosh_sub_sinh_le {u : ℝ} (hu : 0 ≤ u) : u * cosh u - sinh u ≤ u ^ 2 * sinh u := by
  let h : ℝ → ℝ := fun u => u ^ 2 * sinh u - u * cosh u + sinh u
  have hd : ∀ x, HasDerivAt h (x * sinh x + x ^ 2 * cosh x) x := by
    intro x
    have h1 := ((hasDerivAt_pow 2 x).mul (hasDerivAt_sinh x))
    have h2 := ((hasDerivAt_id x).mul (hasDerivAt_cosh x))
    have := (h1.sub h2).add (hasDerivAt_sinh x)
    convert this using 1
    · funext y; simp only [h, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, id]
    · simp only [id, one_mul]; norm_num; ring
  have hmono : MonotoneOn h (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact ((continuous_pow 2).mul continuous_sinh |>.sub
        (continuous_id.mul continuous_cosh) |>.add continuous_sinh).continuousOn
    · exact fun x _ => (hd x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      rw [(hd x).deriv]
      have hx' : (0:ℝ) < x := hx
      have h1 := sinh_pos_iff.mpr hx'
      have h2 := cosh_pos x
      exact add_nonneg (mul_nonneg hx'.le h1.le) (mul_nonneg (sq_nonneg x) h2.le)
  have := hmono ((Set.mem_Ici.mpr le_rfl)) hu hu
  simp [h] at this
  linarith

/-! ### `Λ'` and `Λ''` -/

/-- `Λ'(s) = 1/2 + 1/(eˢ - 1) - 1/s`, with value `0` at `s = 0`. -/
noncomputable def Lp (s : ℝ) : ℝ := if s = 0 then 0 else 1 / 2 + 1 / (exp s - 1) - 1 / s

/-- `Λ''(s) = 1/s² - eˢ/(eˢ - 1)²` (meaningful for `s ≠ 0`). -/
noncomputable def Lpp (s : ℝ) : ℝ := 1 / s ^ 2 - exp s / (exp s - 1) ^ 2

lemma exp_sub_one_ne {s : ℝ} (hs : s ≠ 0) : exp s - 1 ≠ 0 := by
  intro h
  have : exp s = 1 := by linarith
  exact hs (Real.exp_eq_one_iff s |>.mp this)

lemma exp_eq_sq_half (s : ℝ) : exp s = exp (s / 2) ^ 2 := by
  rw [sq, ← Real.exp_add]; ring_nf

/-- `1/2 + 1/(eˢ - 1) = cosh(s/2)/(2 sinh(s/2))` for `s ≠ 0`. -/
lemma half_add_eq_coth {s : ℝ} (hs : s ≠ 0) :
    1 / 2 + 1 / (exp s - 1) = cosh (s / 2) / (2 * sinh (s / 2)) := by
  have he := exp_sub_one_ne hs
  rw [exp_eq_sq_half] at he ⊢
  rw [cosh_eq, sinh_eq, Real.exp_neg]
  have hpos := Real.exp_pos (s / 2)
  set e := exp (s / 2)
  have h1 : e ^ 2 - 1 ≠ 0 := he
  have h2 : e - e⁻¹ ≠ 0 := by
    intro h
    apply h1
    have : e * (e - e⁻¹) = e ^ 2 - 1 := by field_simp
    rw [← this, h, mul_zero]
  field_simp
  ring

/-- `eˢ/(eˢ - 1)² = 1/(4 sinh²(s/2))` for `s ≠ 0`. -/
lemma exp_div_sq_eq {s : ℝ} (hs : s ≠ 0) :
    exp s / (exp s - 1) ^ 2 = 1 / (4 * sinh (s / 2) ^ 2) := by
  have he := exp_sub_one_ne hs
  rw [exp_eq_sq_half] at he ⊢
  rw [sinh_eq, Real.exp_neg]
  have hpos := Real.exp_pos (s / 2)
  set e := exp (s / 2)
  have h1 : e ^ 2 - 1 ≠ 0 := he
  have h2 : e - e⁻¹ ≠ 0 := by
    intro h
    apply h1
    have : e * (e - e⁻¹) = e ^ 2 - 1 := by field_simp
    rw [← this, h, mul_zero]
  field_simp
  try ring

lemma Lp_of_ne {s : ℝ} (hs : s ≠ 0) : Lp s = 1 / 2 + 1 / (exp s - 1) - 1 / s := by
  simp [Lp, hs]

@[simp] lemma Lp_zero : Lp 0 = 0 := by simp [Lp]

/-- In hyperbolic form: `Λ'(s) = (u cosh u - sinh u)/(2u sinh u)` with `u = s/2`, `s ≠ 0`. -/
lemma Lp_hyp {s : ℝ} (hs : s ≠ 0) :
    Lp s = (s / 2 * cosh (s / 2) - sinh (s / 2)) / (2 * (s / 2) * sinh (s / 2)) := by
  rw [Lp_of_ne hs, half_add_eq_coth hs]
  have hsh : sinh (s / 2) ≠ 0 := by
    intro h; rw [Real.sinh_eq_zero] at h; exact hs (by linarith)
  field_simp
  try ring

theorem Lp_odd (s : ℝ) : Lp (-s) = -Lp s := by
  by_cases hs : s = 0
  · simp [hs]
  have hs' : -s ≠ 0 := neg_ne_zero.mpr hs
  rw [Lp_of_ne hs, Lp_of_ne hs', Real.exp_neg]
  have he := exp_sub_one_ne hs
  have hpos := Real.exp_pos s
  have h1e : 1 - exp s ≠ 0 := by intro h; apply he; linarith
  have hinv : 1 / ((exp s)⁻¹ - 1) = -(exp s / (exp s - 1)) := by
    have : (exp s)⁻¹ - 1 = (1 - exp s) / exp s := by field_simp
    rw [this]; field_simp; ring
  rw [hinv]
  field_simp
  ring

theorem Lp_pos {s : ℝ} (hs : 0 < s) : 0 < Lp s := by
  rw [Lp_hyp hs.ne']
  have hu : 0 < s / 2 := by positivity
  have h1 := sinh_lt_mul_cosh hu
  have h2 := sinh_pos_iff.mpr hu
  apply div_pos (by linarith) (by positivity)

theorem Lp_le_quarter {s : ℝ} (hs : 0 ≤ s) : Lp s ≤ s / 4 := by
  rcases eq_or_lt_of_le hs with h | h
  · rw [← h]; simp
  rw [Lp_hyp h.ne']
  have hu : 0 < s / 2 := by positivity
  have h1 := mul_cosh_sub_sinh_le hu.le
  have h2 := sinh_pos_iff.mpr hu
  rw [div_le_iff₀ (by positivity)]
  nlinarith

theorem Lp_lt_half {s : ℝ} (hs : 0 < s) : Lp s < 1 / 2 := by
  rw [Lp_of_ne hs.ne']
  have h1 : s + 1 < exp s := add_one_lt_exp hs.ne'
  have h2 : 1 / (exp s - 1) < 1 / s := one_div_lt_one_div_of_lt hs (by linarith)
  linarith

theorem half_sub_inv_lt_Lp {s : ℝ} (hs : 0 < s) : 1 / 2 - 1 / s < Lp s := by
  rw [Lp_of_ne hs.ne']
  have h1 : s + 1 < exp s := add_one_lt_exp hs.ne'
  have : 0 < 1 / (exp s - 1) := by apply one_div_pos.mpr; linarith
  linarith

theorem Lp_le_half_sub {s : ℝ} (hs : 0 < s) : Lp s ≤ 1 / 2 - 1 / (s + 2) := by
  rw [Lp_of_ne hs.ne']
  have h1 := quadratic_le_exp_of_nonneg hs.le
  have hq : 0 < s * (s + 2) / 2 := by positivity
  have h2 : 1 / (exp s - 1) ≤ 1 / (s * (s + 2) / 2) :=
    one_div_le_one_div_of_le hq (by nlinarith)
  have h3 : 1 / (s * (s + 2) / 2) - 1 / s = -(1 / (s + 2)) := by
    field_simp; ring
  linarith

theorem hasDerivAt_Lp {s : ℝ} (hs : s ≠ 0) : HasDerivAt Lp (Lpp s) s := by
  have he := exp_sub_one_ne hs
  have hev : (fun x => 1 / 2 + 1 / (exp x - 1) - 1 / x) =ᶠ[𝓝 s] Lp := by
    filter_upwards [isOpen_ne.mem_nhds hs] with x hx
    rw [Lp_of_ne hx]
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev.symm
  have h1 : HasDerivAt (fun x => exp x - 1) (exp s) s := (Real.hasDerivAt_exp s).sub_const 1
  have h2 := (h1.inv he)
  have h3 := (hasDerivAt_id s).inv hs
  have := ((hasDerivAt_const s (1 / 2 : ℝ)).add h2).sub h3
  simp only [one_div]
  convert this using 1
  · funext x; simp [Pi.add_apply, Pi.sub_apply, Pi.inv_apply]
  · unfold Lpp
    simp only [id]
    field_simp
    ring

theorem Lpp_pos {s : ℝ} (hs : 0 < s) : 0 < Lpp s := by
  unfold Lpp
  rw [exp_div_sq_eq hs.ne']
  have hu : 0 < s / 2 := by positivity
  have h1 : s / 2 < sinh (s / 2) := self_lt_sinh_iff.mpr hu
  have h2 : (s / 2) ^ 2 < sinh (s / 2) ^ 2 := by nlinarith
  have h3 : 1 / (4 * sinh (s / 2) ^ 2) < 1 / s ^ 2 := by
    apply one_div_lt_one_div_of_lt (by positivity); nlinarith
  linarith

theorem Lpp_le_quarter {s : ℝ} (hs : 0 < s) : Lpp s ≤ 1 / 4 := by
  unfold Lpp
  rw [exp_div_sq_eq hs.ne']
  have hu : 0 < s / 2 := by positivity
  set u := s / 2 with hu_def
  have hsu : s = 2 * u := by rw [hu_def]; ring
  rw [hsu]
  have h1 := sinh_lt_mul_cosh hu
  have h2 := sinh_pos_iff.mpr hu
  have hc := cosh_sq u
  -- sinh² ≤ u² cosh² = u² (sinh² + 1)
  have h3 : sinh u ^ 2 ≤ u ^ 2 * (sinh u ^ 2 + 1) := by
    rw [← hc]; nlinarith
  rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

theorem Lp_slope {σ σ' : ℝ} (hσ : 0 ≤ σ) (h : σ ≤ σ') : Lp σ' - Lp σ ≤ (σ' - σ) / 4 := by
  rcases eq_or_lt_of_le hσ with h0 | h0
  · rw [← h0, Lp_zero, sub_zero, sub_zero]; exact Lp_le_quarter (h0 ▸ h)
  rcases eq_or_lt_of_le h with h1 | h1
  · rw [h1]; simp
  have hcont : ContinuousOn Lp (Icc σ σ') := fun x hx =>
    (hasDerivAt_Lp (by linarith [hx.1] : x ≠ 0)).continuousAt.continuousWithinAt
  obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope Lp Lpp h1 hcont
    (fun x hx => hasDerivAt_Lp (by linarith [hx.1] : x ≠ 0))
  have hcpos : 0 < c := lt_trans h0 hc.1
  have hle := Lpp_le_quarter hcpos
  rw [hceq, div_le_iff₀ (by linarith)] at hle
  linarith

theorem Lp_strictMonoOn_nonneg : StrictMonoOn Lp (Ici 0) := by
  intro σ hσ σ' _ h
  rcases eq_or_lt_of_le (show (0:ℝ) ≤ σ from hσ) with h0 | h0
  · rw [← h0, Lp_zero]; exact Lp_pos (h0 ▸ h)
  have hcont : ContinuousOn Lp (Icc σ σ') := fun x hx =>
    (hasDerivAt_Lp (by linarith [hx.1] : x ≠ 0)).continuousAt.continuousWithinAt
  obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope Lp Lpp h hcont
    (fun x hx => hasDerivAt_Lp (by linarith [hx.1] : x ≠ 0))
  have hpos := Lpp_pos (lt_trans h0 hc.1)
  rw [hceq, lt_div_iff₀ (by linarith)] at hpos
  linarith

theorem Lp_strictMono : StrictMono Lp := by
  intro s s' h
  by_cases hs : 0 ≤ s
  · exact Lp_strictMonoOn_nonneg hs (le_trans hs h.le) h
  push Not at hs
  by_cases hs' : s' ≤ 0
  · have := Lp_strictMonoOn_nonneg (show (0:ℝ) ≤ -s' by linarith) (show (0:ℝ) ≤ -s by linarith)
      (show -s' < -s by linarith)
    rw [Lp_odd, Lp_odd] at this; linarith
  · push Not at hs'
    have h1 := Lp_pos hs'
    have h2 := Lp_pos (show 0 < -s by linarith)
    rw [Lp_odd] at h2; linarith

theorem abs_Lp_le (s : ℝ) : |Lp s| ≤ |s| / 4 := by
  rcases le_total 0 s with hs | hs
  · rw [abs_of_nonneg hs]
    rcases eq_or_lt_of_le hs with h | h
    · rw [← h]; simp
    rw [abs_of_pos (Lp_pos h)]; exact Lp_le_quarter hs
  · have h := abs_Lp_le_aux (-s) (by linarith)
    rw [Lp_odd, abs_neg, abs_neg] at h; exact h
where
  abs_Lp_le_aux (s : ℝ) (hs : 0 ≤ s) : |Lp s| ≤ |s| / 4 := by
    rw [abs_of_nonneg hs]
    rcases eq_or_lt_of_le hs with h | h
    · rw [← h]; simp
    rw [abs_of_pos (Lp_pos h)]; exact Lp_le_quarter hs

theorem Lp_continuous : Continuous Lp := by
  rw [continuous_iff_continuousAt]
  intro s
  by_cases hs : s = 0
  · subst hs
    have : Tendsto Lp (𝓝 0) (𝓝 0) := by
      apply squeeze_zero_norm (a := fun s => |s| / 4)
      · intro x; rw [Real.norm_eq_abs]; exact abs_Lp_le x
      · have : Tendsto (fun s : ℝ => |s| / 4) (𝓝 0) (𝓝 (|0| / 4)) :=
          (continuous_abs.div_const 4).tendsto 0
        simpa using this
    simpa [ContinuousAt, Lp_zero] using this
  · exact (hasDerivAt_Lp hs).continuousAt

theorem abs_Lp_lt_half (s : ℝ) : |Lp s| < 1 / 2 := by
  rcases lt_trichotomy s 0 with h | h | h
  · have h1 := Lp_lt_half (show 0 < -s by linarith)
    have h2 := Lp_pos (show 0 < -s by linarith)
    rw [Lp_odd] at h1 h2
    rw [abs_lt]; constructor <;> linarith
  · subst h; simp
  · have h1 := Lp_lt_half h
    have h2 := Lp_pos h
    rw [abs_lt]; constructor <;> linarith

theorem Lp_surj {x : ℝ} (hx : x ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2)) : ∃ s, Lp s = x := by
  -- first for `0 ≤ x`
  have key : ∀ y : ℝ, 0 ≤ y → y < 1 / 2 → ∃ s, Lp s = y := by
    intro y hy0 hy1
    set T := 1 / (1 / 2 - y) + 1 with hT
    have hd : 0 < 1 / 2 - y := by linarith
    have hTpos : 0 < T := by positivity
    have hTlt : y < Lp T := by
      have h1 := half_sub_inv_lt_Lp hTpos
      have h2 : 1 / T < 1 / 2 - y := by
        rw [div_lt_iff₀ hTpos]
        have : (1 / 2 - y) * (1 / (1 / 2 - y)) = 1 := mul_one_div_cancel hd.ne'
        nlinarith
      linarith
    obtain ⟨s, _, hs⟩ := intermediate_value_Icc hTpos.le Lp_continuous.continuousOn
      ⟨by simpa using hy0, hTlt.le⟩
    exact ⟨s, hs⟩
  rcases le_total 0 x with h | h
  · exact key x h hx.2
  · obtain ⟨s, hs⟩ := key (-x) (by linarith) (by linarith [hx.1])
    exact ⟨-s, by rw [Lp_odd, hs, neg_neg]⟩

/-! ### The inverse `Ip = I'` -/

/-- `I'(x)`: the unique `s` with `Λ'(s) = x`, for `|x| < 1/2`. -/
noncomputable def Ip (x : ℝ) : ℝ := Function.invFunOn Lp univ x

theorem Lp_Ip {x : ℝ} (hx : x ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2)) : Lp (Ip x) = x := by
  obtain ⟨s, hs⟩ := Lp_surj hx
  exact Function.invFunOn_eq ⟨s, mem_univ _, hs⟩

theorem Ip_Lp (s : ℝ) : Ip (Lp s) = s := by
  have hx : Lp s ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2) := by
    have := abs_Lp_lt_half s; rw [abs_lt] at this; exact this
  exact Lp_strictMono.injective (Lp_Ip hx)

@[simp] theorem Ip_zero : Ip 0 = 0 := by
  have := Ip_Lp 0; rwa [Lp_zero] at this

theorem Ip_strictMonoOn : StrictMonoOn Ip (Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
  intro x hx y hy hxy
  by_contra hcon
  push Not at hcon
  have := Lp_strictMono.monotone hcon
  rw [Lp_Ip hx, Lp_Ip hy] at this
  linarith

theorem Ip_continuousOn : ContinuousOn Ip (Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
  intro a ha
  apply ContinuousAt.continuousWithinAt
  apply Ip_strictMonoOn.continuousAt_of_image_mem_nhds (Ioo_mem_nhds ha.1 ha.2)
  apply Filter.univ_mem'
  intro σ
  refine ⟨Lp σ, ?_, Ip_Lp σ⟩
  have := abs_Lp_lt_half σ; rw [abs_lt] at this; exact this

lemma mem_Ioo_of {y : ℝ} (h0 : 0 ≤ y) (h1 : y < 1 / 2) : y ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2) :=
  ⟨by linarith, h1⟩

theorem Ip_nonneg {y : ℝ} (h0 : 0 ≤ y) (h1 : y < 1 / 2) : 0 ≤ Ip y := by
  rcases eq_or_lt_of_le h0 with h | h
  · rw [← h, Ip_zero]
  · have := Ip_strictMonoOn (mem_Ioo_of le_rfl (by norm_num)) (mem_Ioo_of h0 h1) h
    rw [Ip_zero] at this; exact this.le

theorem Ip_slope {y y' : ℝ} (h0 : 0 ≤ y) (h : y ≤ y') (h1 : y' < 1 / 2) :
    4 * (y' - y) ≤ Ip y' - Ip y := by
  have hy : y ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2) := mem_Ioo_of h0 (lt_of_le_of_lt h h1)
  have hy' : y' ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2) := mem_Ioo_of (h0.trans h) h1
  have hσ := Ip_nonneg h0 (lt_of_le_of_lt h h1)
  have hσσ' : Ip y ≤ Ip y' := Ip_strictMonoOn.monotoneOn hy hy' h
  have := Lp_slope hσ hσσ'
  rw [Lp_Ip hy, Lp_Ip hy'] at this
  linarith

theorem Ip_lower {y : ℝ} (h0 : 0 ≤ y) (h1 : y < 1 / 2) : 1 / (1 / 2 - y) - 2 ≤ Ip y := by
  have hy : y ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2) := mem_Ioo_of h0 h1
  have hσ := Ip_nonneg h0 h1
  rcases eq_or_lt_of_le hσ with h | h
  · have : y = 0 := by have := Lp_Ip hy; rw [← h, Lp_zero] at this; linarith
    rw [this, Ip_zero]; norm_num
  · have h2 := Lp_le_half_sub h
    rw [Lp_Ip hy] at h2
    have hd : 0 < 1 / 2 - y := by linarith
    have h3 : 1 / (Ip y + 2) ≤ 1 / 2 - y := by linarith
    have h4 : 1 / (1 / 2 - y) ≤ Ip y + 2 := by
      rw [div_le_iff₀ hd]
      rw [div_le_iff₀ (by linarith)] at h3
      nlinarith
    linarith

end UniformLanczos
