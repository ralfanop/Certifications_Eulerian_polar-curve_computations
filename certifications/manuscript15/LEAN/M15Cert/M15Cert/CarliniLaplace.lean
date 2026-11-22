/-
Manuscript 15, Section 7.11, Theorem 7.26 -- Carlini–Laplace normalisation.

* (292)  h/(2R) = U/cosh U = U/(1 + (U²/2) r_E(iU)²) for the catenoid portion between
         u = -U and u = U (h = 2aU, R = a cosh U);
* (293)  there is exactly one u_* > 0 with u_* tanh u_* = 1, and U ↦ U/cosh U attains at
         u_* its unique maximum (on the whole real line);
* (294)  λ_CL = u_*/cosh u_* = 1/sinh u_* = √(u_*² - 1);
* the classical defining equation λ e^{√(1+λ²)} = 1 + √(1+λ²) of the Kepler-series
  threshold holds, and λ_CL is its only positive solution;
* tangent bicone: cosh u ≥ |u|/λ_CL with equality exactly at |u| = u_*, where the two
  radial profiles have the same slope sinh u_* = 1/λ_CL; the whole bicone
  √(x²+y²) = |z|/λ_CL lies inside or on the catenoid;
* (295)  the opening angle α_CL = 2 arccot λ_CL = 2 arctan(1/λ_CL) = π - 2 arctan λ_CL, with
         tan(α_CL/2) = 1/λ_CL and 0 < α_CL < π.
-/
import M15Cert.Kernel

open Real

namespace M15

/-! ### The equation u tanh u = 1 -/

/-- f(u) = u sinh u - cosh u; on u > 0, f(u) = 0 iff u tanh u = 1. -/
noncomputable def fCL (u : ℝ) : ℝ := u * Real.sinh u - Real.cosh u

lemma tanh_eq_iff (u : ℝ) : u * Real.tanh u = 1 ↔ fCL u = 0 := by
  unfold fCL
  rw [Real.tanh_eq_sinh_div_cosh]
  have hc := (Real.cosh_pos u).ne'
  constructor
  · intro h; field_simp at h; linarith
  · intro h; field_simp; linarith

lemma hasDerivAt_fCL (u : ℝ) : HasDerivAt fCL (u * Real.cosh u) u := by
  have h := ((hasDerivAt_id' u).mul (Real.hasDerivAt_sinh u)).sub (Real.hasDerivAt_cosh u)
  have e : 1 * Real.sinh u + u * Real.cosh u - Real.sinh u = u * Real.cosh u := by ring
  rw [e] at h
  exact h

lemma fCL_strictMonoOn : StrictMonoOn fCL (Set.Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0)
  · exact fun x _ => (hasDerivAt_fCL x).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    rw [(hasDerivAt_fCL x).deriv]
    exact mul_pos hx (Real.cosh_pos x)

lemma fCL_zero : fCL 0 = -1 := by simp [fCL]

lemma fCL_two_pos : 0 < fCL 2 := by
  unfold fCL
  rw [Real.sinh_eq, Real.cosh_eq]
  have h4 : (3 : ℝ) < Real.exp 4 := by
    have := Real.add_one_lt_exp (x := 4) (by norm_num); linarith
  have hm : Real.exp (-2) = (Real.exp 2)⁻¹ := Real.exp_neg 2
  have h22 : Real.exp 2 * Real.exp 2 = Real.exp 4 := by rw [← Real.exp_add]; norm_num
  have hp : 0 < Real.exp 2 := Real.exp_pos 2
  rw [hm]
  have : 2 * ((Real.exp 2 - (Real.exp 2)⁻¹) / 2) - (Real.exp 2 + (Real.exp 2)⁻¹) / 2 =
      (Real.exp 2 * Real.exp 2 - 3) / (2 * Real.exp 2) := by field_simp; ring
  rw [this]
  apply div_pos _ (by positivity)
  linarith

/-- Eq. (293): there is exactly one u_* > 0 with u_* tanh u_* = 1. -/
theorem exists_unique_uStar : ∃! u : ℝ, 0 < u ∧ u * Real.tanh u = 1 := by
  have hcont : ContinuousOn fCL (Set.Icc 0 2) :=
    fun x _ => (hasDerivAt_fCL x).continuousAt.continuousWithinAt
  obtain ⟨c, hc, hfc⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 2) hcont
    ⟨by rw [fCL_zero]; norm_num, fCL_two_pos.le⟩
  have hc0 : c ≠ 0 := by rintro rfl; rw [fCL_zero] at hfc; norm_num at hfc
  refine ⟨c, ⟨lt_of_le_of_ne hc.1 (Ne.symm hc0), (tanh_eq_iff c).2 hfc⟩, ?_⟩
  rintro y ⟨hy, hy1⟩
  have hfy := (tanh_eq_iff y).1 hy1
  exact fCL_strictMonoOn.injOn (Set.mem_Ici.2 hy.le) (Set.mem_Ici.2 hc.1) (hfy.trans hfc.symm)

/-- The critical parameter u_* (OEIS A085984). -/
noncomputable def uStar : ℝ := Classical.choose exists_unique_uStar

theorem uStar_pos : 0 < uStar := (Classical.choose_spec exists_unique_uStar).1.1
theorem uStar_tanh : uStar * Real.tanh uStar = 1 := (Classical.choose_spec exists_unique_uStar).1.2
theorem uStar_unique {u : ℝ} (hu : 0 < u) (h : u * Real.tanh u = 1) : u = uStar :=
  (Classical.choose_spec exists_unique_uStar).2 u ⟨hu, h⟩

lemma cosh_uStar : Real.cosh uStar = uStar * Real.sinh uStar := by
  have := (tanh_eq_iff uStar).1 uStar_tanh; unfold fCL at this; linarith

lemma sinh_uStar_pos : 0 < Real.sinh uStar := Real.sinh_pos_iff.2 uStar_pos

/-- 1 < u_* < 2. -/
theorem uStar_bounds : 1 < uStar ∧ uStar < 2 := by
  have hf : fCL uStar = 0 := (tanh_eq_iff uStar).1 uStar_tanh
  constructor
  · by_contra h
    rw [not_lt] at h
    -- for 0 < u ≤ 1, u sinh u < cosh u
    have : uStar * Real.sinh uStar < Real.cosh uStar := by
      have h1 : uStar * Real.sinh uStar ≤ Real.sinh uStar := by
        nlinarith [sinh_uStar_pos]
      have h2 : Real.sinh uStar < Real.cosh uStar := Real.sinh_lt_cosh uStar
      linarith
    unfold fCL at hf; linarith
  · by_contra h
    rw [not_lt] at h
    have := fCL_strictMonoOn.monotoneOn (Set.mem_Ici.2 (by norm_num : (0:ℝ) ≤ 2))
      (Set.mem_Ici.2 uStar_pos.le) h
    linarith [fCL_two_pos]

/-- The Carlini–Laplace constant λ_CL = u_*/cosh u_* (OEIS A033259). -/
noncomputable def lambdaCL : ℝ := uStar / Real.cosh uStar

/-- Eq. (294): λ_CL = u_*/cosh u_* = 1/sinh u_* = √(u_*² - 1). -/
theorem lambdaCL_eq : lambdaCL = 1 / Real.sinh uStar ∧ lambdaCL = Real.sqrt (uStar ^ 2 - 1) := by
  have hs := sinh_uStar_pos
  have hc := cosh_uStar
  have hu := uStar_pos
  constructor
  · unfold lambdaCL; rw [hc]; field_simp
  · have hsq : (uStar ^ 2 - 1) * Real.sinh uStar ^ 2 = 1 := by
      have := Real.cosh_sq uStar
      rw [hc] at this; nlinarith [this]
    have h1 : lambdaCL = 1 / Real.sinh uStar := by unfold lambdaCL; rw [hc]; field_simp
    rw [h1]
    have hpos : 0 < uStar ^ 2 - 1 := by
      by_contra h; rw [not_lt] at h; nlinarith [sq_nonneg (Real.sinh uStar)]
    rw [eq_comm, Real.sqrt_eq_iff_mul_self_eq hpos.le (by positivity)]
    field_simp
    linarith

theorem lambdaCL_pos : 0 < lambdaCL := by
  unfold lambdaCL; exact div_pos uStar_pos (Real.cosh_pos _)

/-! ### Unique maximum and the tangent bicone -/

/-- Strict tangent-line inequality for cosh: cosh y > cosh x + sinh x (y - x), y ≠ x. -/
lemma cosh_tangent_lt {x y : ℝ} (h : y ≠ x) :
    Real.cosh x + Real.sinh x * (y - x) < Real.cosh y := by
  set d := y - x with hd
  have hd0 : d ≠ 0 := sub_ne_zero.2 h
  have h1 := Real.add_one_lt_exp hd0
  have h2 := Real.add_one_lt_exp (neg_ne_zero.2 hd0)
  have e1 : Real.exp y = Real.exp x * Real.exp d := by rw [← Real.exp_add]; congr 1; ring
  have e2 : Real.exp (-y) = Real.exp (-x) * Real.exp (-d) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [Real.cosh_eq, Real.cosh_eq, Real.sinh_eq, e1, e2]
  nlinarith [mul_pos (Real.exp_pos x) (sub_pos.2 h1), mul_pos (Real.exp_pos (-x)) (sub_pos.2 h2)]

/-- The supporting line: U sinh u_* ≤ cosh U for all U, with equality only at U = u_*. -/
lemma mul_sinh_uStar_lt_cosh {U : ℝ} (h : U ≠ uStar) : U * Real.sinh uStar < Real.cosh U := by
  have := cosh_tangent_lt h
  rw [cosh_uStar] at this; linarith

/-- Eq. (292), first form: h/(2R) = U/cosh U for h = 2aU, R = a cosh U, a > 0. -/
theorem catenoid_aspect (a U : ℝ) (ha : 0 < a) :
    (2 * a * U) / (2 * (a * Real.cosh U)) = U / Real.cosh U := by
  have := (Real.cosh_pos U).ne'
  field_simp

/-- Eq. (292), Eulerian form: U/cosh U = U/(1 + (U²/2) r_E(iU)²). -/
theorem catenoid_aspect_eulerian (U : ℝ) :
    U / Real.cosh U = U / (1 + U ^ 2 / 2 * rEi U ^ 2) := by
  rw [sq_mul_rEi_sq]; ring_nf

/-- Eq. (292) with the entire kernel of Eq. (1): U/cosh U = U/(1 + (U²/2) r_E(iU)²) in ℂ. -/
theorem catenoid_aspect_eulerian_rEc (U : ℝ) :
    ((U / Real.cosh U : ℝ) : ℂ) = (U : ℂ) / (1 + (U : ℂ) ^ 2 / 2 * rEc (Complex.I * U) ^ 2) := by
  rw [catenoid_aspect_eulerian, rEc_I_mul]; push_cast; ring

/-- Theorem 7.26: U/cosh U ≤ λ_CL for every real U, with equality iff U = u_*. -/
theorem aspect_unique_max (U : ℝ) :
    U / Real.cosh U ≤ lambdaCL ∧ (U / Real.cosh U = lambdaCL ↔ U = uStar) := by
  have hcU := Real.cosh_pos U
  have hs := sinh_uStar_pos
  have hl : lambdaCL = 1 / Real.sinh uStar := lambdaCL_eq.1
  have key : ∀ V, V ≠ uStar → V / Real.cosh V < lambdaCL := by
    intro V hV
    have := mul_sinh_uStar_lt_cosh hV
    rw [hl, div_lt_div_iff₀ (Real.cosh_pos V) hs]
    linarith
  refine ⟨?_, ?_⟩
  · by_cases h : U = uStar
    · subst h; rfl
    · exact (key U h).le
  · constructor
    · intro hU; by_contra h; exact (key U h).ne hU
    · rintro rfl; rfl

/-- The maximal inequality |u|/λ_CL ≤ cosh u, with equality iff |u| = u_*. -/
theorem bicone_inside (u : ℝ) :
    |u| / lambdaCL ≤ Real.cosh u ∧ (|u| / lambdaCL = Real.cosh u ↔ |u| = uStar) := by
  have hl := lambdaCL_pos
  have hc : Real.cosh u = Real.cosh |u| := (Real.cosh_abs u).symm
  have h := aspect_unique_max |u|
  rw [hc]
  have hcp := Real.cosh_pos |u|
  refine ⟨?_, ?_⟩
  · rw [div_le_iff₀ hl]; have := h.1; rw [div_le_iff₀ hcp] at this; linarith
  · rw [← h.2]
    constructor
    · intro e; field_simp at e ⊢; linarith
    · intro e; field_simp at e ⊢; linarith

/-- The whole bicone √(x²+y²) = |z|/λ_CL lies inside or on the catenoid of scale a > 0:
its radius at height z never exceeds the catenoid radius a cosh(z/a). -/
theorem bicone_subset_catenoid (a z : ℝ) (ha : 0 < a) :
    |z| / lambdaCL ≤ a * Real.cosh (z / a) := by
  have h := (bicone_inside (z / a)).1
  rw [abs_div, abs_of_pos ha] at h
  have hl := lambdaCL_pos
  calc |z| / lambdaCL = a * (|z| / a / lambdaCL) := by field_simp
    _ ≤ a * Real.cosh (z / a) := by gcongr

/-- Tangency along the boundary circles |u| = u_*: equal radii and equal slopes,
cosh u_* = u_*/λ_CL and sinh u_* = 1/λ_CL. -/
theorem bicone_tangent :
    Real.cosh uStar = uStar / lambdaCL ∧ Real.sinh uStar = 1 / lambdaCL := by
  have hl : lambdaCL = 1 / Real.sinh uStar := lambdaCL_eq.1
  have hs := sinh_uStar_pos.ne'
  refine ⟨?_, ?_⟩
  · rw [hl, cosh_uStar]; field_simp
  · rw [hl]; field_simp

/-! ### The classical defining equation -/

lemma sqrt_one_add_lambdaCL_sq : Real.sqrt (1 + lambdaCL ^ 2) = uStar := by
  have h2 := lambdaCL_eq.2
  have hpos : 0 ≤ uStar ^ 2 - 1 := by
    have := Real.sqrt_nonneg (uStar ^ 2 - 1)
    by_contra h; rw [not_le] at h
    have hs := sinh_uStar_pos
    have : lambdaCL = 0 := by rw [h2]; exact Real.sqrt_eq_zero_of_nonpos h.le
    exact (lambdaCL_pos.ne') this
  rw [h2, Real.sq_sqrt hpos]
  rw [show 1 + (uStar ^ 2 - 1) = uStar ^ 2 by ring, Real.sqrt_sq uStar_pos.le]

/-- λ_CL satisfies λ e^{√(1+λ²)} = 1 + √(1+λ²), the classical defining equation of the
convergence threshold of the series solution of Kepler's equation. -/
theorem lambdaCL_laplace_equation :
    lambdaCL * Real.exp (Real.sqrt (1 + lambdaCL ^ 2)) = 1 + Real.sqrt (1 + lambdaCL ^ 2) := by
  rw [sqrt_one_add_lambdaCL_sq, lambdaCL_eq.1]
  have hs := sinh_uStar_pos
  have hc := cosh_uStar
  -- e^{u} = cosh u + sinh u = (u + 1) sinh u
  have he : Real.exp uStar = Real.cosh uStar + Real.sinh uStar := by
    rw [Real.cosh_eq, Real.sinh_eq]; ring
  rw [he, hc]; field_simp; ring

/-- λ_CL is the only positive solution of the classical equation. -/
theorem laplace_equation_unique {l : ℝ} (hl : 0 < l)
    (h : l * Real.exp (Real.sqrt (1 + l ^ 2)) = 1 + Real.sqrt (1 + l ^ 2)) : l = lambdaCL := by
  set s := Real.sqrt (1 + l ^ 2) with hsdef
  have hs2 : s ^ 2 = 1 + l ^ 2 := Real.sq_sqrt (by positivity)
  have hs1 : 1 < s := by
    rw [hsdef, Real.lt_sqrt (by norm_num)]; nlinarith
  have hspos : 0 < s := by linarith
  -- square: (s² - 1) e^{2s} = (1 + s)²  ⇒  (s - 1) e^{2s} = s + 1
  have hE : Real.exp s * Real.exp s = Real.exp (2 * s) := by rw [← Real.exp_add]; ring_nf
  have hl2' : l ^ 2 = (s - 1) * (s + 1) := by linear_combination -hs2
  have hsq : l ^ 2 * Real.exp (2 * s) = (1 + s) ^ 2 := by rw [← hE, ← h]; ring
  rw [hl2'] at hsq
  have h2 : (s - 1) * Real.exp (2 * s) = s + 1 := by
    have hne : (s + 1) ≠ 0 := by linarith
    have : (s + 1) * ((s - 1) * Real.exp (2 * s)) = (s + 1) * (s + 1) := by
      linear_combination hsq
    exact mul_left_cancel₀ hne this
  -- hence s tanh s = 1
  have htanh : s * Real.tanh s = 1 := by
    rw [tanh_eq_iff]
    unfold fCL
    rw [Real.sinh_eq, Real.cosh_eq]
    have hp : 0 < Real.exp s := Real.exp_pos s
    have hm : Real.exp (-s) * Real.exp s = 1 := by rw [← Real.exp_add]; simp
    have this' : (s - 1) * (Real.exp s * Real.exp s) = s + 1 := by rw [hE]; exact h2
    have key : (s * ((Real.exp s - Real.exp (-s)) / 2) - (Real.exp s + Real.exp (-s)) / 2) *
        Real.exp s = 0 := by
      linear_combination (1 / 2) * this' - ((s + 1) / 2) * hm
    exact (mul_eq_zero.1 key).resolve_right hp.ne'
  have hsu : s = uStar := uStar_unique hspos htanh
  have hl2 : l = Real.sqrt (s ^ 2 - 1) := by
    rw [hs2, show 1 + l ^ 2 - 1 = l ^ 2 by ring, Real.sqrt_sq hl.le]
  rw [hl2, hsu, ← lambdaCL_eq.2]

/-! ### The opening angle -/

/-- Eq. (295): α_CL := 2 arccot(λ_CL), written with Mathlib's arctan as 2 arctan(1/λ_CL). -/
noncomputable def alphaCL : ℝ := 2 * Real.arctan (1 / lambdaCL)

theorem alphaCL_props :
    alphaCL = Real.pi - 2 * Real.arctan lambdaCL ∧ Real.tan (alphaCL / 2) = 1 / lambdaCL ∧
      0 < alphaCL ∧ alphaCL < Real.pi ∧ alphaCL = 2 * Real.arctan (Real.sinh uStar) := by
  have hl := lambdaCL_pos
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold alphaCL
    rw [one_div, Real.arctan_inv_of_pos hl]; ring
  · unfold alphaCL; rw [mul_div_cancel_left₀ _ two_ne_zero, Real.tan_arctan]
  · unfold alphaCL; have := Real.arctan_pos.2 (one_div_pos.2 hl); linarith
  · unfold alphaCL; have := Real.arctan_lt_pi_div_two (1 / lambdaCL); linarith
  · unfold alphaCL; rw [bicone_tangent.2.symm]

/-- The half-angle α_CL/2 is the angle between the axis and a generator (|z|/λ, z) of the
bicone: its tangent is the ratio radius/height = 1/λ_CL. -/
theorem bicone_half_angle (z : ℝ) (hz : z ≠ 0) :
    Real.tan (alphaCL / 2) = (|z| / lambdaCL) / |z| := by
  rw [alphaCL_props.2.1]
  have : |z| ≠ 0 := abs_ne_zero.2 hz
  field_simp

end M15
