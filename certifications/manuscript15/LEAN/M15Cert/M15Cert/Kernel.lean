/-
Manuscript 15 -- common definitions for the formalisation of Sections 7.9 and 7.11.

The Eulerian kernel of Eq. (1),
  r_E(z) = sin(z/2)/(z/2)  (z ≠ 0),   r_E(0) = 1,
is defined on ℂ (`rEc`) and on ℝ (`rE`).  The Eulerian factor of
Flajolet–Sedgewick is B(u) = (u - 1)/log u with B(1) = 1 (principal logarithm),
and the cardioid is c_Mand(θ) = u/2 - u²/4 with u = e^{iθ}.
Only Mathlib is imported.
-/
import Mathlib

open Complex

namespace M15

/-- The Eulerian kernel on ℂ, Eq. (1) of the manuscript. -/
noncomputable def rEc (z : ℂ) : ℂ := if z = 0 then 1 else Complex.sin (z / 2) / (z / 2)

/-- The Eulerian kernel on ℝ. -/
noncomputable def rE (θ : ℝ) : ℝ := if θ = 0 then 1 else Real.sin (θ / 2) / (θ / 2)

/-- The kernel on the imaginary axis, r_E(iu) = sinh(u/2)/(u/2). -/
noncomputable def rEi (u : ℝ) : ℝ := if u = 0 then 1 else Real.sinh (u / 2) / (u / 2)

lemma rEc_ofReal (θ : ℝ) : rEc (θ : ℂ) = (rE θ : ℂ) := by
  unfold rEc rE
  by_cases h : θ = 0
  · simp [h]
  · have h' : (θ : ℂ) ≠ 0 := by exact_mod_cast h
    simp [h, h', Complex.ofReal_sin, Complex.ofReal_div]

/-- `r_E` is the slope function of `sin` at `0`, evaluated at `z/2`. -/
lemma rEc_eq_dslope (z : ℂ) : rEc z = dslope Complex.sin 0 (z / 2) := by
  unfold rEc
  by_cases h : z = 0
  · simp [h, dslope_same]
  · have h2 : z / 2 ≠ 0 := div_ne_zero h two_ne_zero
    simp only [h, ↓reduceIte]
    rw [dslope_of_ne _ h2, slope_def_field]
    simp

/-- `r_E` is an entire function (Eq. (1): "an even entire function"). -/
theorem rEc_differentiable : Differentiable ℂ rEc := by
  have hd : DifferentiableOn ℂ (dslope Complex.sin 0) Set.univ :=
    (differentiableOn_dslope Filter.univ_mem).2 Complex.differentiable_sin.differentiableOn
  have : rEc = (dslope Complex.sin 0) ∘ fun z : ℂ => z / 2 := by
    funext z; simp [rEc_eq_dslope]
  rw [this]
  exact (differentiableOn_univ.1 hd).comp (differentiable_id.div_const 2)

/-- r_E(iu) = sinh(u/2)/(u/2), with the removable value 1 at u = 0. -/
theorem rEc_I_mul (u : ℝ) : rEc (I * u) = (rEi u : ℂ) := by
  unfold rEc rEi
  by_cases h : u = 0
  · simp [h]
  · have h' : I * (u : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (by exact_mod_cast h)
    simp only [h', h, ↓reduceIte]
    have hs : Complex.sin (I * u / 2) = Complex.sinh (u / 2) * I := by
      rw [show I * (u : ℂ) / 2 = (u / 2 : ℂ) * I by ring, Complex.sin_mul_I]
    rw [hs, show I * (u : ℂ) / 2 = (u / 2 : ℂ) * I by ring,
      mul_div_mul_right _ _ I_ne_zero]
    push_cast
    ring

/-- r_E(2iu) = sinh(u)/u, with the removable value 1 at u = 0. -/
theorem rEc_two_I_mul (u : ℝ) :
    rEc (2 * I * u) = ((if u = 0 then 1 else Real.sinh u / u : ℝ) : ℂ) := by
  have := rEc_I_mul (2 * u)
  rw [show (2 : ℂ) * I * u = I * ((2 * u : ℝ) : ℂ) by push_cast; ring, this]
  unfold rEi
  by_cases h : u = 0
  · simp [h]
  · have h2 : (2 * u) ≠ 0 := mul_ne_zero two_ne_zero h
    simp [h, h2, mul_div_cancel_left₀ u (two_ne_zero' ℝ)]

/-- The basic half-angle identity: (u²/2) r_E(iu)² = cosh u - 1. -/
theorem sq_mul_rEi_sq (u : ℝ) : u ^ 2 / 2 * rEi u ^ 2 = Real.cosh u - 1 := by
  unfold rEi
  by_cases h : u = 0
  · simp [h]
  · simp only [h, ↓reduceIte]
    have hc : Real.cosh u = Real.cosh (2 * (u / 2)) := by ring_nf
    rw [hc, Real.cosh_two_mul, Real.cosh_sq]
    field_simp
    ring

/-- u² r_E(2iu)² = sinh² u. -/
theorem sq_mul_rEi_two_sq (u : ℝ) :
    u ^ 2 * (if u = 0 then 1 else Real.sinh u / u) ^ 2 = Real.sinh u ^ 2 := by
  by_cases h : u = 0
  · simp [h]
  · simp only [h, ↓reduceIte]; field_simp

/-- The Eulerian factor B(u) = (u - 1)/log u, B(1) = 1, principal logarithm. -/
noncomputable def eulerianB (u : ℂ) : ℂ := if u = 1 then 1 else (u - 1) / Complex.log u

/-- The main cardioid of the Mandelbrot set, Eq. (254): c(θ) = u/2 - u²/4, u = e^{iθ}. -/
noncomputable def cMand (θ : ℝ) : ℂ :=
  Complex.exp (θ * I) / 2 - Complex.exp (θ * I) ^ 2 / 4

/-- The half-angle identity u - 1 = iθ r_E(θ) e^{iθ/2}, Eq. (263). -/
theorem exp_sub_one_eq (θ : ℝ) :
    Complex.exp (θ * I) - 1 = I * θ * (rE θ : ℂ) * Complex.exp (θ / 2 * I) := by
  unfold rE
  by_cases h : θ = 0
  · simp [h]
  · simp only [h, ↓reduceIte]
    have hθ : (θ : ℂ) ≠ 0 := by exact_mod_cast h
    have e1 : Complex.exp (θ * I) = Complex.exp (θ / 2 * I) * Complex.exp (θ / 2 * I) := by
      rw [← Complex.exp_add]; ring_nf
    have e2 : (1 : ℂ) = Complex.exp (θ / 2 * I) * Complex.exp (-(θ / 2 * I)) := by
      rw [← Complex.exp_add]; simp
    have hsin : Complex.exp (θ / 2 * I) - Complex.exp (-(θ / 2 * I)) =
        2 * I * Complex.sin (θ / 2) := by
      rw [Complex.sin]; field_simp; ring_nf; simp [Complex.I_sq]; ring_nf
    push_cast
    calc Complex.exp (θ * I) - 1
        = Complex.exp (θ / 2 * I) * (Complex.exp (θ / 2 * I) - Complex.exp (-(θ / 2 * I))) := by
          rw [e1, mul_sub, ← e2]
      _ = I * θ * (Complex.sin (θ / 2) / (θ / 2)) * Complex.exp (θ / 2 * I) := by
          rw [hsin]; field_simp

end M15
