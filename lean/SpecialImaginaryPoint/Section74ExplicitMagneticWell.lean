import Mathlib

/-! Concrete two-dimensional polynomial vector potential for M14 §7.4.
This constructs a confining field and verifies its curl and minimum.
It does not assert the Friedrichs domain or diamagnetic semigroup theorem. -/
noncomputable section
namespace Manuscript14.ExplicitMagneticWell

def A₁ (_x _y : ℝ) : ℝ := 0
def A₂ (b k x y : ℝ) : ℝ := b*x + k*(x^3/3+x*y^2)
def B (b k x y : ℝ) : ℝ := b+k*(x^2+y^2)

theorem potential_deriv_x (b k x y : ℝ) :
    HasDerivAt (fun t => A₂ b k t y) (B b k x y) x := by
  have h1 := (hasDerivAt_id x).const_mul b
  have h2 := ((hasDerivAt_id x).pow 3).div_const 3
  have h3 := (hasDerivAt_id x).mul_const (y^2)
  have hh := h1.add ((h2.add h3).const_mul k)
  convert hh using 1
  · funext t
    simp only [Pi.add_apply, id_eq]
    dsimp [A₂]
    ring
  · dsimp [B]
    ring

theorem curl_eq (b k x y : ℝ) :
    deriv (fun t => A₂ b k t y) x - deriv (fun t => A₁ x t) y =
      B b k x y := by
  rw [(potential_deriv_x b k x y).deriv]
  simp [A₁]

theorem global_confinement (b k x y : ℝ) (hk : 0 < k) :
    b ≤ B b k x y := by
  unfold B
  nlinarith [mul_nonneg hk.le (add_nonneg (sq_nonneg x) (sq_nonneg y))]

theorem unique_minimum (b k x y : ℝ) (hk : 0 < k) :
    B b k x y = b ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    unfold B at h
    have hz : x^2+y^2 = 0 := by
      have hm : k*(x^2+y^2) = 0 := by linarith
      exact (mul_eq_zero.mp hm).resolve_left hk.ne'
    constructor
    · by_contra hx
      nlinarith [sq_pos_of_ne_zero hx, sq_nonneg y]
    · by_contra hy
      nlinarith [sq_pos_of_ne_zero hy, sq_nonneg x]
  · rintro ⟨rfl,rfl⟩
    simp [B]

/-- Algebraic form splitting underlying the shifted comparison (given the
actual magnetic quadratic form lower bound q ≥ h(b*m+k*w)). -/
theorem shifted_form_split (h b k q m w : ℝ) (hh : 0 < h)
    (hh1 : h ≤ 1) (hq : h*(b*m+k*w) ≤ q) :
    (q-h*b*m)/h^2 ≥ q/h + (1-h)*k*w/h - b*m := by
  have hn : 0 ≤ (1-h)*(q-h*(b*m+k*w)) :=
    mul_nonneg (sub_nonneg.mpr hh1) (sub_nonneg.mpr hq)
  apply (le_div_iff₀ (sq_pos_of_pos hh)).2
  have he : (q/h+(1-h)*k*w/h-b*m)*h^2 =
      h*q+(1-h)*k*w*h-b*m*h^2 := by field_simp [hh.ne'] <;> ring
  rw [he]
  nlinarith [hn]

#print axioms potential_deriv_x
#print axioms curl_eq
#print axioms global_confinement
#print axioms unique_minimum
#print axioms shifted_form_split
end Manuscript14.ExplicitMagneticWell
