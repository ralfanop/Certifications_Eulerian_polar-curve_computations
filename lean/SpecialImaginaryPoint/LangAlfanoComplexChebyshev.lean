import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Tactic

/-! OEIS A049310 (Wolfdieter Lang, 2023-06-05, acknowledging Roberto Alfano).
The coordinate theta is a lift of x = 2 cos theta. No global inverse cosine
or globally single-valued continuation in x is presumed. -/
namespace M14.LangAlfano
noncomputable section
open Complex

def profile (z : ℂ) : ℂ := if z = 0 then 1 else Complex.sin (z/2)/(z/2)

def liftedS (nu theta : ℂ) : ℂ :=
  Complex.sin ((nu+1)*theta)/Complex.sin theta

theorem liftedS_zero (theta : ℂ) (h : Complex.sin theta ≠ 0) :
    liftedS 0 theta = 1 := by
  simp [liftedS,h]

theorem liftedS_one (theta : ℂ) (h : Complex.sin theta ≠ 0) :
    liftedS 1 theta = 2*Complex.cos theta := by
  unfold liftedS
  rw [show (1+1:ℂ)*theta=theta+theta by ring,Complex.sin_add]
  apply (div_eq_iff h).2
  ring

theorem liftedS_recurrence (nu theta : ℂ) (h : Complex.sin theta ≠ 0) :
    liftedS (nu+1) theta = 2*Complex.cos theta*liftedS nu theta -
      liftedS (nu-1) theta := by
  unfold liftedS
  have ha : (nu+1+1)*theta=(nu+1)*theta+theta := by ring
  have hb : (nu-1+1)*theta=(nu+1)*theta-theta := by ring
  rw [ha,hb,Complex.sin_add,Complex.sin_sub]
  field_simp [h]
  <;> ring

/-- Agreement with the actual Mathlib scaled Chebyshev polynomial S(n,x). -/
theorem liftedS_nat (n : ℕ) (theta : ℂ) (h : Complex.sin theta ≠ 0) :
    liftedS (n:ℂ) theta =
      (Polynomial.Chebyshev.S ℂ (n:ℤ)).eval (2*Complex.cos theta) := by
  have hp : ∀ k : ℕ,
      liftedS (k:ℂ) theta =
        (Polynomial.Chebyshev.S ℂ (k:ℤ)).eval (2*Complex.cos theta) ∧
      liftedS ((k:ℂ)+1) theta =
        (Polynomial.Chebyshev.S ℂ ((k:ℤ)+1)).eval (2*Complex.cos theta) := by
    intro k
    induction k with
    | zero =>
      constructor
      · simpa using liftedS_zero theta h
      · simpa using liftedS_one theta h
    | succ k ih =>
      push_cast
      constructor
      · exact ih.2
      · rw [show (k:ℂ)+1+1=((k:ℂ)+1)+1 by ring,
            liftedS_recurrence ((k:ℂ)+1) theta h,
            show (k:ℂ)+1-1=(k:ℂ) by ring,ih.1,ih.2]
        rw [show (k:ℤ)+1+1=(k:ℤ)+2 by omega,
          Polynomial.Chebyshev.S_add_two,Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_X]
  exact (hp n).1

/-- Identity with the Eulerian sinc profile; no singular 0/0 convention used. -/
theorem liftedS_profile (nu theta : ℂ) (h : Complex.sin theta ≠ 0)
    (hn : nu+1 ≠ 0) :
    liftedS nu theta = (nu+1)*profile (2*(nu+1)*theta)/profile (2*theta) := by
  have ht : theta ≠ 0 := by
    intro hz
    apply h
    simp [hz]
  have ha : 2*(nu+1)*theta ≠ 0 := by exact mul_ne_zero (mul_ne_zero (by norm_num) hn) ht
  have hb : 2*theta ≠ 0 := mul_ne_zero (by norm_num) ht
  simp only [liftedS,profile,if_neg ha,if_neg hb,
    show (2*(nu+1)*theta)/2=(nu+1)*theta by ring,
    show 2*theta/2=theta by ring]
  field_simp [ht,hn,h]
  <;> ring

theorem liftedS_minus_one (theta : ℂ) :
    liftedS (-1) theta = 0 := by simp [liftedS]

/-- Corrected OEIS x=0 formula for arbitrary complex order. -/
theorem liftedS_at_zero_x (nu : ℂ) :
    liftedS nu ((Real.pi:ℂ)/2) = Complex.cos (nu*(Real.pi:ℂ)/2) := by
  unfold liftedS
  rw [show (nu+1)*((Real.pi:ℂ)/2)=nu*(Real.pi:ℂ)/2+(Real.pi:ℂ)/2 by ring,
    Complex.sin_add_pi_div_two,Complex.sin_pi_div_two,div_one]

theorem liftedS_neg_theta (nu theta : ℂ) :
    liftedS nu (-theta) = liftedS nu theta := by
  unfold liftedS
  rw [mul_neg,Complex.sin_neg,Complex.sin_neg,neg_div_neg_eq]

/-- Nonintegral degree need not descend to x = 2 cos theta. -/
theorem liftedS_half_monodromy (theta : ℂ) :
    liftedS (1/2) (theta+2*(Real.pi:ℂ)) = -liftedS (1/2) theta := by
  unfold liftedS
  rw [show ((1/2:ℂ)+1)*(theta+2*(Real.pi:ℂ))=
      (((1/2:ℂ)+1)*theta+(Real.pi:ℂ))+2*(Real.pi:ℂ) by ring,
    Complex.sin_add_two_pi,Complex.sin_add_pi,Complex.sin_add_two_pi,neg_div]

theorem half_no_global_descent :
    ¬ ∃ F : ℂ → ℂ, ∀ theta : ℂ, Complex.sin theta ≠ 0 →
      F (2*Complex.cos theta)=liftedS (1/2) theta := by
  intro ⟨F,hF⟩
  let t : ℂ := (Real.pi:ℂ)/3
  have ht : Complex.sin t ≠ 0 := by
    have hp : 0 < Real.sin (Real.pi/3) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    have hh : Complex.sin t = (Real.sin (Real.pi/3):ℂ) := by
      dsimp [t]
      simpa only [Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_sin] using
        (rfl : ((Real.sin (Real.pi/3):ℝ):ℂ) = ((Real.sin (Real.pi/3):ℝ):ℂ))
    rw [hh]
    exact_mod_cast hp.ne'
  have ht' : Complex.sin (t+2*(Real.pi:ℂ)) ≠ 0 := by
    rwa [Complex.sin_add_two_pi]
  have h1 := hF t ht
  have h2 := hF (t+2*(Real.pi:ℂ)) ht'
  rw [Complex.cos_add_two_pi,liftedS_half_monodromy,h1] at h2
  have hn : liftedS (1/2) t ≠ 0 := by
    unfold liftedS
    rw [show ((1/2:ℂ)+1)*t=(Real.pi:ℂ)/2 by dsimp [t]; ring,
      Complex.sin_pi_div_two]
    exact div_ne_zero one_ne_zero ht
  apply hn
  linear_combination (1/2:ℂ)*h2

#print axioms liftedS_zero
#print axioms liftedS_one
#print axioms liftedS_recurrence
#print axioms liftedS_nat
#print axioms liftedS_profile
#print axioms liftedS_minus_one
#print axioms liftedS_at_zero_x
#print axioms liftedS_neg_theta
#print axioms liftedS_half_monodromy
#print axioms half_no_global_descent
end
end M14.LangAlfano
