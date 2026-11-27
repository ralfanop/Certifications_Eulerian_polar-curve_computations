import Mathlib

/-! M12 26 November: algebra of parity, fundamental symmetries and curvature.
Source labels eq:ul-krein-geodesic, prop:ul-krein-curvature,
eq:ul-krein-curvature; eq:ul-high-recursion (scalar coefficient solve).
The Hilbert-space exponential, positivity, actual Jacobi spectral
identification, analytical remainders and Bessel expansion are separate.
-/
namespace M12KreinEditorial

def comm {R : Type*} [Ring R] (x y : R) : R := x * y - y * x

section Algebra
variable {R : Type*} [Ring R]

theorem parity_product (S A X : R) (hS : S*S = 1)
    (hX : S*X = -(X*S)) :
    (A*S)*(X*S) = -(A*X) := by
  calc
    (A*S)*(X*S) = A*(S*X)*S := by noncomm_ring
    _ = -(A*X) := by rw [hX]; simp [mul_assoc, hS]

theorem parity_even_product (S A X : R)
    (hA : S*A = -(A*S)) (hX : S*X = -(X*S)) :
    S*(A*X) = (A*X)*S := by
  calc
    S*(A*X) = (S*A)*X := by noncomm_ring
    _ = -(A*(S*X)) := by rw [hA]; noncomm_ring
    _ = (A*X)*S := by rw [hX]; noncomm_ring

theorem parity_even_comm (S A X : R)
    (hA : S*A = -(A*S)) (hX : S*X = -(X*S)) :
    S*comm A X = comm A X*S := by
  unfold comm
  rw [mul_sub, sub_mul, parity_even_product S A X hA hX,
    parity_even_product S X A hX hA]

theorem tangent_square (S A : R) (hS : S*S = 1)
    (hA : S*A = -(A*S)) :
    (2*A*S)*(2*A*S) = -4*(A*A) := by
  calc
    (2*A*S)*(2*A*S) = 4*((A*S)*(A*S)) := by noncomm_ring
    _ = -4*(A*A) := by rw [parity_product S A A hS hA]; noncomm_ring

theorem tangent_comm (S A X : R) (hS : S*S = 1)
    (hA : S*A = -(A*S)) (hX : S*X = -(X*S)) :
    comm (2*A*S) (2*X*S) = -4*comm A X := by
  calc
    comm (2*A*S) (2*X*S) =
        4*((A*S)*(X*S) - (X*S)*(A*S)) := by unfold comm; noncomm_ring
    _ = -4*comm A X := by
      rw [parity_product S A X hS hX, parity_product S X A hS hA]
      unfold comm
      noncomm_ring

theorem curvature_fourfold (S A X C : R) (hS : S*S = 1)
    (hA : S*A = -(A*S)) (hX : S*X = -(X*S)) :
    comm (comm (2*A*S) (2*X*S)) (2*C*S) =
      -8*comm (comm A X) C*S := by
  have hD := parity_even_comm S A X hA hX
  rw [tangent_comm S A X hS hA hX]
  calc
    comm (-4*comm A X) (2*C*S) =
      -8*(comm A X*C*S - C*(S*comm A X)) := by
        unfold comm
        noncomm_ring
    _ = -8*comm (comm A X) C*S := by
      rw [hD]
      unfold comm
      noncomm_ring

theorem twisted_involution (S T U : R) (hS : S*S = 1)
    (hTU : T*U = 1) (hST : S*T = U*S) :
    (T*S)*(T*S) = 1 := by
  calc
    (T*S)*(T*S) = T*(S*T)*S := by noncomm_ring
    _ = 1 := by rw [hST]; calc
      T*(U*S)*S = (T*U)*(S*S) := by noncomm_ring
      _ = 1 := by rw [hTU, hS]; simp

theorem conjugation (S T U : R) (hSU : S*U = T*S) :
    T*S*U = T*T*S := by
  calc
    T*S*U = T*(S*U) := by noncomm_ring
    _ = T*T*S := by rw [hSU]; noncomm_ring

end Algebra

theorem recurrence_coefficient (d k b : ℝ) (hd : d ≠ 0)
    (h : 2*d*b+k=0) : b = -k/(2*d) := by
  apply (eq_div_iff (mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) hd)).2
  linarith [h, show b*(2*d)=2*d*b by ring]

theorem angular_ratio_inverse (x : ℝ) (hx : 0 < x) :
    (1+(x-1)/(x+1))/(1-(x-1)/(x+1)) = x := by
  have hp : x+1 ≠ 0 := by positivity
  have hq : 1-(x-1)/(x+1) ≠ 0 := by
    intro h
    have h' : (x-1)/(x+1)=1 := by linarith
    have hh := (div_eq_iff hp).mp h'
    linarith
  field_simp
  <;> ring

theorem angular_silver_ratio :
    ((1+Real.sqrt 2)-1)/((1+Real.sqrt 2)+1) = Real.sqrt 2-1 := by
  have hsq := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hpos : (1+Real.sqrt 2)+1 ≠ 0 := by positivity
  apply (div_eq_iff hpos).2
  nlinarith

theorem angular_log_three : ((3:ℝ)-1)/(3+1) = 1/2 := by norm_num

end M12KreinEditorial

#print axioms M12KreinEditorial.parity_product
#print axioms M12KreinEditorial.parity_even_product
#print axioms M12KreinEditorial.parity_even_comm
#print axioms M12KreinEditorial.tangent_square
#print axioms M12KreinEditorial.tangent_comm
#print axioms M12KreinEditorial.curvature_fourfold
#print axioms M12KreinEditorial.twisted_involution
#print axioms M12KreinEditorial.conjugation
#print axioms M12KreinEditorial.recurrence_coefficient
#print axioms M12KreinEditorial.angular_ratio_inverse
#print axioms M12KreinEditorial.angular_silver_ratio
#print axioms M12KreinEditorial.angular_log_three
