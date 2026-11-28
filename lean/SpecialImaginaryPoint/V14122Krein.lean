import Mathlib
open Matrix
noncomputable section
namespace Manuscript14V14122Krein

def J : Matrix (Fin 2) (Fin 2) ℝ := !![1,0;0,-1]
def U (c s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![c,s;s,c]
def S (c s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![c,-s;s,-c]

theorem boost_preserves (c s : ℝ) (h : c^2-s^2=1) :
    (U c s).transpose * J * U c s = J := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [U,J,Matrix.mul_apply,Fin.sum_univ_succ] <;> nlinarith

theorem symmetry_square (c s : ℝ) (h : c^2-s^2=1) :
    S c s * S c s = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [S,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.one_apply] <;> nlinarith

theorem symmetry_conjugation (c s : ℝ) :
    U c s * J * U c (-s) = S (c^2+s^2) (2*c*s) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [U,J,S,Matrix.mul_apply,Fin.sum_univ_succ] <;> ring

theorem symmetry_product (c s : ℝ) : S c s * J = U c s := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [S,J,U,Matrix.mul_apply,Fin.sum_univ_succ]

theorem special_square : S (Real.sqrt 2) 1 * S (Real.sqrt 2) 1 = 1 := by
  apply symmetry_square
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]

theorem special_angular :
    2*(Real.sqrt 2-1)/(1+(Real.sqrt 2-1)^2) = 1/Real.sqrt 2 := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hp : Real.sqrt 2 ≠ 0 := by positivity
  have hd : 1+(Real.sqrt 2-1)^2 ≠ 0 := by positivity
  field_simp [hp,hd] <;> nlinarith

/-- Explicit PT companion generator and indefinite Gram matrix. -/
def H (g a : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0,0,1,0;0,0,0,1;1,(g:ℂ),Complex.I*(a:ℂ),0;(g:ℂ),1,0,-Complex.I*(a:ℂ)]
def W (g : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![(g:ℂ),1,0,0;1,(g:ℂ),0,0;0,0,0,1;0,0,1,0]

theorem indefinite_adjoint (g a : ℝ) : (H g a).conjTranspose * W g = W g * H g a := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [H,W,Matrix.conjTranspose_apply,Matrix.mul_apply,Fin.sum_univ_succ] <;> ring

def N (g a : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![(a:ℂ)^2,2*(g:ℂ),2*Complex.I*(a:ℂ),0;
     2*(g:ℂ),(a:ℂ)^2,0,-2*Complex.I*(a:ℂ);
     2*Complex.I*(a:ℂ),2*Complex.I*(g:ℂ)*(a:ℂ),-(a:ℂ)^2,2*(g:ℂ);
     -2*Complex.I*(g:ℂ)*(a:ℂ),-2*Complex.I*(a:ℂ),2*(g:ℂ),-(a:ℂ)^2]

theorem numerator_identity (g a : ℝ) :
    N g a = (2:ℂ) • (H g a * H g a) - (2-(a:ℂ)^2) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [N,H,Matrix.mul_apply,Matrix.one_apply,Fin.sum_univ_succ] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

theorem numerator_square (g a : ℝ) :
    N g a * N g a =
      (4*(g:ℂ)^2+(a:ℂ)^4-4*(a:ℂ)^2) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [N,Matrix.mul_apply,Matrix.one_apply,Fin.sum_univ_succ] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

theorem discriminant_scale (g a : ℝ)
    (h : g^2 = 1-(2-a^2)^2/8) :
    4*g^2+a^4-4*a^2 = (2-a^2)^2/2 := by
  linear_combination 4*h

#print axioms boost_preserves
#print axioms symmetry_square
#print axioms symmetry_conjugation
#print axioms symmetry_product
#print axioms special_square
#print axioms special_angular
#print axioms indefinite_adjoint
#print axioms numerator_identity
#print axioms numerator_square
#print axioms discriminant_scale
end Manuscript14V14122Krein
