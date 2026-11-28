import Mathlib
open Matrix
open scoped ComplexOrder
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

/-- The characteristic determinant of the actual 4-by-4 generator. -/
theorem characteristic_determinant (g a : ℝ) (y : ℂ) :
    Matrix.det (y • (1 : Matrix (Fin 4) (Fin 4) ℂ) - H g a) =
      y^4 + ((a:ℂ)^2-2)*y^2 + 1-(g:ℂ)^2 := by
  rw [Matrix.det_succ_row_zero]
  simp [Matrix.det_fin_three,H,Matrix.one_apply,Fin.sum_univ_succ,Fin.succAbove]
  <;> norm_num [Fin.succAbove,Fin.castSucc,Fin.succ] <;> ring_nf <;> (try simp [Complex.I_sq]) <;> ring

def sigma1 : Matrix (Fin 2) (Fin 2) ℂ := !![0,1;1,0]
def sigma2 : Matrix (Fin 2) (Fin 2) ℂ := !![0,-Complex.I;Complex.I,0]
def sigma3 : Matrix (Fin 2) (Fin 2) ℂ := !![1,0;0,-1]
def xi1 : Matrix (Fin 2) (Fin 2) ℂ := (2:ℂ) • (sigma1 * sigma3)
def xi2 : Matrix (Fin 2) (Fin 2) ℂ := (2:ℂ) • (sigma2 * sigma3)
def comm (X Y : Matrix (Fin 2) (Fin 2) ℂ) := X*Y-Y*X

theorem angular_commutator : comm xi1 xi2 = (-8*Complex.I) • sigma3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [comm,xi1,xi2,sigma1,sigma2,sigma3,Matrix.mul_apply,Fin.sum_univ_succ] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

theorem angular_curvature :
    (1/4:ℂ) • comm (comm xi1 xi2) xi2 = (-4:ℂ) • xi1 := by
  rw [angular_commutator]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [comm,xi1,xi2,sigma1,sigma2,sigma3,Matrix.mul_apply,Fin.sum_univ_succ] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

def dp (g a : ℝ) := 2*g+a^2
def dm (g a : ℝ) := 2*g-a^2
def cp (g a : ℝ) := 2*a*(g+1)
def cm (g a : ℝ) := 2*a*(g-1)
def dd (g a : ℝ) := 4*g^2+a^4-4*a^2

/-- Unnormalised change to the two coupled parity blocks, followed by square completion. -/
def chol (g a : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1,1,0,0;1,-1,0,0;
     -Complex.I*(cp g a:ℂ),-Complex.I*(cp g a:ℂ),(dp g a:ℂ),-(dp g a:ℂ);
     -Complex.I*(cm g a:ℂ),Complex.I*(cm g a:ℂ),(dm g a:ℂ),(dm g a:ℂ)]

def diagWeight (g a : ℝ) : Fin 4 → ℂ :=
  ![((g+1)*dd g a/(2*dp g a):ℝ),((1-g)*dd g a/(2*dm g a):ℝ),
    (1/(2*dp g a):ℝ),(1/(2*dm g a):ℝ)]

set_option maxHeartbeats 8000000 in
theorem gram_factorization (g a : ℝ) (hp : dp g a ≠ 0) (hm : dm g a ≠ 0) :
    W g * N g a = (chol g a).conjTranspose * Matrix.diagonal (diagWeight g a) * chol g a := by
  have hp' : (2*(g:ℂ)+(a:ℂ)^2) ≠ 0 := by exact_mod_cast hp
  have hm' : (2*(g:ℂ)-(a:ℂ)^2) ≠ 0 := by exact_mod_cast hm
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [W,N,chol,diagWeight,dp,dm,cp,cm,dd,Matrix.mul_apply,Matrix.diagonal,
      Matrix.conjTranspose_apply,Fin.sum_univ_succ] <;>
    push_cast <;> field_simp [hp',hm'] <;> ring_nf <;>
    (try simp [Complex.I_sq]) <;> ring

theorem chol_injective (g a : ℝ) (hp : dp g a ≠ 0) (hm : dm g a ≠ 0) :
    Function.Injective (chol g a).mulVec := by
  intro v w h
  have h0 := congrFun h (0:Fin 4)
  have h1 := congrFun h (1:Fin 4)
  have h2 := congrFun h (2:Fin 4)
  have h3 := congrFun h (3:Fin 4)
  simp [chol,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] at h0 h1 h2 h3
  have e0 : v 0 = w 0 := by linear_combination (h0+h1)/2
  have e1 : v 1 = w 1 := by linear_combination (h0-h1)/2
  rw [e0,e1] at h2 h3
  have h2' : (dp g a:ℂ)*((v 2-w 2)-(v 3-w 3)) = 0 := by linear_combination h2
  have h3' : (dm g a:ℂ)*((v 2-w 2)+(v 3-w 3)) = 0 := by linear_combination h3
  have h2'' := (mul_eq_zero.mp h2').resolve_left (Complex.ofReal_ne_zero.mpr hp)
  have h3'' := (mul_eq_zero.mp h3').resolve_left (Complex.ofReal_ne_zero.mpr hm)
  have e2 : v 2 = w 2 := by linear_combination (h2''+h3'')/2
  have e3 : v 3 = w 3 := by linear_combination (h3''-h2'')/2
  funext i
  fin_cases i
  · exact e0
  · exact e1
  · exact e2
  · exact e3

/-- Direct global positivity of W*N on the manuscript's entire unbroken positive branch. -/
theorem gram_positive (g a : ℝ) (hg : 0 < g) (ha : a^2 < 2)
    (hf : g^2 = 1-(2-a^2)^2/8) : (W g * N g a).PosDef := by
  have hg1 : g < 1 := by
    nlinarith [sq_pos_of_pos (show 0 < 2-a^2 by linarith)]
  have hp : 0 < dp g a := by unfold dp; positivity
  have hgaps : 0 < (2-a^2)*(1+3*a^2/2) := by
    exact mul_pos (by linarith) (by positivity)
  have hgap : 4*g^2-a^4 = (2-a^2)*(1+3*a^2/2) := by
    linear_combination 4*hf
  have hm : 0 < dm g a := by
    by_contra! hn
    have h := mul_nonpos_of_nonpos_of_nonneg hn hp.le
    unfold dm dp at h
    nlinarith
  have hd : 0 < dd g a := by
    unfold dd
    rw [discriminant_scale g a hf]
    positivity
  rw [gram_factorization g a hp.ne' hm.ne']
  apply Matrix.PosDef.conjTranspose_mul_mul_same
  · apply Matrix.PosDef.diagonal
    intro i
    fin_cases i <;> simp only [diagWeight, Matrix.cons_val_zero, Matrix.cons_val_succ] <;>
      apply Complex.zero_lt_real.mpr <;> positivity
  · exact chol_injective g a hp.ne' hm.ne'

#print axioms characteristic_determinant
#print axioms angular_commutator
#print axioms angular_curvature
#print axioms gram_factorization
#print axioms chol_injective
#print axioms gram_positive

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
