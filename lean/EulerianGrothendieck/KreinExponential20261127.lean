import EulerianGrothendieck.KreinBilateralJacobi20261127
import EulerianGrothendieck.KreinEditorialAlgebra

/-! M12 Theorem 5.18, (203). Concrete bilateral operators, not a
finite matrix model. The exponential, fundamental symmetry identities
and strictly positive invertible metric are established on the same
Hilbert space as the certified Jacobi construction.
Spectral mapping, canonical geodesic differential equation, angular
operator and asymptotics remain separate. -/
noncomputable section
open scoped InnerProductSpace
namespace M12KreinExponential
open M12BilateralJacobi

def E (u : Bonds) (t : ℝ) : Op :=
  NormedSpace.exp ((t:ℂ) • J u)

theorem E_zero (u : Bonds) : E u 0 = 1 := by
  unfold E
  rw [Complex.ofReal_zero,show (0:ℂ) • J u = (0:Op) from zero_smul ℂ _,NormedSpace.exp_zero]

theorem E_add (u : Bonds) (s t : ℝ) : E u (s+t) = E u s*E u t := by
  have hc : Commute ((s:ℂ) • J u) ((t:ℂ) • J u) :=
    ((Commute.refl (J u)).smul_left (s:ℂ)).smul_right (t:ℂ)
  unfold E
  rw [Complex.ofReal_add,show ((s:ℂ)+(t:ℂ)) • J u = (s:ℂ) • J u + (t:ℂ) • J u from add_smul _ _ _,NormedSpace.exp_add_of_commute hc]

theorem E_inverse (u : Bonds) (t : ℝ) :
    E u t*E u (-t)=1 := by
  rw [← E_add,add_neg_cancel,E_zero]

theorem E_selfAdjoint (u : Bonds) (t : ℝ) : IsSelfAdjoint (E u t) := by
  change star (E u t) = E u t
  unfold E
  rw [NormedSpace.star_exp,star_smul,(J_selfAdjoint u).star_eq]
  simp

theorem parity_E (u : Bonds) (t : ℝ) :
    S0*E u t=E u (-t)*S0 := by
  have h : SemiconjBy S0 ((t:ℂ) • J u) (((-t:ℝ):ℂ) • J u) := by
    change S0*((t:ℂ) • J u)=(((-t:ℝ):ℂ) • J u)*S0
    rw [mul_smul_comm,smul_mul_assoc,parity_anticomm,Complex.ofReal_neg]
    rw [smul_neg,neg_smul]
  unfold E
  simp_rw [NormedSpace.exp_eq_tsum ℂ]
  exact SemiconjBy.tsum_right S0 (NormedSpace.expSeries_summable' (𝕂 := ℂ) _)
    (NormedSpace.expSeries_summable' (𝕂 := ℂ) _) (fun n => (h.pow_right n).smul_right _)

def symmetry (u : Bonds) (t : ℝ) : Op := E u (2*t)*S0

def kreinAdjoint (T : Op) : Op := S0*star T*S0

theorem symmetry_zero (u : Bonds) : symmetry u 0=S0 := by
  simp [symmetry,E_zero]

theorem symmetry_involution (u : Bonds) (t : ℝ) :
    symmetry u t*symmetry u t=1 := by
  unfold symmetry
  exact M12KreinEditorial.twisted_involution S0 (E u (2*t)) (E u (-(2*t)))
    S0_square (E_inverse u (2*t)) (parity_E u (2*t))

theorem symmetry_krein_selfAdjoint (u : Bonds) (t : ℝ) :
    kreinAdjoint (symmetry u t)=symmetry u t := by
  unfold kreinAdjoint symmetry
  rw [star_mul,S0_selfAdjoint.star_eq,(E_selfAdjoint u (2*t)).star_eq]
  calc
    _ = (S0*S0)*E u (2*t)*S0 := by noncomm_ring
    _ = _ := by rw [S0_square,one_mul]

theorem symmetry_conjugation (u : Bonds) (t : ℝ) :
    E u t*S0*E u (-t)=symmetry u t := by
  unfold symmetry
  calc
    _ = E u t*(S0*E u (-t)) := by noncomm_ring
    _ = E u t*(E u t*S0) := by rw [parity_E,neg_neg]
    _ = (E u t*E u t)*S0 := by noncomm_ring
    _ = _ := by rw [← E_add,show t+t=2*t by ring]

theorem metric_eq (u : Bonds) (t : ℝ) :
    S0*symmetry u t=E u (-(2*t)) := by
  unfold symmetry
  calc
    _ = (S0*E u (2*t))*S0 := by noncomm_ring
    _ = (E u (-(2*t))*S0)*S0 := by rw [parity_E]
    _ = E u (-(2*t))*(S0*S0) := by noncomm_ring
    _ = _ := by rw [S0_square,mul_one]

theorem metric_inverse (u : Bonds) (t : ℝ) :
    (S0*symmetry u t)*E u (2*t)=1 ∧
      E u (2*t)*(S0*symmetry u t)=1 := by
  rw [metric_eq]
  exact ⟨by simpa only [neg_neg] using E_inverse u (-(2*t)), E_inverse u (2*t)⟩

theorem E_injective (u : Bonds) (t : ℝ) : Function.Injective (E u t) := by
  intro x y h
  have hi := E_inverse u (-t)
  rw [neg_neg] at hi
  have hx := congrArg (fun T : Op => T x) hi
  have hy := congrArg (fun T : Op => T y) hi
  change E u (-t) (E u t x)=x at hx
  change E u (-t) (E u t y)=y at hy
  rw [h] at hx
  exact hx.symm.trans hy

theorem metric_pair (u : Bonds) (t : ℝ) (x : H) :
    ⟪x,(S0*symmetry u t) x⟫_ℂ = ⟪E u (-t) x,E u (-t) x⟫_ℂ := by
  rw [metric_eq,show -(2*t)=(-t)+(-t) by ring,E_add]
  change ⟪x,E u (-t) (E u (-t) x)⟫_ℂ = _
  exact ((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (E_selfAdjoint u (-t)))
    x (E u (-t) x)).symm

theorem metric_strict_positive (u : Bonds) (t : ℝ) (x : H) (hx : x≠0) :
    0 < (⟪x,(S0*symmetry u t) x⟫_ℂ).re := by
  rw [metric_pair]
  have hn : E u (-t) x≠0 := by
    intro h
    apply hx
    apply E_injective u (-t)
    simpa only [map_zero] using h
  exact (re_inner_self_pos (𝕜 := ℂ)).mpr hn

theorem symmetry_product (u : Bonds) (s t : ℝ) :
    symmetry u t*symmetry u s=E u (2*(t-s)) := by
  unfold symmetry
  calc
    _ = E u (2*t)*(S0*E u (2*s))*S0 := by noncomm_ring
    _ = E u (2*t)*(E u (-(2*s))*S0)*S0 := by rw [parity_E]
    _ = (E u (2*t)*E u (-(2*s)))*(S0*S0) := by noncomm_ring
    _ = _ := by rw [S0_square,mul_one,← E_add,show 2*t+ -(2*s)=2*(t-s) by ring]

theorem transvection_square (u : Bonds) (s t : ℝ) :
    E u (t-s)*E u (t-s)=symmetry u t*symmetry u s := by
  rw [← E_add,symmetry_product,show t-s+(t-s)=2*(t-s) by ring]

theorem transvection_composition (u : Bonds) (r s t : ℝ) :
    E u (t-s)*E u (s-r)=E u (t-r) := by
  rw [← E_add,show t-s+(s-r)=t-r by ring]

end M12KreinExponential
#print axioms M12KreinExponential.E_zero
#print axioms M12KreinExponential.E_add
#print axioms M12KreinExponential.E_inverse
#print axioms M12KreinExponential.E_selfAdjoint
#print axioms M12KreinExponential.parity_E
#print axioms M12KreinExponential.symmetry_zero
#print axioms M12KreinExponential.symmetry_involution
#print axioms M12KreinExponential.symmetry_krein_selfAdjoint
#print axioms M12KreinExponential.symmetry_conjugation
#print axioms M12KreinExponential.metric_eq
#print axioms M12KreinExponential.metric_inverse
#print axioms M12KreinExponential.E_injective
#print axioms M12KreinExponential.metric_pair
#print axioms M12KreinExponential.metric_strict_positive
#print axioms M12KreinExponential.symmetry_product
#print axioms M12KreinExponential.transvection_square
#print axioms M12KreinExponential.transvection_composition
