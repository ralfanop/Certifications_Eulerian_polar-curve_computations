import EulerianGrothendieck.JacobiSmoothCompressions20261127
import Mathlib.Analysis.Matrix.Spectrum

/-! Actual real spectral decomposition of the finite bond cutoff,
extended to the bilateral complex Hilbert space. All coordinate vectors
used for the trace calculation eventually lie in the active block. -/
set_option maxHeartbeats 2000000
noncomputable section
open Finset NormedSpace Set
open scoped ENNReal InnerProductSpace
namespace M12FiniteSpectrum
open M12BilateralJacobi M12DKBilateral M12SmoothCompressions

abbrev sites (N : ℕ) := ↥(Finset.Icc (-(N:ℤ)-1) (N:ℤ))

def liftVec (N : ℕ) (v : sites N → ℂ) : H :=
  ∑ i : sites N, lp.single 2 (i:ℤ) (v i)

theorem lift_inside (N : ℕ) (v : sites N → ℂ) (k : sites N) :
    liftVec N v (k:ℤ) = v k := by
  classical
  unfold liftVec
  rw [lp.coeFn_sum,Finset.sum_apply]
  rw [Finset.sum_eq_single k]
  · exact lp.single_apply_self _ _ _
  · intro i _ hi
    exact lp.single_apply_ne _ _ _ (fun h => hi (Subtype.ext h.symm))
  · simp

theorem lift_outside (N : ℕ) (v : sites N → ℂ) (k : ℤ)
    (hk : k ∉ Finset.Icc (-(N:ℤ)-1) (N:ℤ)) :
    liftVec N v k = 0 := by
  classical
  unfold liftVec
  rw [lp.coeFn_sum,Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  exact lp.single_apply_ne _ _ _ (fun h => hk (h ▸ i.property))

def mat (u : Bonds) (N : ℕ) : Matrix (sites N) (sites N) ℝ :=
  fun i j => (if (i:ℤ)-1=(j:ℤ) then (cut u N).1 i else 0) +
    (if (i:ℤ)+1=(j:ℤ) then (cut u N).1 j else 0)

theorem entry_formula (u : Bonds) (N : ℕ) (i j : sites N) :
    entry (J (cut u N)) i j = (mat u N i j:ℂ) := by
  unfold entry mat
  rw [J_apply]
  by_cases h₁ : (i:ℤ)-1=(j:ℤ) <;> by_cases h₂ : (i:ℤ)+1=(j:ℤ)
  · omega
  · simp [lp.single_apply,h₁,h₂,Ne.symm h₂]
  · simp [lp.single_apply,h₁,h₂,Ne.symm h₁]
  · simp [lp.single_apply,h₁,h₂,Ne.symm h₁,Ne.symm h₂]

theorem matrix_hermitian (u : Bonds) (N : ℕ) : (mat u N).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  rw [star_trivial]
  unfold mat
  by_cases h₁ : (i:ℤ)-1=(j:ℤ) <;> by_cases h₂ : (i:ℤ)+1=(j:ℤ)
  · omega
  · have h₃ : (j:ℤ)+1=(i:ℤ) := by omega
    have h₄ : (j:ℤ)-1≠(i:ℤ) := by omega
    simp [h₁,h₂,h₃,h₄]
  · have h₃ : (j:ℤ)-1=(i:ℤ) := by omega
    have h₄ : (j:ℤ)+1≠(i:ℤ) := by omega
    simp [h₁,h₂,h₃,h₄]
  · have h₃ : (j:ℤ)-1≠(i:ℤ) := by omega
    have h₄ : (j:ℤ)+1≠(i:ℤ) := by omega
    simp [h₁,h₂,h₃,h₄]

theorem cutoff_outside (u : Bonds) (N : ℕ) (x : H) (k : ℤ)
    (hk : k ∉ Finset.Icc (-(N:ℤ)-1) (N:ℤ)) : J (cut u N) x k = 0 := by
  rw [J_apply]
  simp only [Finset.mem_Icc,not_and_or,not_le] at hk
  rcases hk with hk|hk
  · have h₁ : ¬ -(N:ℤ) ≤ k := by omega
    have h₂ : ¬ -(N:ℤ) ≤ k+1 := by omega
    simp [cut,h₁,h₂]
  · have h₁ : ¬ k ≤ (N:ℤ) := by omega
    have h₂ : ¬ k+1 ≤ (N:ℤ) := by omega
    simp [cut,h₁,h₂]

def eigenvalues (u : Bonds) (N : ℕ) := (matrix_hermitian u N).eigenvalues

def basis (u : Bonds) (N : ℕ) := (matrix_hermitian u N).eigenvectorBasis

def eigenvector (u : Bonds) (N : ℕ) (r : sites N) : H :=
  liftVec N (fun i => ((basis u N r) i:ℂ))

theorem eigenvector_action (u : Bonds) (N : ℕ) (r : sites N) :
    J (cut u N) (eigenvector u N r) =
      (eigenvalues u N r:ℂ) • eigenvector u N r := by
  classical
  ext k
  by_cases hk : k ∈ Finset.Icc (-(N:ℤ)-1) (N:ℤ)
  · let i : sites N := ⟨k,hk⟩
    change J (cut u N) (eigenvector u N r) (i:ℤ) =
      (eigenvalues u N r:ℂ) * eigenvector u N r (i:ℤ)
    have h := congrFun ((matrix_hermitian u N).mulVec_eigenvectorBasis r) i
    change (∑ j : sites N, mat u N i j * basis u N r j) =
      eigenvalues u N r * basis u N r i at h
    have hc := congrArg Complex.ofReal h
    push_cast at hc
    rw [eigenvector,lift_inside]
    change J (cut u N) (liftVec N fun j => ((basis u N r) j:ℂ)) i = _
    unfold liftVec
    rw [map_sum,lp.coeFn_sum,Finset.sum_apply]
    convert hc using 1
    apply Finset.sum_congr rfl
    intro j _
    have hs : lp.single 2 (j:ℤ) ((basis u N r) j:ℂ) =
        ((basis u N r) j:ℂ) • (lp.single 2 (j:ℤ) 1 : H) := by
      apply lp.ext
      funext l
      change (lp.single 2 (j:ℤ) ((basis u N r) j:ℂ) : H) l = ((basis u N r) j:ℂ) * (lp.single 2 (j:ℤ) (1:ℂ) : H) l
      by_cases hl : l=(j:ℤ)
      · subst l; simp [lp.single_apply]
      · simp [lp.single_apply,hl,Ne.symm hl]
    rw [hs,map_smul]
    change ((basis u N r) j:ℂ)*entry (J (cut u N)) i j = _
    rw [entry_formula]
    ring
  · rw [cutoff_outside u N _ k hk]
    change 0 = (eigenvalues u N r:ℂ)*eigenvector u N r k
    rw [eigenvector,lift_outside N _ k hk,mul_zero]

theorem eigenvector_ne_zero (u : Bonds) (N : ℕ) (r : sites N) :
    eigenvector u N r ≠ 0 := by
  intro h
  have hz : basis u N r = 0 := by
    ext k
    have he := congrArg (fun x : H => x (k:ℤ)) h
    change liftVec N (fun j => ((basis u N r) j:ℂ)) k = 0 at he
    rw [lift_inside] at he
    change (basis u N r) k = (0:ℝ)
    have he' := congrArg Complex.re he
    simpa using he'
  have hn := (basis u N).norm_eq_one r
  rw [hz,norm_zero] at hn
  norm_num at hn

theorem eigenvalue_interval (u : Bonds) (N : ℕ) (r : sites N) :
    eigenvalues u N r ∈ Icc (-1:ℝ) 1 := by
  let v := eigenvector u N r
  have hv : 0 < ‖v‖ := norm_pos_iff.mpr (eigenvector_ne_zero u N r)
  have h := ((J (cut u N)).le_opNorm v).trans
    (by simpa using mul_le_mul_of_nonneg_right (J_norm_le (cut u N)) hv.le)
  change ‖J (cut u N) (eigenvector u N r)‖ ≤ ‖v‖ at h
  rw [eigenvector_action,norm_smul,Complex.norm_real,Real.norm_eq_abs] at h
  apply abs_le.mp
  by_contra! hn
  have hh := mul_pos (sub_pos.mpr hn) hv
  change 0 < (|eigenvalues u N r|-1)*‖eigenvector u N r‖ at hh
  nlinarith only [h,hh]

theorem basis_expansion (u : Bonds) (N : ℕ) (l : sites N) :
    (lp.single 2 (l:ℤ) 1 : H) =
      ∑ r : sites N, ((basis u N r) l:ℂ) • eigenvector u N r := by
  classical
  have h := (basis u N).sum_repr (EuclideanSpace.single l (1:ℝ))
  have hr (r : sites N) : (basis u N).repr (EuclideanSpace.single l (1:ℝ)) r =
      (basis u N r) l := by
    rw [OrthonormalBasis.repr_apply_apply,EuclideanSpace.inner_single_right]
    simp
  simp_rw [hr] at h
  ext k
  rw [lp.coeFn_sum,Finset.sum_apply]
  by_cases hk : k ∈ Finset.Icc (-(N:ℤ)-1) (N:ℤ)
  · let i : sites N := ⟨k,hk⟩
    have he := congrArg (fun x : EuclideanSpace ℝ (sites N) => ⟪EuclideanSpace.single i (1:ℝ), x⟫_ℝ) h
    simp only [inner_sum,inner_smul_right,EuclideanSpace.inner_single_left,map_one,one_mul] at he
    change (∑ r : sites N, (basis u N r) l * (basis u N r) i) =
      EuclideanSpace.single l (1:ℝ) i at he
    have hc := congrArg Complex.ofReal he
    push_cast at hc
    change lp.single 2 (l:ℤ) 1 (i:ℤ) =
      ∑ r : sites N, ((basis u N r) l:ℂ)*eigenvector u N r (i:ℤ)
    simp_rw [eigenvector,lift_inside]
    rw [hc]
    by_cases hi : i=l
    · subst i; simp [lp.single_apply,EuclideanSpace.single_apply]
    · have hn : (i:ℤ)≠(l:ℤ) := fun hh => hi (Subtype.ext hh)
      simp [lp.single_apply,EuclideanSpace.single_apply,hi,hn]
  · have hn : k≠(l:ℤ) := fun h => hk (h ▸ l.property)
    rw [lp.single_apply_ne _ _ _ hn]
    apply Eq.symm
    apply Finset.sum_eq_zero
    intro r _
    change ((basis u N r) l:ℂ)*eigenvector u N r k=0
    rw [eigenvector,lift_outside N _ k hk,mul_zero]

theorem exp_eigenvector (u : Bonds) (N : ℕ) (r : sites N) (t : ℝ) :
    E (cut u N) t (eigenvector u N r) =
      Complex.exp (((t:ℂ)*Complex.I)*(eigenvalues u N r:ℂ)) • eigenvector u N r := by
  let v := eigenvector u N r
  let a : ℂ := ((t:ℂ)*Complex.I)*(eigenvalues u N r:ℂ)
  have hA : A (cut u N) t v = a • v := by
    unfold A
    change ((t:ℂ)*Complex.I) • J (cut u N) v = _
    rw [show v = eigenvector u N r from rfl,eigenvector_action,smul_smul]
  have hp (n : ℕ) : ((A (cut u N) t)^n) v = a^n • v := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ',ContinuousLinearMap.mul_apply,ih,map_smul,hA,smul_smul,pow_succ]
  change exp (A (cut u N) t) v = _
  rw [exp_apply_series]
  simp_rw [hp,smul_smul]
  change (∑' n : ℕ, (((n.factorial:ℂ)⁻¹) • a^n) • v) = _
  rw [(NormedSpace.expSeries_summable' (𝕂 := ℂ) a).tsum_smul_const v,
    ← congrFun (NormedSpace.exp_eq_tsum ℂ) a,← Complex.exp_eq_exp_ℂ]

/-- Literal finite spectral expansion for the actual cutoff phase. -/
theorem phase_entry (u : Bonds) (N : ℕ) (t : ℝ) (k l : sites N) :
    entry (E (cut u N) t) k l =
      ∑ r : sites N, ((basis u N r) k:ℂ)*((basis u N r) l:ℂ)*
        Complex.exp (((t:ℂ)*Complex.I)*(eigenvalues u N r:ℂ)) := by
  unfold entry
  rw [basis_expansion u N l,map_sum,lp.coeFn_sum,Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro r _
  rw [map_smul,exp_eigenvector]
  change ((basis u N r) l:ℂ)*
    (Complex.exp (((t:ℂ)*Complex.I)*(eigenvalues u N r:ℂ))*eigenvector u N r k) = _
  rw [eigenvector,lift_inside]
  ring

end M12FiniteSpectrum
#print axioms M12FiniteSpectrum.lift_inside
#print axioms M12FiniteSpectrum.lift_outside
#print axioms M12FiniteSpectrum.entry_formula
#print axioms M12FiniteSpectrum.matrix_hermitian
#print axioms M12FiniteSpectrum.cutoff_outside
#print axioms M12FiniteSpectrum.eigenvector_action
#print axioms M12FiniteSpectrum.eigenvector_ne_zero
#print axioms M12FiniteSpectrum.eigenvalue_interval
#print axioms M12FiniteSpectrum.basis_expansion
#print axioms M12FiniteSpectrum.exp_eigenvector
#print axioms M12FiniteSpectrum.phase_entry
