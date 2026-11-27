import Manuscript16.V166L2SpectralInverse

/-! Concrete bilateral Jacobi operator, shared by M12 Lemma 5.12 and
Theorem 5.18. No finite dimensional replacement of the Hilbert space.
Finite propagation is a prerequisite for the functional-calculus estimates,
not a proof of the entire asymptotic theorem. -/

noncomputable section
open scoped ENNReal InnerProductSpace
namespace M12BilateralJacobi
open Manuscript16.V166L2SpectralInverse

abbrev H := L2 ℤ
abbrev Op := H →L[ℂ] H

def translation (d : ℤ) : ℤ ≃ ℤ where
  toFun k := k + d
  invFun k := k - d
  left_inv k := by change k+d-d=k; omega
  right_inv k := by change k-d+d=k; omega

def reindexVector (e : ℤ ≃ ℤ) (x : H) : H :=
  ⟨fun k => x (e k), by
    apply memℓp_gen
    have h := (lp.memℓp x).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    exact (e.summable_iff).2 h⟩

theorem reindex_norm (e : ℤ ≃ ℤ) (x : H) :
    ‖reindexVector e x‖ = ‖x‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal),
      lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  congr 1
  exact e.tsum_eq (fun k => ‖x k‖ ^ (2 : ℝ≥0∞).toReal)

def shift (d : ℤ) : Op :=
  (show H →ₗ[ℂ] H from
    { toFun := reindexVector (translation d)
      map_add' x y := by apply lp.ext; funext k; rfl
      map_smul' c x := by apply lp.ext; funext k; rfl }).mkContinuous 1
    (fun x => by
      change ‖reindexVector (translation d) x‖ ≤ 1 * ‖x‖
      rw [reindex_norm, one_mul])

@[simp] theorem shift_apply (d : ℤ) (x : H) (k : ℤ) :
    shift d x k = x (k + d) := rfl

theorem shift_norm_le (d : ℤ) : ‖shift d‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  change ‖reindexVector (translation d) x‖ ≤ 1 * ‖x‖
  rw [reindex_norm, one_mul]

def Bonds := {u : ℤ → ℝ // ∀ k, 0 ≤ u k ∧ u k ≤ 1/2}

def weight (u : Bonds) : Op :=
  diagonal (fun k => (u.1 k : ℂ)) (1/2) (by norm_num)
    (fun k => by rw [Complex.norm_real, Real.norm_of_nonneg (u.2 k).1]; exact (u.2 k).2)

@[simp] theorem weight_apply (u : Bonds) (x : H) (k : ℤ) :
    weight u x k = (u.1 k : ℂ) * x k := rfl

theorem weight_norm_le (u : Bonds) : ‖weight u‖ ≤ 1/2 :=
  diagonal_norm_le _ _ _ _

def J (u : Bonds) : Op := weight u * shift (-1) + shift 1 * weight u

theorem J_apply (u : Bonds) (x : H) (k : ℤ) :
    J u x k = (u.1 k : ℂ) * x (k-1) + (u.1 (k+1) : ℂ) * x (k+1) := by
  change weight u (shift (-1) x) k + shift 1 (weight u x) k = _
  simp [sub_eq_add_neg]

theorem J_norm_le (u : Bonds) : ‖J u‖ ≤ 1 := by
  unfold J
  calc
    _ ≤ ‖weight u * shift (-1)‖ + ‖shift 1 * weight u‖ := norm_add_le _ _
    _ ≤ ‖weight u‖ * ‖shift (-1)‖ + ‖shift 1‖ * ‖weight u‖ :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ (1/2) * 1 + 1 * (1/2) := add_le_add
      (mul_le_mul (weight_norm_le u) (shift_norm_le (-1)) (norm_nonneg _) (by norm_num))
      (mul_le_mul (shift_norm_le 1) (weight_norm_le u) (norm_nonneg _) (by norm_num))
    _ = 1 := by norm_num

theorem forward_backward (u : Bonds) (x y : H) :
    ⟪weight u (shift (-1) x), y⟫_ℂ = ⟪x, shift 1 (weight u y)⟫_ℂ := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  calc
    _ = ∑' k : ℤ, ⟪weight u (shift (-1) x) (translation 1 k), y (translation 1 k)⟫_ℂ :=
      ((translation 1).tsum_eq _).symm
    _ = _ := by
      congr 1
      funext k
      have hk : k + 1 + (-1 : ℤ) = k := by omega
      simp only [translation, Equiv.coe_fn_mk, weight_apply, shift_apply, hk]
      change ⟪(u.1 (k+1) : ℂ) • x k, y (k+1)⟫_ℂ =
        ⟪x k, (u.1 (k+1) : ℂ) • y (k+1)⟫_ℂ
      rw [inner_smul_left, inner_smul_right]
      simp

theorem J_selfAdjoint (u : Bonds) : IsSelfAdjoint (J u) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  change ⟪weight u (shift (-1) x) + shift 1 (weight u x), y⟫_ℂ =
    ⟪x, weight u (shift (-1) y) + shift 1 (weight u y)⟫_ℂ
  rw [inner_add_left, inner_add_right, forward_backward]
  have h := congrArg (starRingEnd ℂ) (forward_backward u y x)
  rw [inner_conj_symm, inner_conj_symm] at h
  rw [← h, add_comm]

def paritySign (k : ℤ) : ℂ := if k % 2 = 0 then 1 else -1

theorem paritySign_step (k : ℤ) : paritySign (k+1) = -paritySign k := by
  by_cases h : k % 2 = 0
  · have h' : (k+1) % 2 ≠ 0 := by omega
    simp [paritySign, h, h']
  · have h' : (k+1) % 2 = 0 := by omega
    simp [paritySign, h, h']

theorem paritySign_prev (k : ℤ) : paritySign (k-1) = -paritySign k := by
  have h := paritySign_step (k-1)
  rw [show k-1+1=k by omega] at h
  rw [h, neg_neg]

def S0 : Op := diagonal paritySign 1 (by norm_num) (fun k => by
  unfold paritySign
  split <;> simp)

@[simp] theorem S0_apply (x : H) (k : ℤ) :
    S0 x k = paritySign k * x k := rfl

theorem S0_square : S0 * S0 = 1 := by
  ext x k
  change paritySign k * (paritySign k * x k) = x k
  unfold paritySign
  split <;> simp

theorem S0_selfAdjoint : IsSelfAdjoint S0 := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  congr 1
  funext k
  change ⟪paritySign k • x k, y k⟫_ℂ = ⟪x k, paritySign k • y k⟫_ℂ
  rw [inner_smul_left, inner_smul_right]
  unfold paritySign
  split <;> simp

theorem parity_anticomm (u : Bonds) : S0 * J u = -(J u * S0) := by
  ext x k
  change S0 (J u x) k = -(J u (S0 x) k)
  rw [S0_apply, J_apply, J_apply, S0_apply, S0_apply, paritySign_prev, paritySign_step]
  ring

def entry (T : Op) (k m : ℤ) : ℂ := T (lp.single 2 m 1) k

theorem power_entry_outside (u : Bonds) (n : ℕ) (k m : ℤ)
    (h : k < m-(n:ℤ) ∨ m+(n:ℤ) < k) : entry ((J u)^n) k m = 0 := by
  induction n generalizing k with
  | zero =>
      have hk : k ≠ m := by omega
      simp [entry, hk, Ne.symm hk]
  | succ n ih =>
      have hm : k-1 < m-(n:ℤ) ∨ m+(n:ℤ) < k-1 := by omega
      have hp : k+1 < m-(n:ℤ) ∨ m+(n:ℤ) < k+1 := by omega
      have hm' := ih (k-1) hm
      have hp' := ih (k+1) hp
      unfold entry at hm' hp' ⊢
      rw [pow_succ']
      change J u (((J u)^n) (lp.single 2 m 1)) k = 0
      rw [J_apply, hm', hp']
      ring

end M12BilateralJacobi

#print axioms M12BilateralJacobi.reindex_norm
#print axioms M12BilateralJacobi.shift_norm_le
#print axioms M12BilateralJacobi.weight_norm_le
#print axioms M12BilateralJacobi.J_apply
#print axioms M12BilateralJacobi.J_norm_le
#print axioms M12BilateralJacobi.forward_backward
#print axioms M12BilateralJacobi.J_selfAdjoint
#print axioms M12BilateralJacobi.S0_square
#print axioms M12BilateralJacobi.S0_selfAdjoint
#print axioms M12BilateralJacobi.parity_anticomm
#print axioms M12BilateralJacobi.power_entry_outside
