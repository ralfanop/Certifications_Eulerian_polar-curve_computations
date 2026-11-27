import EulerianGrothendieck.KreinBilateralJacobi20261127

/-! M12 Lemma 5.12, equations (178)-(179).
Actual complex Frechet derivative of the polynomial functional calculus
on the bounded operators of the bilateral Hilbert space. Exact bond
perturbation, derivative recurrence, norm estimate and finite propagation.
The extension to arbitrary compactly supported smooth functions (Fourier
inversion, Duhamel, and positivity of divided differences) is not claimed
by this module. -/
noncomputable section
open scoped RightActions ENNReal
namespace M12JacobiFrechet
open M12BilateralJacobi

/-- Derivative of the noncommutative power map, as a continuous linear
map on the actual Banach algebra of bounded operators. -/
def powerD (A : Op) : ℕ → (Op →L[ℂ] Op)
  | 0 => 0
  | n+1 => A • powerD A n + (ContinuousLinearMap.id ℂ Op) <• A^n

theorem powerD_zero (A X : Op) : powerD A 0 X = 0 := rfl

theorem powerD_succ (A X : Op) (n : ℕ) :
    powerD A (n+1) X = A * powerD A n X + X * A^n := rfl

theorem power_hasFDerivAt (A : Op) (n : ℕ) :
    HasFDerivAt (fun T : Op => T^n) (powerD A n) A := by
  induction n with
  | zero =>
      simpa only [pow_zero,powerD] using (hasFDerivAt_const (1:Op) A)
  | succ n ih =>
      have h := (hasFDerivAt_id (𝕜 := ℂ) A).mul' ih
      rw [show (fun T : Op => T^(n+1)) = id * (fun T : Op => T^n) by
        funext T; exact pow_succ' T n]
      exact h

theorem power_fderiv (A : Op) (n : ℕ) :
    fderiv ℂ (fun T : Op => T^n) A = powerD A n :=
  (power_hasFDerivAt A n).fderiv

theorem powerD_norm (A X : Op) (hA : ‖A‖ ≤ 1) (n : ℕ) :
    ‖powerD A n X‖ ≤ (n:ℝ)*‖X‖ := by
  induction n with
  | zero => simp [powerD_zero]
  | succ n ih =>
      have hp : ‖A^n‖ ≤ 1 := by
        by_cases hn : n = 0
        · subst n
          rw [pow_zero]
          exact ContinuousLinearMap.norm_id_le
        · exact (norm_pow_le' A (Nat.pos_of_ne_zero hn)).trans (pow_le_one₀ (norm_nonneg A) hA)
      rw [powerD_succ]
      calc
        _ ≤ ‖A*powerD A n X‖ + ‖X*A^n‖ := norm_add_le _ _
        _ ≤ ‖A‖*‖powerD A n X‖ + ‖X‖*‖A^n‖ :=
          add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
        _ ≤ 1*((n:ℝ)*‖X‖)+‖X‖*1 :=
          add_le_add (mul_le_mul hA ih (norm_nonneg _) (by norm_num))
            (mul_le_mul_of_nonneg_left hp (norm_nonneg X))
        _ = ((n+1:ℕ):ℝ)*‖X‖ := by push_cast; ring

theorem powerD_opNorm (A : Op) (hA : ‖A‖ ≤ 1) (n : ℕ) :
    ‖powerD A n‖ ≤ (n:ℝ) :=
  ContinuousLinearMap.opNorm_le_bound _ (Nat.cast_nonneg n)
    (fun X => powerD_norm A X hA n)

/-- A single actual bond, with off-diagonal entries equal to one. -/
def halfBond (m : ℤ) : Bonds :=
  ⟨fun k => if k=m then 1/2 else 0, fun k => by by_cases hk : k = m <;> simp [hk]⟩

def bond (m : ℤ) : Op := (2:ℂ) • J (halfBond m)

theorem bond_apply (m k : ℤ) (x : H) :
    bond m x k = (if k=m then x (k-1) else 0) +
      (if k+1=m then x (k+1) else 0) := by
  change (2:ℂ) * (J (halfBond m) x k) = _
  rw [J_apply]
  unfold halfBond
  by_cases h : k=m <;> by_cases h' : k+1=m <;> simp [h,h'] <;> ring

theorem bond_outside (m k : ℤ) (x : H) (hk : k≠m) (hk' : k+1≠m) :
    bond m x k = 0 := by simp [bond_apply,hk,hk']

theorem bond_norm_le (m : ℤ) : ‖bond m‖ ≤ 2 := by
  unfold bond
  rw [norm_smul]
  have hn : ‖(2:ℂ)‖ = 2 := by norm_num
  rw [hn]
  nlinarith [J_norm_le (halfBond m)]

theorem derivative_entry_bound (u : Bonds) (n : ℕ) (m k l : ℤ) :
    ‖entry (powerD (J u) n (bond m)) k l‖ ≤ 2*(n:ℝ) := by
  let x : H := lp.single 2 l 1
  have hx : ‖x‖ = 1 := by
    simp [x,lp.norm_single]
  let T := powerD (J u) n (bond m)
  calc
    _ ≤ ‖T x‖ := lp.norm_apply_le_norm (by norm_num : (2:ℝ≥0∞) ≠ 0) _ _
    _ ≤ ‖T‖*‖x‖ := T.le_opNorm x
    _ = ‖T‖ := by rw [hx,mul_one]
    _ ≤ (n:ℝ)*‖bond m‖ := powerD_norm _ _ (J_norm_le u) _
    _ ≤ 2*(n:ℝ) := by
      rw [mul_comm 2]
      exact mul_le_mul_of_nonneg_left (bond_norm_le m) (Nat.cast_nonneg n)

/-- The differentiated power cannot propagate further from the inserted
bond than the degree of the polynomial. -/
theorem derivative_entry_outside (u : Bonds) (n : ℕ) (m k l : ℤ)
    (hk : k < m-(n:ℤ) ∨ m+(n:ℤ)<k) :
    entry (powerD (J u) n (bond m)) k l = 0 := by
  induction n generalizing k with
  | zero => simp [powerD,entry]
  | succ n ih =>
      have hm : k - 1 < m - (n:ℤ) ∨ m + (n:ℤ) < k - 1 := by omega
      have hp : k + 1 < m - (n:ℤ) ∨ m + (n:ℤ) < k + 1 := by omega
      have hk0 : k≠m := by omega
      have hk1 : k+1≠m := by omega
      have hminus := ih (k-1) hm
      have hplus := ih (k+1) hp
      unfold entry at hminus hplus ⊢
      rw [powerD_succ]
      change J u ((powerD (J u) n (bond m)) (lp.single 2 l 1)) k +
        bond m (((J u)^n) (lp.single 2 l 1)) k = 0
      rw [J_apply,hminus,hplus,bond_outside m k _ hk0 hk1]
      ring

/-- Finite polynomial calculus, without a commutativity assumption
on the perturbation. -/
def polynomialOp (N : ℕ) (a : ℕ → ℂ) (A : Op) : Op :=
  ∑ n ∈ Finset.range N, a n • A^n

def polynomialD (N : ℕ) (a : ℕ → ℂ) (A : Op) : Op →L[ℂ] Op :=
  ∑ n ∈ Finset.range N, a n • powerD A n

theorem polynomial_hasFDerivAt (N : ℕ) (a : ℕ → ℂ) (A : Op) :
    HasFDerivAt (polynomialOp N a) (polynomialD N a A) A := by
  induction N with
  | zero =>
      have he : polynomialOp 0 a = (fun _ : Op => (0:Op)) := by funext T; simp [polynomialOp]
      rw [he,show polynomialD 0 a A = 0 by simp [polynomialD]]
      exact hasFDerivAt_const (0:Op) A
  | succ N ih =>
      have h := ih.add ((power_hasFDerivAt A N).const_smul (a N))
      rw [show polynomialOp (N+1) a = polynomialOp N a + a N • (fun T : Op => T^N) by
        funext T; simp only [polynomialOp,Finset.sum_range_succ,Pi.add_apply,Pi.smul_apply]]
      simpa only [polynomialD,Finset.sum_range_succ] using h

theorem polynomialD_locality (N : ℕ) (a : ℕ → ℂ) (u : Bonds) (m k l : ℤ)
    (hk : k < m-(N:ℤ) ∨ m+(N:ℤ)<k) :
    entry (polynomialD N a (J u) (bond m)) k l = 0 := by
  induction N with
  | zero => simp [polynomialD,entry]
  | succ N ih =>
      have hh : k < m - (N:ℤ) ∨ m + (N:ℤ) < k := by omega
      have h1 := ih hh
      have h2 := derivative_entry_outside u N m k l hh
      have he : polynomialD (N+1) a (J u) = polynomialD N a (J u) + a N • powerD (J u) N := by
        simp only [polynomialD,Finset.sum_range_succ]
      rw [he]
      change entry (polynomialD N a (J u) (bond m)) k l + a N * entry (powerD (J u) N (bond m)) k l = 0
      rw [h1,h2,mul_zero,add_zero]

end M12JacobiFrechet

#print axioms M12JacobiFrechet.powerD_succ
#print axioms M12JacobiFrechet.power_hasFDerivAt
#print axioms M12JacobiFrechet.power_fderiv
#print axioms M12JacobiFrechet.powerD_norm
#print axioms M12JacobiFrechet.powerD_opNorm
#print axioms M12JacobiFrechet.bond_apply
#print axioms M12JacobiFrechet.bond_outside
#print axioms M12JacobiFrechet.bond_norm_le
#print axioms M12JacobiFrechet.derivative_entry_bound
#print axioms M12JacobiFrechet.derivative_entry_outside
#print axioms M12JacobiFrechet.polynomial_hasFDerivAt
#print axioms M12JacobiFrechet.polynomialD_locality
