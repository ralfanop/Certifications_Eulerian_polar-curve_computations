import EulerianGrothendieck.JacobiFrechet20261127

noncomputable section
open Filter Set
open scoped Topology
namespace M12DKBilateral
open M12BilateralJacobi M12JacobiFrechet

/-- Finite cutoff of the literal bilateral bonds. -/
def cut (u : Bonds) (N : ℕ) : Bonds :=
  ⟨fun m => if -(N:ℤ) ≤ m ∧ m ≤ (N:ℤ) then u.1 m else 0,
   fun m => by
     change 0 ≤ (if -(N:ℤ) ≤ m ∧ m ≤ (N:ℤ) then u.1 m else 0) ∧
       (if -(N:ℤ) ≤ m ∧ m ≤ (N:ℤ) then u.1 m else 0) ≤ 1/2
     split_ifs <;> first | exact u.2 m | norm_num⟩

theorem cut_eq (u : Bonds) (N : ℕ) (m : ℤ)
    (h₁ : -(N:ℤ) ≤ m) (h₂ : m ≤ (N:ℤ)) :
    (cut u N).1 m = u.1 m := by simp [cut,h₁,h₂]

theorem cut_norm (u : Bonds) (N : ℕ) : ‖J (cut u N)‖ ≤ 1 :=
  J_norm_le _

/-- Exact finite propagation of powers on any vector for a common local
bond window, not just convergence of matrix coefficients. -/
theorem power_local_agreement (u v : Bonds) (n : ℕ) (k : ℤ) (x : H)
    (h : ∀ m : ℤ, k-(n:ℤ) ≤ m → m ≤ k+(n:ℤ) → u.1 m = v.1 m) :
    ((J u)^n) x k = ((J v)^n) x k := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    rw [pow_succ',pow_succ']
    change J u (((J u)^n) x) k = J v (((J v)^n) x) k
    rw [J_apply,J_apply,h k (by omega) (by omega),h (k+1) (by omega) (by omega)]
    rw [ih (k-1) (fun m hm hm' => h m (by omega) (by omega)),
        ih (k+1) (fun m hm hm' => h m (by omega) (by omega))]

theorem derivative_local_agreement (u v : Bonds) (n : ℕ) (m k : ℤ) (x : H)
    (h : ∀ r : ℤ, k-(n:ℤ) ≤ r → r ≤ k+(n:ℤ) → u.1 r = v.1 r) :
    powerD (J u) n (bond m) x k = powerD (J v) n (bond m) x k := by
  induction n generalizing k with
  | zero => simp [powerD]
  | succ n ih =>
    rw [powerD_succ,powerD_succ]
    change J u ((powerD (J u) n (bond m)) x) k + bond m (((J u)^n) x) k =
      J v ((powerD (J v) n (bond m)) x) k + bond m (((J v)^n) x) k
    rw [J_apply,J_apply,bond_apply,bond_apply,h k (by omega) (by omega),h (k+1) (by omega) (by omega)]
    rw [ih (k-1) (fun r hr hr' => h r (by omega) (by omega)),
        ih (k+1) (fun r hr hr' => h r (by omega) (by omega)),
        power_local_agreement u v n (k-1) x (fun r hr hr' => h r (by omega) (by omega)),
        power_local_agreement u v n (k+1) x (fun r hr hr' => h r (by omega) (by omega))]

theorem cut_derivative_entry (u : Bonds) (N n : ℕ) (m k l : ℤ)
    (h₁ : -(N:ℤ) ≤ k-(n:ℤ)) (h₂ : k+(n:ℤ) ≤ (N:ℤ)) :
    entry (powerD (J (cut u N)) n (bond m)) k l =
      entry (powerD (J u) n (bond m)) k l := by
  exact derivative_local_agreement _ _ _ _ _ _
    (fun r hr hr' => cut_eq u N r (h₁.trans hr) (hr'.trans h₂))

/-- Closure of the finite-support PSD inequality under entrywise limits.
The remaining smooth-calculus compression convergence is explicit. -/
theorem psd_of_entrywise_limit (K : ℕ → ℤ → ℤ → ℝ) (L : ℤ → ℤ → ℝ)
    (hlim : ∀ k m, Tendsto (fun n => K n k m) atTop (𝓝 (L k m)))
    (hpos : ∀ n (W : Finset ℤ) (x : ℤ → ℝ),
      0 ≤ ∑ k ∈ W, ∑ m ∈ W, K n k m*x k*x m)
    (W : Finset ℤ) (x : ℤ → ℝ) :
    0 ≤ ∑ k ∈ W, ∑ m ∈ W, L k m*x k*x m := by
  have h : Tendsto (fun n => ∑ k ∈ W, ∑ m ∈ W, K n k m*x k*x m) atTop
      (𝓝 (∑ k ∈ W, ∑ m ∈ W, L k m*x k*x m)) := by
    apply tendsto_finset_sum
    intro k _
    apply tendsto_finset_sum
    intro m _
    exact ((hlim k m).mul tendsto_const_nhds).mul tendsto_const_nhds
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds h (fun n => hpos n W x)

theorem symmetric_of_entrywise_limit (K : ℕ → ℤ → ℤ → ℝ) (L : ℤ → ℤ → ℝ)
    (hlim : ∀ k m, Tendsto (fun n => K n k m) atTop (𝓝 (L k m)))
    (hsym : ∀ n k m, K n k m = K n m k) (k m : ℤ) : L k m = L m k := by
  apply tendsto_nhds_unique (hlim k m)
  have he : (fun n => K n k m) = (fun n => K n m k) := funext fun n => hsym n k m
  rw [he]
  exact hlim m k

end M12DKBilateral

#print axioms M12DKBilateral.cut_eq
#print axioms M12DKBilateral.cut_norm
#print axioms M12DKBilateral.power_local_agreement
#print axioms M12DKBilateral.derivative_local_agreement
#print axioms M12DKBilateral.cut_derivative_entry
#print axioms M12DKBilateral.psd_of_entrywise_limit
#print axioms M12DKBilateral.symmetric_of_entrywise_limit
