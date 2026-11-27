import EulerianGrothendieck.JacobiPropagation20261127
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Complete the near/far cone estimate and the two-distance Duhamel
bound on the literal bilateral Jacobi operator. The scalar absolute
Fourier moment is the input to the final integrated bound. -/
set_option maxHeartbeats 2000000
noncomputable section
open NormedSpace MeasureTheory Set
open scoped ENNReal InnerProductSpace
namespace M12FourierLocality
open M12BilateralJacobi M12JacobiFrechet M12JacobiFourier M12JacobiPropagation

def U (u : Bonds) (t : ℝ) : Op := exp (((t:ℂ)*Complex.I) • J u)

theorem unitary_entry_bound (u : Bonds) (t : ℝ) (k l : ℤ) :
    ‖entry (U u t) k l‖ ≤ 1 := by
  apply (entry_norm_le _ _ _).trans
  change ‖exp (((t:ℂ)*Complex.I) • J u)‖ ≤ 1
  rw [CStarRing.norm_of_mem_unitary (jacobi_unitary u t)]

def K (N : ℕ) : ℝ :=
  (1+2*Real.exp 1)^N+(Nat.factorial N:ℝ)*2^N*Real.exp (1/2)

theorem propagation_constant_nonneg (N : ℕ) : 0 ≤ K N := by
  unfold K
  positivity

theorem global_propagation (u : Bonds) (t : ℝ) (k l : ℤ) (N : ℕ) :
    ‖entry (U u t) k l‖ ≤ K N*(1+|t|)^N/(1+|(k:ℝ)-l|)^N := by
  let d : ℕ := (k-l).natAbs
  have hd : k ≤ l-(d:ℤ) ∨ l+(d:ℤ) ≤ k := by
    dsimp [d]
    omega
  have hr : (d:ℝ) = |(k:ℝ)-l| := by
    have he : (d:ℤ) = |k-l| := by simp [d,Int.natCast_natAbs]
    exact_mod_cast he
  rw [← hr]
  have hpos : 0 < (1+(d:ℝ))^N := by positivity
  by_cases hfar : 2*Real.exp 1*|t| ≤ (d:ℝ)
  · apply (far_cone_polynomial u t k l d N hd hfar).trans
    apply div_le_div_of_nonneg_right _ hpos.le
    have hK : (Nat.factorial N:ℝ)*2^N*Real.exp (1/2) ≤ K N := by
      unfold K
      have hh : 0 ≤ (1+2*Real.exp 1)^N := by positivity
      linarith
    have ht : 1 ≤ (1+|t|)^N := one_le_pow₀ (by linarith [abs_nonneg t])
    exact hK.trans (by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left ht (propagation_constant_nonneg N))
  · apply (unitary_entry_bound u t k l).trans
    apply (le_div_iff₀ hpos).2
    rw [one_mul]
    have h : 1+(d:ℝ) ≤ (1+2*Real.exp 1)*(1+|t|) := by
      nlinarith [le_of_not_ge hfar,Real.exp_pos 1,abs_nonneg t]
    calc
      _ ≤ ((1+2*Real.exp 1)*(1+|t|))^N :=
        pow_le_pow_left₀ (by positivity) h N
      _ = (1+2*Real.exp 1)^N*(1+|t|)^N := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right (by
        unfold K
        have hh : 0 ≤ (Nat.factorial N:ℝ)*2^N*Real.exp (1/2) := by positivity
        linarith) (by positivity)

theorem bond_rank_two (m : ℤ) (x : H) :
    bond m x = lp.single 2 m (x (m-1)) + lp.single 2 (m-1) (x m) := by
  ext k
  rw [bond_apply]
  by_cases h : k=m
  · subst k
    simp [lp.single_apply,show m+1≠m by omega,show m≠m-1 by omega,show m-1≠m by omega]
  · by_cases h' : k=m-1
    · subst k
      simp [lp.single_apply,show m-1≠m by omega,show m≠m-1 by omega]
    · have hh : k+1≠m := by omega
      simp [lp.single_apply,h,h',hh,Ne.symm h,Ne.symm h']

theorem bond_product_entry (A C : Op) (m k l : ℤ) :
    entry (A*bond m*C) k l =
      entry A k m * entry C (m-1) l + entry A k (m-1) * entry C m l := by
  let x : H := lp.single 2 l 1
  change A (bond m (C x)) k = _
  rw [bond_rank_two,map_add]
  have hs (j : ℤ) (z : ℂ) : lp.single 2 j z = z • (lp.single 2 j 1 : H) := by
    ext i
    by_cases h : i=j <;> simp [lp.single_apply,h,Ne.symm h]
  rw [hs m,hs (m-1),map_smul,map_smul]
  change (C x (m-1))*entry A k m+(C x m)*entry A k (m-1) = _
  change entry C (m-1) l*entry A k m+entry C m l*entry A k (m-1) = _
  ring

/-- A product with both factors bounded by one inherits decay from the
larger of the two propagation distances. -/
theorem product_decay (a b d L : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hd : 0 ≤ d) (hL : 0 ≤ L) (htriangle : d ≤ 1+a+b)
    (x y : ℂ) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (N : ℕ)
    (hxa : ‖x‖ ≤ L/(1+a)^N) (hyb : ‖y‖ ≤ L/(1+b)^N) :
    ‖x*y‖ ≤ (2:ℝ)^N*L/(1+d)^N := by
  rw [norm_mul]
  have hp : 0 < (1+d)^N := by positivity
  apply (le_div_iff₀ hp).2
  rcases le_total a b with hab|hba
  · have h₁ : ‖x‖*‖y‖ ≤ L/(1+b)^N := by
      calc
        _ ≤ 1*‖y‖ := mul_le_mul_of_nonneg_right hx (norm_nonneg _)
        _ ≤ _ := by simpa only [one_mul] using hyb
    have h₂ : (1+d)^N ≤ 2^N*(1+b)^N := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith) N
    calc
      _ ≤ (L/(1+b)^N)*(2^N*(1+b)^N) :=
        mul_le_mul h₁ h₂ hp.le (by positivity)
      _ = _ := by field_simp; ring
  · have h₁ : ‖x‖*‖y‖ ≤ L/(1+a)^N := by
      calc
        _ ≤ ‖x‖*1 := mul_le_mul_of_nonneg_left hy (norm_nonneg _)
        _ ≤ _ := by simpa only [mul_one] using hxa
    have h₂ : (1+d)^N ≤ 2^N*(1+a)^N := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith) N
    calc
      _ ≤ (L/(1+a)^N)*(2^N*(1+a)^N) :=
        mul_le_mul h₁ h₂ hp.le (by positivity)
      _ = _ := by field_simp; ring

theorem bond_density_bound (u : Bonds) (t s : ℝ) (hs : s ∈ Icc (0:ℝ) 1)
    (m k l : ℤ) (N : ℕ) :
    ‖entry (U u ((1-s)*t)*bond m*U u (s*t)) k l‖ ≤
      2*2^N*K N*(1+|t|)^N/(1+|(k:ℝ)-m|+|(m:ℝ)-l|)^N := by
  let A := U u ((1-s)*t)
  let C := U u (s*t)
  let L := K N*(1+|t|)^N
  let d := |(k:ℝ)-m|+|(m:ℝ)-l|
  have hL : 0 ≤ L := mul_nonneg (propagation_constant_nonneg N) (by positivity)
  have hd : 0 ≤ d := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have ht₁ : |(1-s)*t| ≤ |t| := by
    rw [abs_mul,abs_of_nonneg (sub_nonneg.mpr hs.2)]
    nlinarith [hs.1,abs_nonneg t]
  have ht₂ : |s*t| ≤ |t| := by
    rw [abs_mul,abs_of_nonneg hs.1]
    nlinarith [hs.2,abs_nonneg t]
  have hA (i j : ℤ) : ‖entry A i j‖ ≤ L/(1+|(i:ℝ)-j|)^N := by
    apply (global_propagation u _ i j N).trans
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) N) (propagation_constant_nonneg N)
  have hC (i j : ℤ) : ‖entry C i j‖ ≤ L/(1+|(i:ℝ)-j|)^N := by
    apply (global_propagation u _ i j N).trans
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) N) (propagation_constant_nonneg N)
  have htri₁ : d ≤ 1+|(k:ℝ)-m|+|((m-1:ℤ):ℝ)-l| := by
    have h := abs_add_le (((m-1:ℤ):ℝ)-l) (1:ℝ)
    have he : (((m-1:ℤ):ℝ)-l)+1 = (m:ℝ)-l := by push_cast; ring
    rw [he,abs_one] at h
    dsimp [d]
    linarith
  have htri₂ : d ≤ 1+|(k:ℝ)-(m-1:ℤ)|+|(m:ℝ)-l| := by
    have h := abs_add_le ((k:ℝ)-(m-1:ℤ)) (-1:ℝ)
    have he : ((k:ℝ)-(m-1:ℤ))+(-1) = (k:ℝ)-m := by push_cast; ring
    rw [he,abs_neg,abs_one] at h
    dsimp [d]
    linarith
  have h₁ := product_decay _ _ d L (abs_nonneg _) (abs_nonneg _) hd hL htri₁
    (entry A k m) (entry C (m-1) l) (unitary_entry_bound u _ _ _)
    (unitary_entry_bound u _ _ _) N (hA k m) (hC (m-1) l)
  have h₂ := product_decay _ _ d L (abs_nonneg _) (abs_nonneg _) hd hL htri₂
    (entry A k (m-1)) (entry C m l) (unitary_entry_bound u _ _ _)
    (unitary_entry_bound u _ _ _) N (hA k (m-1)) (hC m l)
  change ‖entry (A*bond m*C) k l‖ ≤ _
  rw [bond_product_entry]
  calc
    _ ≤ ‖entry A k m*entry C (m-1) l‖+‖entry A k (m-1)*entry C m l‖ := norm_add_le _ _
    _ ≤ 2^N*L/(1+d)^N+2^N*L/(1+d)^N := add_le_add h₁ h₂
    _ = _ := by dsimp [L,d]; rw [show 1+|(k:ℝ)-m|+|(m:ℝ)-l|=1+(|(k:ℝ)-m|+|(m:ℝ)-l|) by ring]; ring

def bondDuhamel (u : Bonds) (t : ℝ) (m : ℤ) : Op :=
  ∫ s in (0:ℝ)..1, U u ((1-s)*t)*bond m*U u (s*t)

theorem duhamel_entry_bound (u : Bonds) (t : ℝ) (m k l : ℤ) (N : ℕ) :
    ‖entry (bondDuhamel u t m) k l‖ ≤
      2*2^N*K N*(1+|t|)^N/(1+|(k:ℝ)-m|+|(m:ℝ)-l|)^N := by
  have hc : Continuous (U u) := by
    unfold U
    apply (show Continuous (exp : Op → Op) from M12ExpFrechet.exp_cont).comp
    exact (Complex.continuous_ofReal.mul (continuous_const : Continuous (fun _ : ℝ => Complex.I))).smul continuous_const
  have hi : IntervalIntegrable (fun s : ℝ => U u ((1-s)*t)*bond m*U u (s*t)) volume 0 1 :=
    (((hc.comp ((continuous_const.sub continuous_id).mul continuous_const)).mul continuous_const).mul
      (hc.comp (continuous_id.mul continuous_const))).intervalIntegrable 0 1
  unfold bondDuhamel
  rw [← entryMap_apply,← (entryMap k l).intervalIntegral_comp_comm hi]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := 1) (f := fun s => entryMap k l (U u ((1-s)*t)*bond m*U u (s*t)))
    (C := 2*2^N*K N*(1+|t|)^N/(1+|(k:ℝ)-m|+|(m:ℝ)-l|)^N)
    (fun s hs => by
      rw [entryMap_apply]
      apply bond_density_bound u t s _ m k l N
      rw [uIoc_of_le zero_le_one] at hs
      exact ⟨hs.1.le,hs.2⟩)
  simpa using h

/-- Integrated bound for the actual Duhamel bond entry, assuming only
the scalar absolute Fourier moment and measurability of the entry. -/
theorem fourier_bond_decay (u : Bonds) (w : ℝ → ℂ) (m k l : ℤ) (N : ℕ)
    (hm : Integrable (fun t : ℝ => ‖w t‖*|t|*(1+|t|)^N))
    (hi : Integrable (fun t : ℝ => w t*((t:ℂ)*Complex.I)*entry (bondDuhamel u t m) k l)) :
    ‖∫ t : ℝ, w t*((t:ℂ)*Complex.I)*entry (bondDuhamel u t m) k l‖ ≤
      (2*2^N*K N*(∫ t : ℝ, ‖w t‖*|t|*(1+|t|)^N))/(1+|(k:ℝ)-m|+|(m:ℝ)-l|)^N := by
  let C := 2*2^N*K N/(1+|(k:ℝ)-m|+|(m:ℝ)-l|)^N
  have hC : 0 ≤ C := by dsimp [C]; positivity
  calc
    _ ≤ ∫ t : ℝ, ‖w t*((t:ℂ)*Complex.I)*entry (bondDuhamel u t m) k l‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, C*(‖w t‖*|t|*(1+|t|)^N) := by
      apply integral_mono hi.norm (hm.const_mul C)
      intro t
      rw [norm_mul,norm_mul,norm_mul,Complex.norm_real,Complex.norm_I,mul_one,Real.norm_eq_abs]
      have h := mul_le_mul_of_nonneg_left (duhamel_entry_bound u t m k l N)
        (mul_nonneg (norm_nonneg _) (abs_nonneg _))
      convert h using 1 <;> dsimp [C] <;> ring
    _ = _ := by rw [integral_const_mul]; dsimp [C]; ring

end M12FourierLocality
#print axioms M12FourierLocality.unitary_entry_bound
#print axioms M12FourierLocality.propagation_constant_nonneg
#print axioms M12FourierLocality.global_propagation
#print axioms M12FourierLocality.bond_rank_two
#print axioms M12FourierLocality.bond_product_entry
#print axioms M12FourierLocality.product_decay
#print axioms M12FourierLocality.bond_density_bound
#print axioms M12FourierLocality.duhamel_entry_bound
#print axioms M12FourierLocality.fourier_bond_decay
