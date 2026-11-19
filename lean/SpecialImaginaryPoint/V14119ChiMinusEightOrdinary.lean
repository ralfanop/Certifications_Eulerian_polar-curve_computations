import SpecialImaginaryPoint.V14119DiscriminantMinusEight

/-! M14.119: exact character modulo 8 and convergence of the ordinary
ordered Dirichlet partial sums, not unordered HasSum of a conditionally
convergent family. The analytic continuation LFunction at s=1 is separate. -/
open Filter Finset
open scoped BigOperators Topology
noncomputable section
namespace Manuscript14.DiscriminantMinusEight

def chiInt (a : ZMod 8) : ℤ :=
  if a = 1 ∨ a = 3 then 1 else if a = 5 ∨ a = 7 then -1 else 0

theorem chiInt_mul (a b : ZMod 8) : chiInt (a*b) = chiInt a * chiInt b := by
  fin_cases a <;> fin_cases b <;> decide

theorem chiInt_nonzero_sq (a : ZMod 8) : chiInt a ≠ 0 → a*a = 1 := by
  fin_cases a <;> decide

def chi8 : DirichletCharacter ℂ 8 where
  toMonoidHom := {
    toFun := fun a => (chiInt a : ℂ)
    map_one' := by
      have h : chiInt (1:ZMod 8) = 1 := by decide
      rw [h]; norm_num
    map_mul' := by
      intro a b
      rw [chiInt_mul,Int.cast_mul] }
  map_nonunit' := by
    intro a ha
    have h : chiInt a = 0 := by
      by_contra hn
      have hs := chiInt_nonzero_sq a hn
      exact ha ⟨⟨a,a,hs,hs⟩,rfl⟩
    change (chiInt a : ℂ) = 0
    simp [h]

theorem chi8_apply (a : ZMod 8) : chi8 a = (chiInt a : ℂ) := rfl

def realCharacter (n : ℕ) : ℝ := (chiInt (n:ZMod 8) : ℝ)

def ordinaryTerm (n : ℕ) : ℝ := realCharacter n / (n:ℝ)

def ordinaryPartial (N : ℕ) : ℝ := ∑ n ∈ Finset.range N, ordinaryTerm n

theorem realCharacter_eq_re (n : ℕ) : realCharacter n = (chi8 (n:ZMod 8)).re := by
  simp [realCharacter,chi8_apply]

theorem realCharacter_period (n r : ℕ) :
    realCharacter (8*n+r) = realCharacter r := by
  unfold realCharacter
  have h : (8:ZMod 8) = 0 := by decide
  simp [Nat.cast_add,Nat.cast_mul,h]

theorem realCharacter_abs_le (n : ℕ) : |realCharacter n| ≤ 1 := by
  unfold realCharacter
  unfold chiInt
  split_ifs <;> norm_num

theorem realCharacter_zero : realCharacter 0 = 0 := by
  have h : chiInt (0:ZMod 8) = 0 := by decide
  simp [realCharacter,h]

theorem ordinary_block (n : ℕ) :
    (∑ r ∈ Finset.range 8, ordinaryTerm (8*n+r)) = block n := by
  have h0 : chiInt (0:ZMod 8) = 0 := by decide
  have h1 : chiInt (1:ZMod 8) = 1 := by decide
  have h2 : chiInt (2:ZMod 8) = 0 := by decide
  have h3 : chiInt (3:ZMod 8) = 1 := by decide
  have h4 : chiInt (4:ZMod 8) = 0 := by decide
  have h5 : chiInt (5:ZMod 8) = -1 := by decide
  have h6 : chiInt (6:ZMod 8) = 0 := by decide
  have h7 : chiInt (7:ZMod 8) = -1 := by decide
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,ordinaryTerm,realCharacter_period]
  norm_num [realCharacter,h0,h1,h2,h3,h4,h5,h6,h7,block,Nat.cast_add,Nat.cast_mul]
  <;> ring

theorem ordinary_aligned (N : ℕ) :
    ordinaryPartial (8*N) = ∑ n ∈ Finset.range N, block n := by
  induction N with
  | zero => simp [ordinaryPartial]
  | succ N ih =>
    rw [show 8*(N+1)=8*N+8 by omega]
    unfold ordinaryPartial at *
    rw [Finset.sum_range_add,ih,ordinary_block,Finset.sum_range_succ]

theorem ordinary_term_bound (n r : ℕ) :
    |ordinaryTerm (8*n+r)| ≤ 1/(8*(n:ℝ)+1) := by
  by_cases hr : r=0
  · subst r
    unfold ordinaryTerm
    rw [realCharacter_period,realCharacter_zero,zero_div,abs_zero]
    positivity
  · have hr' : 1 ≤ r := by omega
    have hcast : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr'
    have hn : 0 ≤ (n:ℝ) := by positivity
    have hd : 0 < ((8*n+r:ℕ):ℝ) := by push_cast; linarith
    unfold ordinaryTerm
    rw [abs_div,abs_of_pos hd]
    apply (div_le_div_iff₀ hd (by positivity : 0 < 8*(n:ℝ)+1)).2
    have hmul := mul_le_mul_of_nonneg_right (realCharacter_abs_le (8*n+r)) (by positivity : 0 ≤ 8*(n:ℝ)+1)
    push_cast
    linarith

theorem ordinary_tail (n r : ℕ) (hr : r < 8) :
    |ordinaryPartial (8*n+r) - ordinaryPartial (8*n)| ≤ 8/(8*(n:ℝ)+1) := by
  unfold ordinaryPartial
  rw [Finset.sum_range_add,add_sub_cancel_left]
  calc
    _ ≤ ∑ j ∈ Finset.range r, |ordinaryTerm (8*n+j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range r, 1/(8*(n:ℝ)+1) :=
      Finset.sum_le_sum fun j _ => ordinary_term_bound n j
    _ = (r:ℝ)/(8*(n:ℝ)+1) := by simp [div_eq_mul_inv]
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast hr.le

theorem ordinary_error (N : ℕ) :
    |ordinaryPartial N - Real.pi/Real.sqrt 8| ≤
      10/(8*((N/8:ℕ):ℝ)+1) := by
  let q := N/8
  let r := N%8
  have hN : 8*q+r=N := Nat.div_add_mod N 8
  have hr : r<8 := Nat.mod_lt N (by decide)
  have ht := ordinary_tail q r hr
  rw [hN,ordinary_aligned] at ht
  have hb := partial_sum_error q
  have hab : |(∑ n ∈ Finset.range q, block n)-Real.pi/Real.sqrt 8| ≤ 2/(8*(q:ℝ)+1) := by
    rw [abs_sub_comm,abs_of_nonneg hb.1]
    exact hb.2
  calc
    _ = |(ordinaryPartial N-(∑ n ∈ Finset.range q, block n))+
      ((∑ n ∈ Finset.range q, block n)-Real.pi/Real.sqrt 8)| := by congr 1; ring
    _ ≤ |ordinaryPartial N-(∑ n ∈ Finset.range q, block n)|+
      |(∑ n ∈ Finset.range q, block n)-Real.pi/Real.sqrt 8| := abs_add_le _ _
    _ ≤ 8/(8*(q:ℝ)+1)+2/(8*(q:ℝ)+1) := add_le_add ht hab
    _ = _ := by dsimp [q]; ring

theorem ordinary_tendsto : Tendsto ordinaryPartial atTop (𝓝 (Real.pi/Real.sqrt 8)) := by
  have hq : Tendsto (fun N : ℕ => ((N/8:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (Nat.tendsto_div_const_atTop (by decide : (8:ℕ) ≠ 0))
  have hd : Tendsto (fun N : ℕ => 8*((N/8:ℕ):ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (hq.const_mul_atTop (by norm_num))
  have ht : Tendsto (fun N : ℕ => 10/(8*((N/8:ℕ):ℝ)+1)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds.mul hd.inv_tendsto_atTop :
        Tendsto (fun N : ℕ => 10*(8*((N/8:ℕ):ℝ)+1)⁻¹) atTop (𝓝 (10*0)))
  have hlo : Tendsto (fun N : ℕ => Real.pi/Real.sqrt 8-10/(8*((N/8:ℕ):ℝ)+1))
      atTop (𝓝 (Real.pi/Real.sqrt 8)) := by
    simpa using tendsto_const_nhds.sub ht
  have hhi : Tendsto (fun N : ℕ => Real.pi/Real.sqrt 8+10/(8*((N/8:ℕ):ℝ)+1))
      atTop (𝓝 (Real.pi/Real.sqrt 8)) := by
    simpa using tendsto_const_nhds.add ht
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi
    (fun N => by linarith [(abs_le.mp (ordinary_error N)).1])
    (fun N => by linarith [(abs_le.mp (ordinary_error N)).2])

#print axioms chiInt_mul
#print axioms chiInt_nonzero_sq
#print axioms chi8
#print axioms chi8_apply
#print axioms realCharacter_eq_re
#print axioms realCharacter_period
#print axioms realCharacter_abs_le
#print axioms realCharacter_zero
#print axioms ordinary_block
#print axioms ordinary_aligned
#print axioms ordinary_term_bound
#print axioms ordinary_tail
#print axioms ordinary_error
#print axioms ordinary_tendsto

end Manuscript14.DiscriminantMinusEight
