import Mathlib

/-! Frozen M14.119, prop:dominant-pole-modulus, discriminant -8.
An elementary integral proof of the actual grouped Dirichlet series at 1.
No class-number formula or numerical equality is assumed. The four nonzero
residues modulo 8 are +1,+1,-1,-1. The grouped series is absolutely
convergent (the ungrouped character series is only conditionally convergent).
Identification with Mathlib's analytically continued DirichletCharacter.LFunction
is a separate obligation. -/
open MeasureTheory Set Filter Finset
open scoped BigOperators Topology
noncomputable section
namespace Manuscript14.DiscriminantMinusEight

def kernel (x : ℝ) : ℝ := (1+x^2)/(1+x^4)

def primitive (x : ℝ) : ℝ :=
  (Real.arctan (Real.sqrt 2*x+1) + Real.arctan (Real.sqrt 2*x-1))/Real.sqrt 2

theorem kernel_continuous : Continuous kernel := by
  unfold kernel
  exact (continuous_const.add (continuous_id.pow 2)).div
    (continuous_const.add (continuous_id.pow 4)) (fun x => by positivity)

theorem primitive_derivative (x : ℝ) : HasDerivAt primitive (kernel x) x := by
  let s := Real.sqrt 2
  have hs : 0 < s := Real.sqrt_pos.2 (by norm_num)
  have hs2 : s^2 = 2 := Real.sq_sqrt (by norm_num)
  have hp := (Real.hasDerivAt_arctan (s*x+1)).comp x
    (((hasDerivAt_id x).const_mul s).add_const 1)
  have hm := (Real.hasDerivAt_arctan (s*x-1)).comp x
    (((hasDerivAt_id x).const_mul s).sub_const 1)
  have hd := (hp.add hm).div_const s
  have hA : 0 < 1+(s*x+1)^2 := by positivity
  have hB : 0 < 1+(s*x-1)^2 := by positivity
  have hsum : (1+(s*x+1)^2)+(1+(s*x-1)^2) = 4*(1+x^2) := by
    calc
      _ = 4+2*s^2*x^2 := by ring
      _ = _ := by rw [hs2]; ring
  have hprod : (1+(s*x+1)^2)*(1+(s*x-1)^2) = 4*(1+x^4) := by
    calc
      _ = 4+(s^2)^2*x^4 := by ring
      _ = _ := by rw [hs2]; ring
  have he : (1/(1+(s*x+1)^2)*s + 1/(1+(s*x-1)^2)*s)/s = kernel x := by
    unfold kernel
    calc
      _ = ((1+(s*x+1)^2)+(1+(s*x-1)^2)) /
          ((1+(s*x+1)^2)*(1+(s*x-1)^2)) := by
            field_simp [hs.ne', hA.ne', hB.ne'] <;> ring
      _ = _ := by
        rw [hsum,hprod]
        field_simp [show 1+x^4 ≠ 0 by positivity] <;> ring
  rw [← he]
  unfold primitive
  change HasDerivAt (fun y : ℝ => (Real.arctan (s*y+1) + Real.arctan (s*y-1))/s) _ x
  simpa only [Function.comp_apply, Pi.add_apply, id_eq, mul_one] using hd

theorem primitive_zero : primitive 0 = 0 := by
  unfold primitive
  simp [Real.arctan_neg, Real.arctan_one]

theorem primitive_one : primitive 1 = Real.pi/Real.sqrt 8 := by
  let s := Real.sqrt 2
  have hs : 0 < s := Real.sqrt_pos.2 (by norm_num)
  have hs2 : s^2 = 2 := Real.sq_sqrt (by norm_num)
  have h1 : 0 < s+1 := by positivity
  have hinv : s-1 = (s+1)⁻¹ := by
    rw [← one_div]
    apply (eq_div_iff h1.ne').2
    nlinarith [hs2]
  have h8 : Real.sqrt 8 = 2*s := by
    dsimp [s]
    rw [show (8:ℝ)=4*2 by norm_num, Real.sqrt_mul (by norm_num : (0:ℝ)≤4)]
    norm_num
  simp only [primitive,mul_one]
  change (Real.arctan (s+1)+Real.arctan (s-1))/s = _
  rw [hinv,Real.arctan_inv_of_pos h1,h8]
  field_simp [hs.ne'] <;> ring

theorem integral_kernel : (∫ x in (0:ℝ)..1, kernel x) = Real.pi/Real.sqrt 8 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => primitive_derivative x) (kernel_continuous.intervalIntegrable _ _),
    primitive_one,primitive_zero,sub_zero]

def term (n : ℕ) (x : ℝ) : ℝ :=
  x^(8*n)+x^(8*n+2)-x^(8*n+4)-x^(8*n+6)

def block (n : ℕ) : ℝ :=
  1/(8*(n:ℝ)+1)+1/(8*(n:ℝ)+3)-1/(8*(n:ℝ)+5)-1/(8*(n:ℝ)+7)

theorem term_continuous (n : ℕ) : Continuous (term n) := by unfold term; fun_prop

theorem term_factor (n : ℕ) (x : ℝ) :
    term n x = kernel x*x^(8*n)*(1-x^8) := by
  have hd : 1+x^4 ≠ 0 := by positivity
  unfold term kernel
  rw [pow_add,pow_add,pow_add]
  field_simp [hd] <;> ring

theorem block_integral (n : ℕ) :
    (∫ x in (0:ℝ)..1, term n x) = block n := by
  unfold term block
  have h (k : ℕ) : IntervalIntegrable (fun x : ℝ => x^k) volume 0 1 :=
    (continuous_id.pow k).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub
    (((h (8*n)).add (h (8*n+2))).sub (h (8*n+4))) (h (8*n+6)),
    intervalIntegral.integral_sub ((h (8*n)).add (h (8*n+2))) (h (8*n+4)),
    intervalIntegral.integral_add (h (8*n)) (h (8*n+2))]
  simp only [integral_pow, one_pow, zero_pow (Nat.succ_ne_zero _), sub_zero, Nat.cast_add,
    Nat.cast_mul, Nat.cast_ofNat]
  ring

theorem block_nonneg (n : ℕ) : 0 ≤ block n := by
  unfold block
  have h₁ : 1/(8*(n:ℝ)+5) ≤ 1/(8*(n:ℝ)+1) := by
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  have h₂ : 1/(8*(n:ℝ)+7) ≤ 1/(8*(n:ℝ)+3) := by
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  linarith

theorem finite_geometric (N : ℕ) (x : ℝ) :
    (∑ n ∈ Finset.range N, term n x) = kernel x*(1-x^(8*N)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ,ih,term_factor]
    rw [show 8*(N+1)=8*N+8 by omega,pow_add]
    ring

theorem partial_sum_identity (N : ℕ) :
    (∑ n ∈ Finset.range N, block n) =
      ∫ x in (0:ℝ)..1, kernel x*(1-x^(8*N)) := by
  simp_rw [← block_integral]
  rw [← intervalIntegral.integral_finsetSum
    (fun n _ => (term_continuous n).intervalIntegrable 0 1)]
  simp_rw [finite_geometric]

theorem partial_sum_error (N : ℕ) :
    0 ≤ Real.pi/Real.sqrt 8 - (∑ n ∈ Finset.range N, block n) ∧
    Real.pi/Real.sqrt 8 - (∑ n ∈ Finset.range N, block n) ≤ 2/(8*(N:ℝ)+1) := by
  let f : ℝ → ℝ := fun x => kernel x*x^(8*N)
  have hf : Continuous f := kernel_continuous.mul (continuous_id.pow _)
  have hg : Continuous (fun x : ℝ => (2:ℝ)*x^(8*N)) :=
    continuous_const.mul (continuous_id.pow _)
  have he : Real.pi/Real.sqrt 8 - (∑ n ∈ Finset.range N, block n) =
      ∫ x in (0:ℝ)..1, f x := by
    have hcont : Continuous (fun x : ℝ => kernel x*(1-x^(8*N))) :=
      kernel_continuous.mul (continuous_const.sub (continuous_id.pow _))
    have hint : IntervalIntegrable (fun x : ℝ => kernel x*(1-x^(8*N))) volume 0 1 :=
      hcont.intervalIntegrable _ _
    rw [← integral_kernel,partial_sum_identity,
      ← intervalIntegral.integral_sub (kernel_continuous.intervalIntegrable 0 1) hint]
    congr 1
    funext x
    dsimp [f]
    ring
  have hz : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ f x := by
    intro x hx
    dsimp [f,kernel]
    exact mul_nonneg (by positivity) (pow_nonneg hx.1 _)
  have hb : ∀ x ∈ Icc (0:ℝ) 1, f x ≤ 2*x^(8*N) := by
    intro x hx
    have hk : kernel x ≤ 2 := by
      unfold kernel
      apply (div_le_iff₀ (by positivity : 0 < 1+x^4)).2
      have hx2 : x^2 ≤ 1 := by nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hx.2)]
      nlinarith [pow_nonneg hx.1 4]
    exact mul_le_mul_of_nonneg_right hk (pow_nonneg hx.1 _)
  rw [he]
  constructor
  · have h := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ)≤1)
      (continuous_const.intervalIntegrable 0 1) (hf.intervalIntegrable 0 1) hz
    simpa using h
  · have h := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ)≤1)
      (hf.intervalIntegrable 0 1) (hg.intervalIntegrable 0 1) hb
    calc
      _ ≤ ∫ x in (0:ℝ)..1, 2*x^(8*N) := h
      _ = _ := by rw [intervalIntegral.integral_const_mul,integral_pow]
                  simp only [one_pow,zero_pow (Nat.succ_ne_zero _),sub_zero,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
                  ring

/-- Infinite series over the four nonzero character residues in each period. -/
theorem grouped_dirichlet_hasSum : HasSum block (Real.pi/Real.sqrt 8) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg block_nonneg]
  have hNat : Tendsto (fun N : ℕ => (N:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hDen : Tendsto (fun N : ℕ => 8*(N:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (hNat.const_mul_atTop (by norm_num))
  have hTail : Tendsto (fun N : ℕ => 2/(8*(N:ℝ)+1)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_const_nhds.mul hDen.inv_tendsto_atTop :
      Tendsto (fun N : ℕ => 2*(8*(N:ℝ)+1)⁻¹) atTop (𝓝 (2*0)))
  have hLower : Tendsto (fun N : ℕ => Real.pi/Real.sqrt 8-2/(8*(N:ℝ)+1))
      atTop (𝓝 (Real.pi/Real.sqrt 8)) := by
    simpa using tendsto_const_nhds.sub hTail
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hLower tendsto_const_nhds
    (fun N => by linarith [(partial_sum_error N).2])
    (fun N => by linarith [(partial_sum_error N).1])

theorem grouped_dirichlet_value : (∑' n, block n) = Real.pi/Real.sqrt 8 :=
  grouped_dirichlet_hasSum.tsum_eq

#print axioms kernel_continuous
#print axioms primitive_derivative
#print axioms primitive_zero
#print axioms primitive_one
#print axioms integral_kernel
#print axioms term_continuous
#print axioms term_factor
#print axioms block_integral
#print axioms block_nonneg
#print axioms finite_geometric
#print axioms partial_sum_identity
#print axioms partial_sum_error
#print axioms grouped_dirichlet_hasSum
#print axioms grouped_dirichlet_value

end Manuscript14.DiscriminantMinusEight
