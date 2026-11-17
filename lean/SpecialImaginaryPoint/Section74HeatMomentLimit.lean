import Mathlib

/-! M14 §7.4, equations (122)–(125), all-order spectral moments.
Authoritative TeX SHA256 b0aba7205b0e915ff49512ffd66f4deeaef29d2de766293be58c090820aeca68.
A uniform quarter-time heat bound yields an index-wise summable
majorant of order 1/(n+1)^2 for every differentiated summand.
Tannery's theorem then passes to the full moment series, jointly
with a varying positive temperature parameter. This is a sequence-level
theorem; operator heat-kernel comparison and termwise differentiability
remain separate. -/

open Filter Topology
noncomputable section
namespace Manuscript14.HeatMomentLimit

def moment (k : ℕ) (x e : ℝ) : ℝ := (-e)^k * Real.exp (-x*e)

/-- Ordered spectral counting: the first n+1 terms bound the nth weight. -/
theorem ordered_weight_bound (E : ℕ → ℝ) (hm : Monotone E)
    (t C : ℝ) (ht : 0 < t)
    (hs : Summable (fun n => Real.exp (-t * E n)))
    (hC : (∑' n, Real.exp (-t * E n)) ≤ C) (n : ℕ) :
    Real.exp (-t * E n) ≤ C / ((n : ℝ)+1) := by
  have hp : ∀ j ∈ Finset.range (n+1),
      Real.exp (-t * E n) ≤ Real.exp (-t * E j) := by
    intro j hj
    apply Real.exp_le_exp.mpr
    have he := hm (show j ≤ n by have := Finset.mem_range.mp hj; omega)
    nlinarith [mul_nonneg ht.le (sub_nonneg.mpr he)]
  have hsum : ((n : ℝ)+1) * Real.exp (-t * E n) ≤ C := by
    calc
      _ = ∑ j ∈ Finset.range (n+1), Real.exp (-t * E n) := by
        simp [nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      _ ≤ ∑ j ∈ Finset.range (n+1), Real.exp (-t * E j) :=
        Finset.sum_le_sum hp
      _ ≤ ∑' j, Real.exp (-t * E j) :=
        hs.sum_le_tsum _ (fun j _ => (Real.exp_pos _).le)
      _ ≤ C := hC
  apply (le_div_iff₀ (by positivity : 0 < (n:ℝ)+1)).2
  simpa [mul_comm] using hsum

/-- Universal factorial estimate with an explicit positive-time margin. -/
theorem moment_half_time (k : ℕ) (x e δ : ℝ)
    (hd : 0 < δ) (hx : δ ≤ x) (he : 0 ≤ e) :
    ‖moment k x e‖ ≤
      ((2/δ)^k * (k.factorial : ℝ)) * Real.exp (-(δ/2)*e) := by
  let u : ℝ := (δ/2)*e
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hpow := Real.pow_div_factorial_le_exp u hu k
  have hf : 0 < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hp : u^k ≤ Real.exp u * (k.factorial : ℝ) :=
    (div_le_iff₀ hf).mp hpow
  have hepow : e^k = (2/δ)^k * u^k := by
    rw [← mul_pow]
    congr 1
    dsimp [u]
    field_simp
    <;> ring
  have hprod : u^k * Real.exp (-2*u) ≤
      (k.factorial : ℝ) * Real.exp (-u) := by
    calc
      _ ≤ (Real.exp u * (k.factorial : ℝ)) * Real.exp (-2*u) :=
        mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
      _ = (k.factorial : ℝ) * Real.exp (-u) := by
        rw [show -u = u + (-2*u) by ring, Real.exp_add]
        ring
  calc
    ‖moment k x e‖ = e^k * Real.exp (-x*e) := by
      simp [moment, Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg he,
        abs_of_pos (Real.exp_pos _)]
    _ ≤ e^k * Real.exp (-(δ)*e) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg he k)
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg he (sub_nonneg.mpr hx)]
    _ = (2/δ)^k * (u^k * Real.exp (-2*u)) := by
      rw [hepow, show -(δ)*e = -2*u by dsimp [u]; ring]
      ring
    _ ≤ (2/δ)^k * ((k.factorial : ℝ) * Real.exp (-u)) :=
      mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = _ := by dsimp [u]; ring

/-- Majorant derived solely from the earlier heat-trace bound and ordering,
    without a uniform linear lower eigenvalue asymptotic. -/
theorem moment_index_majorant (k : ℕ) (E : ℕ → ℝ) (hm : Monotone E)
    (he : ∀ n, 0 ≤ E n) (x δ C : ℝ) (hd : 0 < δ) (hx : δ ≤ x)
    (hs : Summable (fun n => Real.exp (-(δ/4)*E n)))
    (hC : (∑' n, Real.exp (-(δ/4)*E n)) ≤ C) (n : ℕ) :
    ‖moment k x (E n)‖ ≤
      (((2/δ)^k * (k.factorial : ℝ)) * C^2) * (1/((n:ℝ)+1)^2) := by
  have hb := ordered_weight_bound E hm (δ/4) C (by positivity) hs hC n
  have hq : Real.exp (-(δ/2)*E n) ≤ (C/((n:ℝ)+1))^2 := by
    rw [show -(δ/2)*E n = -(δ/4)*E n + -(δ/4)*E n by ring,
      Real.exp_add, ← pow_two]
    exact pow_le_pow_left₀ (Real.exp_pos _).le hb 2
  calc
    _ ≤ ((2/δ)^k * (k.factorial : ℝ)) * Real.exp (-(δ/2)*E n) :=
      moment_half_time k x (E n) δ hd hx (he n)
    _ ≤ ((2/δ)^k * (k.factorial : ℝ)) * (C/((n:ℝ)+1))^2 :=
      mul_le_mul_of_nonneg_left hq (by positivity)
    _ = _ := by
      have hh : (C/((n:ℝ)+1))^2 = C^2 * (1/((n:ℝ)+1)^2) := by
        rw [div_pow, div_eq_mul_inv, one_div]
      rw [hh, mul_assoc]

/-- Joint limit of the complete spectral moments for all k, also allowing
    x to vary and approach a positive limiting temperature. -/
theorem full_moment_limit {ι : Type*} {l : Filter ι}
    (k : ℕ) (E : ι → ℕ → ℝ) (L : ℕ → ℝ)
    (x : ι → ℝ) (x₀ δ C : ℝ) (hd : 0 < δ)
    (hx : Tendsto x l (𝓝 x₀))
    (hE : ∀ n, Tendsto (fun i => E i n) l (𝓝 (L n)))
    (hbound : ∀ᶠ i in l, δ ≤ x i ∧ Monotone (E i) ∧
      (∀ n, 0 ≤ E i n) ∧
      Summable (fun n => Real.exp (-(δ/4)*E i n)) ∧
      (∑' n, Real.exp (-(δ/4)*E i n)) ≤ C) :
    Tendsto (fun i => ∑' n, moment k (x i) (E i n)) l
      (𝓝 (∑' n, moment k x₀ (L n))) := by
  have hp : Summable (fun n : ℕ => 1/((n:ℝ)+1)^2) := by
    have hs : Summable (fun n : ℕ => 1/(n:ℝ)^2) :=
      Real.summable_one_div_nat_pow.mpr (by omega)
    simpa [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).2 hs
  refine tendsto_tsum_of_dominated_convergence
    (hp.mul_left (((2/δ)^k * (k.factorial : ℝ)) * C^2))
      (fun n => ?_) ?_
  · unfold moment
    exact ((hE n).neg.pow k).mul (Real.continuous_exp.continuousAt.tendsto.comp
      (hx.neg.mul (hE n)))
  · filter_upwards [hbound] with i hi n
    exact moment_index_majorant k (E i) hi.2.1 hi.2.2.1 (x i) δ C hd
      hi.1 hi.2.2.2.1 hi.2.2.2.2 n

#print axioms ordered_weight_bound
#print axioms moment_half_time
#print axioms moment_index_majorant
#print axioms full_moment_limit

end Manuscript14.HeatMomentLimit
