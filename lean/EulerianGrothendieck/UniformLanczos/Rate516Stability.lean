import UniformLanczos.Rate516Weighted

/-! M12 (201) and (196): arbitrary finite-order hybrid tail, row bound,
weighted residual norm and centre stability. The input is a genuinely
uniform residual and kernel decay; no weighted energy estimate is assumed. -/
noncomputable section
namespace UniformLanczos.Rate516Stability
open Finset UniformLanczos.Rate514 UniformLanczos.Rate514Assembly UniformLanczos.Rate516Weighted

theorem hybrid_tail_general (q : ℕ) (j : ℤ) (L : ℕ) {k : ℤ} (hk : k ∈ Finset.Icc (j - L) (j + L))
    (c : ℤ → ℝ) {Cf : ℝ} (hCf : 0 ≤ Cf) (hc0 : ∀ m ∈ Finset.Icc (j - L) (j + L), c m = 0)
    (hc : ∀ m, |c m| ≤ 1) :
    ∑' m : ℤ, |c m| * (Cf * ((1 + |(k:ℝ) - m|) ^ (q+2))⁻¹) ≤
      Cf * Z2 * ((1 + Rate514.Dist L j k) ^ q)⁻¹ := by
  set D := Rate514.Dist L j k
  have hD1 := dist_ge_one j L hk
  set g : ℤ → ℝ := fun n => ((1 + 1 * |(n:ℝ)|) ^ 2)⁻¹
  have hgs : Summable g := summable_profile one_pos le_rfl
  have hg' : Summable fun m : ℤ => Cf * ((1 + D) ^ q)⁻¹ * g (m - k) :=
    ((Equiv.subRight k).summable_iff.mpr hgs).mul_left _
  have hpt : ∀ m : ℤ, |c m| * (Cf * ((1 + |(k:ℝ) - m|) ^ (q+2))⁻¹) ≤
      Cf * ((1 + D) ^ q)⁻¹ * g (m - k) := by
    intro m
    have hgm : g (m - k) = ((1 + |(k:ℝ) - m|) ^ 2)⁻¹ := by
      simp only [g, one_mul]; push_cast; rw [abs_sub_comm]
    rw [hgm]
    by_cases hm : m ∈ Finset.Icc (j - L) (j + L)
    · rw [hc0 m hm, abs_zero, zero_mul]; positivity
    · have hdm := dist_le_of_not_mem j L hk hm
      set x := |(k:ℝ) - m|
      have hx : 1 + D ≤ 1 + x := by linarith
      have hpos : 0 < 1 + D := by linarith
      have h5 : ((1 + x) ^ (q+2))⁻¹ ≤ ((1 + D) ^ q)⁻¹ * ((1 + x) ^ 2)⁻¹ := by
        rw [← mul_inv]
        apply inv_anti₀ (by positivity)
        rw [show (1 + x) ^ (q+2) = (1 + x) ^ q * (1 + x) ^ 2 by rw [pow_add]]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hpos.le hx q) (by positivity)
      calc |c m| * (Cf * ((1 + x) ^ (q+2))⁻¹) ≤ 1 * (Cf * ((1 + x) ^ (q+2))⁻¹) :=
            mul_le_mul_of_nonneg_right (hc m) (by positivity)
        _ ≤ Cf * (((1 + D) ^ q)⁻¹ * ((1 + x) ^ 2)⁻¹) := by
            rw [one_mul]; exact mul_le_mul_of_nonneg_left h5 hCf
        _ = Cf * ((1 + D) ^ q)⁻¹ * ((1 + x) ^ 2)⁻¹ := by ring
  have hsum : Summable (fun m : ℤ => |c m| * (Cf * ((1 + |(k:ℝ) - m|) ^ (q+2))⁻¹)) :=
    Summable.of_nonneg_of_le (fun m => by positivity) hpt hg'
  calc ∑' m : ℤ, |c m| * (Cf * ((1 + |(k:ℝ) - m|) ^ (q+2))⁻¹)
      ≤ ∑' m : ℤ, Cf * ((1 + D) ^ q)⁻¹ * g (m - k) := hsum.tsum_le_tsum hpt hg'
    _ = Cf * ((1 + D) ^ q)⁻¹ * Z2 := by
        rw [tsum_mul_left]; congr 1; exact (Equiv.subRight k).tsum_eq g
    _ = Cf * Z2 * ((1 + D) ^ q)⁻¹ := by ring


theorem inverse_power_mono (a : ℝ) (ha : 1 ≤ a) {p q : ℕ} (hpq : p ≤ q) :
    (a^q)⁻¹ ≤ (a^p)⁻¹ :=
  inv_anti₀ (by positivity) (pow_le_pow_right₀ ha hpq)

theorem weight_sq_le (N : ℕ) (hN : 1 ≤ N) (ε : ℝ) (hε : 0 ≤ ε) (j k : ℤ) :
    weightRoot N ε j k ^ 2 ≤ ω ε j k := by
  have hx : 1 ≤ 1+ε*|(k:ℝ)-j| := by nlinarith [mul_nonneg hε (abs_nonneg ((k:ℝ)-j))]
  simp only [weightRoot,ω,sw,inv_pow,← pow_mul]
  exact inverse_power_mono _ hx (by omega)

def majorant (n : ℕ) (CB : ℝ) (k m : ℤ) : ℝ :=
  ((n+2:ℕ):ℝ)^2 * CB * ((1+|(k:ℝ)-m|)^2)⁻¹

theorem row_majorant_bound (W : Finset ℤ) (n : ℕ) (CB : ℝ) (hCB : 0 ≤ CB) (k : ℤ) :
    ∑ m ∈ W, majorant n CB k m ≤ ((n+2:ℕ):ℝ)^2*CB*Z2 := by
  unfold majorant
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hterm (m : ℤ) : ((1+|(k:ℝ)-m|)^2)⁻¹ = ((1+1*|((k-m:ℤ):ℝ)|)^2)⁻¹ := by
    push_cast; rw [one_mul]
  simp_rw [hterm]
  exact sum_le_tsum_of_injOn (fun m => k-m) (fun x _ y _ hxy => by simpa using hxy)
    (fun n => inv_nonneg.mpr (pow_nonneg (by positivity) _))
    (summable_profile one_pos (by norm_num))

theorem correction_majorant (n P : ℕ) (hP : n+4 ≤ P)
    (ε CB : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hCB : 0 ≤ CB)
    (B : ℤ → ℤ → ℝ)
    (hdecay : ∀ k m : ℤ, |B k m| ≤ CB*((1+|(k:ℝ)-m|)^P)⁻¹)
    (j k m : ℤ) :
    (weightRoot (n+2) ε j k-weightRoot (n+2) ε j m)^2 * |B k m| ≤
      ε^2 * majorant n CB k m * (weightRoot (n+2) ε j k*weightRoot (n+2) ε j m) := by
  let a := |(k:ℝ)-m|
  let x := 1+a
  let s := weightRoot (n+2) ε j k*weightRoot (n+2) ε j m
  have ha : 0 ≤ a := abs_nonneg _
  have hx : 1 ≤ x := by dsimp [x]; linarith
  have hs : 0 ≤ s := by
    unfold s weightRoot
    exact mul_nonneg (pow_nonneg (sw_pos hε _ _).le _) (pow_nonneg (sw_pos hε _ _).le _)
  have hpow : (1+ε*a)^n ≤ x^n := by
    apply pow_le_pow_left₀ (by positivity)
    dsimp [x]
    nlinarith [mul_le_mul_of_nonneg_right hε1 ha]
  have hsq : a^2 ≤ x^2 := by dsimp [x]; nlinarith
  have hdec : |B k m| ≤ CB*(x^(n+4))⁻¹ :=
    (hdecay k m).trans (mul_le_mul_of_nonneg_left (inverse_power_mono x hx hP) hCB)
  have hp : a^2*(1+ε*a)^n*|B k m| ≤ CB*(x^2)⁻¹ := by
    calc
      _ ≤ (x^2*x^n)*(CB*(x^(n+4))⁻¹) :=
        mul_le_mul (mul_le_mul hsq hpow (by positivity) (by positivity)) hdec
          (abs_nonneg _) (by positivity)
      _ = _ := by
        rw [show n+4 = 2+n+2 by omega,pow_add x (2+n) 2,pow_add x 2 n]
        have hx0 : x ≠ 0 := by linarith
        field_simp
        <;> ring
  have h := mul_le_mul_of_nonneg_right (weight_comparison ε hε j k m n) (abs_nonneg (B k m))
  calc
    _ ≤ _ := h
    _ = (ε^2*((n+2:ℕ):ℝ)^2*s)*(a^2*(1+ε*a)^n*|B k m|) := by dsimp [s,a]; ring
    _ ≤ (ε^2*((n+2:ℕ):ℝ)^2*s)*(CB*(x^2)⁻¹) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by dsimp [majorant,s,x,a]; ring

/-- Inner/outer window estimate for arbitrary N. The full boundary
factor is retained as a summable inverse square. -/
theorem tail_weight_bound (N q : ℕ) (hN : 1 ≤ N) (hq : N+1 ≤ q)
    (j : ℤ) (L : ℕ) (hL : 2 ≤ L) {k : ℤ}
    (hk : k ∈ Finset.Icc (j-L) (j+L))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    weightRoot (N+1) ε j k ^ 2 * ((1+Rate514.Dist L j k)^(2*q))⁻¹ ≤
      ((ε*(L:ℝ)/2)^(2*N))⁻¹ * ((1+Rate514.Dist L j k)^2)⁻¹ := by
  let a := |(k:ℝ)-j|
  let x := 1+ε*a
  let y := 1+Rate514.Dist L j k
  let z := ε*(L:ℝ)/2
  have ha : 0 ≤ a := abs_nonneg _
  have hx : 1 ≤ x := by dsimp [x]; nlinarith [mul_nonneg hε.le ha]
  have hy : 1 ≤ y := by dsimp [y]; linarith [dist_ge_one j L hk]
  have hz : 0 < z := by dsimp [z]; positivity
  have hzL : z ≤ (L:ℝ)/2 := by dsimp [z]; nlinarith [mul_le_mul_of_nonneg_right hε1 (Nat.cast_nonneg L : (0:ℝ) ≤ L)]
  have hx1 : 1 ≤ x^(2*(N+1)) := one_le_pow₀ hx
  have hy1 : 1 ≤ y^(2*(q-1)) := one_le_pow₀ hy
  have hp : z^(2*N) ≤ x^(2*(N+1))*y^(2*(q-1)) := by
    by_cases hcase : a ≤ (L:ℝ)/2
    · have hzy : z ≤ y := by dsimp [y,Rate514.Dist]; dsimp [a] at hcase; linarith
      have h := (pow_le_pow_left₀ hz.le hzy (2*N)).trans (pow_le_pow_right₀ hy (by omega : 2*N ≤ 2*(q-1)))
      exact h.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hx1 (by positivity : 0 ≤ y^(2*(q-1))))
    · have hzx : z ≤ x := by dsimp [x,z]; nlinarith [mul_nonneg hε.le (sub_nonneg.mpr (le_of_not_ge hcase))]
      have h := (pow_le_pow_left₀ hz.le hzx (2*N)).trans (pow_le_pow_right₀ hx (by omega : 2*N ≤ 2*(N+1)))
      exact h.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hy1 (by positivity : 0 ≤ x^(2*(N+1)))))
  change (x⁻¹^(N+1))^2*(y^(2*q))⁻¹ ≤ (z^(2*N))⁻¹*(y^2)⁻¹
  rw [←pow_mul,inv_pow,show (N+1)*2=2*(N+1) by omega,
    show 2*q=2*(q-1)+2 by omega,pow_add y, mul_inv,←mul_assoc,←mul_inv]
  exact mul_le_mul_of_nonneg_right (inv_anti₀ (pow_pos hz _) hp) (by positivity)

/-- The actual order-N weighted residual sum, with L>=c M. -/
theorem residual_sum_order (N q : ℕ) (hN : 1 ≤ N) (hq : N+1 ≤ q)
    (j : ℤ) (L : ℕ) (hL : 2 ≤ L) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {M C c : ℝ} (hM : 0 < M) (hc : 0 < c) (hLM : c*M ≤ L)
    (r : ℤ → ℝ)
    (hr : ∀ k ∈ Finset.Icc (j-L) (j+L),
      |r k| ≤ C*(1/M^N+((1+Rate514.Dist L j k)^q)⁻¹)) :
    ∑ k ∈ Finset.Icc (j-L) (j+L), weightRoot (N+1) ε j k ^ 2 * r k^2 ≤
      2*C^2*(Ωε ε+2*Z2*((ε*c/2)^(2*N))⁻¹)/M^(2*N) := by
  let W := Finset.Icc (j-L) (j+L)
  let w : ℤ → ℝ := fun k => weightRoot (N+1) ε j k ^ 2
  have hw : ∀ k, 0 ≤ w k := fun k => sq_nonneg _
  have hs : ∑ k ∈ W, w k ≤ Ωε ε :=
    (Finset.sum_le_sum fun k _ => weight_sq_le (N+1) (by omega) ε hε.le j k).trans (sum_ω_le W hε j)
  have hsq (k : ℤ) (hk : k ∈ W) :
      r k^2 ≤ 2*C^2*(1/M^(2*N)+((1+Rate514.Dist L j k)^(2*q))⁻¹) := by
    have h := pow_le_pow_left₀ (abs_nonneg (r k)) (hr k hk) 2
    rw [sq_abs] at h
    let a := 1/M^N
    let b := ((1+Rate514.Dist L j k)^q)⁻¹
    have hh : (C*(a+b))^2 ≤ 2*C^2*(a^2+b^2) := by nlinarith [sq_nonneg (C*(a-b))]
    have h' := h.trans hh
    dsimp [a,b] at h'
    rwa [div_pow,one_pow,inv_pow,←pow_mul,←pow_mul,mul_comm N 2,mul_comm q 2] at h'
  have htail : ∑ k ∈ W, w k*((1+Rate514.Dist L j k)^(2*q))⁻¹ ≤
      ((ε*(L:ℝ)/2)^(2*N))⁻¹*(2*Z2) := by
    calc
      _ ≤ ∑ k ∈ W, ((ε*(L:ℝ)/2)^(2*N))⁻¹*((1+Rate514.Dist L j k)^2)⁻¹ :=
        Finset.sum_le_sum fun k hk => tail_weight_bound N q hN hq j L hL hk hε hε1
      _ = _ * ∑ k ∈ W, ((1+Rate514.Dist L j k)^2)⁻¹ := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (sum_dist_le L j) (by positivity)
  have hscale : ((ε*(L:ℝ)/2)^(2*N))⁻¹ ≤ ((ε*c/2)^(2*N))⁻¹/M^(2*N) := by
    have hp : 0 < ε*c/2*M := by positivity
    have hh : ε*c/2*M ≤ ε*(L:ℝ)/2 := by
      have := mul_le_mul_of_nonneg_left hLM hε.le
      nlinarith
    calc
      _ ≤ ((ε*c/2*M)^(2*N))⁻¹ :=
        inv_anti₀ (pow_pos hp _) (pow_le_pow_left₀ hp.le hh _)
      _ = _ := by rw [mul_pow,mul_inv,div_eq_mul_inv]
  have hz : 0 ≤ Z2 := tsum_nonneg fun n => by positivity
  have hA : (1/M^(2*N))*(∑ k ∈ W, w k) ≤ Ωε ε/M^(2*N) := by
    rw [one_div_mul_eq_div]
    exact div_le_div_of_nonneg_right hs (by positivity)
  calc
    _ ≤ ∑ k ∈ W, w k*(2*C^2*(1/M^(2*N)+((1+Rate514.Dist L j k)^(2*q))⁻¹)) :=
      Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_left (hsq k hk) (hw k)
    _ = 2*C^2*((1/M^(2*N))*(∑ k ∈ W,w k)+
        ∑ k ∈ W,w k*((1+Rate514.Dist L j k)^(2*q))⁻¹) := by
      rw [Finset.mul_sum,←Finset.sum_add_distrib,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ ≤ 2*C^2*(Ωε ε/M^(2*N)+(((ε*c/2)^(2*N))⁻¹/M^(2*N))*(2*Z2)) :=
      mul_le_mul_of_nonneg_left (add_le_add hA (htail.trans (mul_le_mul_of_nonneg_right hscale (by positivity)))) (by positivity)
    _ = _ := by ring

theorem rate_assembly_order (n : ℕ) (j : ℤ) (L : ℕ) (hL : 2 ≤ L)
    {ε M C c μ₀ CB : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hM : 0 < M) (hc : 0 < c)
    (hLM : c*M ≤ L) (hμ₀ : 0 < μ₀) (hCB : 0 ≤ CB)
    (B : ℤ → ℤ → ℝ) (d r μ : ℤ → ℝ)
    (hsym : ∀ k ∈ Finset.Icc (j-L) (j+L), ∀ m ∈ Finset.Icc (j-L) (j+L), B k m = B m k)
    (hpsd : ∀ x : ℤ → ℝ, 0 ≤ ∑ k ∈ Finset.Icc (j-L) (j+L), ∑ m ∈ Finset.Icc (j-L) (j+L), B k m*x k*x m)
    (hdecay : ∀ k m : ℤ, |B k m| ≤ CB*((1+|(k:ℝ)-m|)^(3*(n+1)+2))⁻¹)
    (hμ : ∀ k ∈ Finset.Icc (j-L) (j+L), μ₀ ≤ μ k)
    (hh : ∀ k ∈ Finset.Icc (j-L) (j+L), r k = ∑ m ∈ Finset.Icc (j-L) (j+L), B k m*d m+μ k*d k)
    (hsmall : ε^2*(((n+2:ℕ):ℝ)^2*CB*Z2) ≤ μ₀)
    (hr : ∀ k ∈ Finset.Icc (j-L) (j+L),
      |r k| ≤ C*(1/M^(n+1)+((1+Rate514.Dist L j k)^(3*(n+1)))⁻¹)) :
    d j^2 ≤ 4/μ₀^2*(2*C^2*(Ωε ε+2*Z2*((ε*c/2)^(2*(n+1)))⁻¹)/M^(2*(n+1))) := by
  let W := Finset.Icc (j-L) (j+L)
  have hj : j ∈ W := by
    simp only [W,Finset.mem_Icc]
    constructor <;> linarith [(Nat.cast_nonneg L : (0:ℤ) ≤ L)]
  have he := centre_energy W j hj (weightRoot (n+2) ε j) d r μ
    (weightRoot_self _ _ _) B (majorant n CB) hμ₀ hsym hpsd
    (correction_majorant n (3*(n+1)+2) (by omega) ε CB hε.le hε1 hCB B hdecay j)
    (fun k m => by unfold majorant; positivity)
    (fun k _ m _ => by unfold majorant; rw [abs_sub_comm])
    (fun k _ => row_majorant_bound W n CB hCB k) hμ hh hsmall
  have hs := residual_sum_order (n+1) (3*(n+1)) (by omega) (by omega) j L hL hε hε1 hM hc hLM r hr
  exact he.trans (mul_le_mul_of_nonneg_left hs (by positivity))

end UniformLanczos.Rate516Stability
#print axioms UniformLanczos.Rate516Stability.hybrid_tail_general
#print axioms UniformLanczos.Rate516Stability.inverse_power_mono
#print axioms UniformLanczos.Rate516Stability.weight_sq_le
#print axioms UniformLanczos.Rate516Stability.row_majorant_bound
#print axioms UniformLanczos.Rate516Stability.correction_majorant
#print axioms UniformLanczos.Rate516Stability.tail_weight_bound
#print axioms UniformLanczos.Rate516Stability.residual_sum_order
#print axioms UniformLanczos.Rate516Stability.rate_assembly_order
