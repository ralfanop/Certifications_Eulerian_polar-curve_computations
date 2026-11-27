import UniformLanczos.Rate514Assembly

/-! M12 (201), arbitrary order weights. Reuses the original finite-window
symmetrisation and energy estimate. The analytic Fourier kernel and its
arbitrary-order decay are separate obligations. -/
noncomputable section
namespace UniformLanczos.Rate516Weighted
open Finset UniformLanczos.Rate514 UniformLanczos.Rate514Assembly

theorem pow_sub_one_bound (q : ℝ) (hq : 1 ≤ q) (n : ℕ) :
    q^(n+1)-1 ≤ (n+1:ℕ) * (q-1)*q^n := by
  have hq0 : 0 ≤ q := by linarith
  induction n with
  | zero => simp
  | succ n ih =>
    have hp : 1 ≤ q^(n+1) := one_le_pow₀ hq
    have h₁ := mul_le_mul_of_nonneg_left ih hq0
    have h₂ := mul_le_mul_of_nonneg_left hp (show 0 ≤ q-1 by linarith)
    push_cast at *
    rw [pow_succ q (n+1)]
    calc
      q^(n+1)*q-1 = q*(q^(n+1)-1)+(q-1) := by ring
      _ ≤ q*((↑n+1)*(q-1)*q^n)+(q-1)*q^(n+1) := add_le_add h₁ h₂
      _ = (↑n+1+1)*(q-1)*(q^(n+1)) := by rw [pow_succ q n]; ring

/-- Ratio form of equation (201), at p = n+2. -/
theorem ratio_bound (q : ℝ) (hq : 1 ≤ q) (n : ℕ) :
    (q^(n+2)-1)^2 / q^(n+2) ≤ ((n+2:ℕ):ℝ)^2*(q-1)^2*q^n := by
  have hq0 : 0 < q := by linarith
  have hp : 1 ≤ q^(n+2) := one_le_pow₀ hq
  have h := pow_sub_one_bound q hq (n+1)
  have hs : (q^(n+2)-1)^2 ≤ (((n+2:ℕ):ℝ)*(q-1)*q^(n+1))^2 :=
    pow_le_pow_left₀ (sub_nonneg.mpr hp) h 2
  apply (div_le_iff₀ (pow_pos hq0 _)).2
  calc
    _ ≤ (((n+2:ℕ):ℝ)*(q-1)*q^(n+1))^2 := hs
    _ = _ := by rw [pow_add q n 1,pow_add q n 2]; ring

theorem ratio_bound_delta (q δ : ℝ) (hq : 1 ≤ q) (hδ : 0 ≤ δ) (h : q ≤ 1+δ) (n : ℕ) :
    (q^(n+2)-1)^2 / q^(n+2) ≤ ((n+2:ℕ):ℝ)^2*δ^2*(1+δ)^n := by
  apply (ratio_bound q hq n).trans
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (show q-1 ≤ δ by linarith) 2) (sq_nonneg _)
  · exact pow_le_pow_left₀ (by linarith) h n
  · positivity
  · positivity

def weightRoot (p : ℕ) (ε : ℝ) (j k : ℤ) : ℝ := (sw ε j k)^p

theorem weightRoot_self (p : ℕ) (ε : ℝ) (j : ℤ) : weightRoot p ε j j = 1 := by
  simp [weightRoot,sw]

/-- Derive the weight comparison directly from the ordered ratio of x and y.
This is the squared relative difference of their negative powers. -/
theorem weight_pair_ordered (x y δ : ℝ) (hx : 1 ≤ x) (hxy : x ≤ y)
    (hδ : 0 ≤ δ) (hd : y-x ≤ δ) (n : ℕ) :
    ((x^(n+2))⁻¹-(y^(n+2))⁻¹)^2 ≤
      ((n+2:ℕ):ℝ)^2*δ^2*(1+δ)^n*((x^(n+2))⁻¹*(y^(n+2))⁻¹) := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hq : 1 ≤ y/x := by rw [le_div_iff₀ hx0]; simpa using hxy
  have hq' : y/x ≤ 1+δ := by
    rw [div_le_iff₀ hx0]
    nlinarith [mul_nonneg hδ (sub_nonneg.mpr hx)]
  have hb := ratio_bound_delta (y/x) δ hq hδ hq' n
  have hden : 0 < (x^(n+2))⁻¹*(y^(n+2))⁻¹ := by positivity
  have he : ((x^(n+2))⁻¹-(y^(n+2))⁻¹)^2 /
      ((x^(n+2))⁻¹*(y^(n+2))⁻¹) =
      ((y/x)^(n+2)-1)^2 / (y/x)^(n+2) := by
    rw [div_pow]
    field_simp
    <;> ring
  rw [← he] at hb
  exact (div_le_iff₀ hden).mp hb

theorem weight_pair (x y δ : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hδ : 0 ≤ δ) (hd : |x-y| ≤ δ) (n : ℕ) :
    ((x^(n+2))⁻¹-(y^(n+2))⁻¹)^2 ≤
      ((n+2:ℕ):ℝ)^2*δ^2*(1+δ)^n*((x^(n+2))⁻¹*(y^(n+2))⁻¹) := by
  rcases le_total x y with h|h
  · exact weight_pair_ordered x y δ hx h hδ (by rw [abs_of_nonpos (sub_nonpos.mpr h)] at hd; linarith) n
  · have hh := weight_pair_ordered y x δ hy h hδ (by rw [abs_of_nonneg (sub_nonneg.mpr h)] at hd; linarith) n
    nlinarith only [hh]

/-- Equation (201), expressed as a product inequality without division by weights. -/
theorem weight_comparison (ε : ℝ) (hε : 0 ≤ ε) (j k m : ℤ) (n : ℕ) :
    (weightRoot (n+2) ε j k-weightRoot (n+2) ε j m)^2 ≤
    ((n+2:ℕ):ℝ)^2*(ε*|(k:ℝ)-m|)^2*(1+ε*|(k:ℝ)-m|)^n*
      (weightRoot (n+2) ε j k*weightRoot (n+2) ε j m) := by
  have hx : 1 ≤ 1+ε*|(k:ℝ)-j| := by nlinarith [mul_nonneg hε (abs_nonneg ((k:ℝ)-j))]
  have hy : 1 ≤ 1+ε*|(m:ℝ)-j| := by nlinarith [mul_nonneg hε (abs_nonneg ((m:ℝ)-j))]
  have hd : |(1+ε*|(k:ℝ)-j|)-(1+ε*|(m:ℝ)-j|)| ≤ ε*|(k:ℝ)-m| := by
    rw [show (1+ε*|(k:ℝ)-j|)-(1+ε*|(m:ℝ)-j|) = ε*(|(k:ℝ)-j|-|(m:ℝ)-j|) by ring,
      abs_mul,abs_of_nonneg hε]
    apply mul_le_mul_of_nonneg_left _ hε
    have h := abs_abs_sub_abs_le_abs_sub ((k:ℝ)-j) ((m:ℝ)-j)
    rw [show (k:ℝ)-j-((m:ℝ)-j)=(k:ℝ)-m by ring] at h
    exact h
  simpa only [weightRoot,sw,inv_pow] using
    weight_pair _ _ _ hx hy (mul_nonneg hε (abs_nonneg _)) hd n

theorem correction_lower_general (W : Finset ℤ) (B : ℤ → ℤ → ℝ) (s d : ℤ → ℝ) (ε S : ℝ) (P : ℤ → ℤ → ℝ)
    (hsym : ∀ k ∈ W, ∀ m ∈ W, B k m = B m k)
    (hss : ∀ k m : ℤ, (s k - s m) ^ 2 * |B k m| ≤ ε ^ 2 * P k m * (s k * s m))
    (hP : ∀ k m, 0 ≤ P k m)
    (hPsym : ∀ k ∈ W, ∀ m ∈ W, P k m = P m k)
    (hrow : ∀ k ∈ W, ∑ m ∈ W, P k m ≤ S) :
    -(ε ^ 2 * S / 2) * ∑ k ∈ W, s k ^ 2 * d k ^ 2 ≤
      (1/2) * ∑ k ∈ W, ∑ m ∈ W, (s k - s m) ^ 2 * B k m * d k * d m := by
  have hterm : ∀ k m : ℤ, |(s k - s m) ^ 2 * B k m * d k * d m| ≤
      ε ^ 2 / 2 * P k m * (s k ^ 2 * d k ^ 2 + s m ^ 2 * d m ^ 2) := by
    intro k m
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg _)]
    have h1 := hss k m
    have h2 : s k * s m * (|d k| * |d m|) ≤ (s k ^ 2 * d k ^ 2 + s m ^ 2 * d m ^ 2) / 2 := by
      nlinarith [sq_nonneg (s k * |d k| - s m * |d m|), sq_abs (d k), sq_abs (d m)]
    have hdd : 0 ≤ |d k| * |d m| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have hE : 0 ≤ ε ^ 2 * P k m := mul_nonneg (sq_nonneg _) (hP k m)
    calc (s k - s m) ^ 2 * |B k m| * |d k| * |d m|
        = (s k - s m) ^ 2 * |B k m| * (|d k| * |d m|) := by ring
      _ ≤ ε ^ 2 * P k m * (s k * s m) * (|d k| * |d m|) :=
        mul_le_mul_of_nonneg_right h1 hdd
      _ = ε ^ 2 * P k m * (s k * s m * (|d k| * |d m|)) := by ring
      _ ≤ ε ^ 2 * P k m * ((s k ^ 2 * d k ^ 2 + s m ^ 2 * d m ^ 2) / 2) :=
        mul_le_mul_of_nonneg_left h2 hE
      _ = ε ^ 2 / 2 * P k m * (s k ^ 2 * d k ^ 2 + s m ^ 2 * d m ^ 2) := by ring
  have hswap : ∑ k ∈ W, ∑ m ∈ W, P k m * (s m ^ 2 * d m ^ 2) =
      ∑ k ∈ W, ∑ m ∈ W, P k m * (s k ^ 2 * d k ^ 2) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun m hm => ?_
    rw [hPsym m hm k hk]
  have hrow' : ∑ k ∈ W, ∑ m ∈ W, P k m * (s k ^ 2 * d k ^ 2) ≤
      S * ∑ k ∈ W, s k ^ 2 * d k ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => ?_
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hrow k hk) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have habs : |∑ k ∈ W, ∑ m ∈ W, (s k - s m) ^ 2 * B k m * d k * d m| ≤
      ε ^ 2 * S * ∑ k ∈ W, s k ^ 2 * d k ^ 2 := by
    calc |∑ k ∈ W, ∑ m ∈ W, (s k - s m) ^ 2 * B k m * d k * d m|
        ≤ ∑ k ∈ W, |∑ m ∈ W, (s k - s m) ^ 2 * B k m * d k * d m| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ W, ∑ m ∈ W, |(s k - s m) ^ 2 * B k m * d k * d m| :=
          Finset.sum_le_sum fun k _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ W, ∑ m ∈ W, ε ^ 2 / 2 * P k m * (s k ^ 2 * d k ^ 2 + s m ^ 2 * d m ^ 2) :=
          Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun m _ => hterm k m
      _ = ε ^ 2 / 2 * (∑ k ∈ W, ∑ m ∈ W, P k m * (s k ^ 2 * d k ^ 2) +
            ∑ k ∈ W, ∑ m ∈ W, P k m * (s m ^ 2 * d m ^ 2)) := by
          simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => ?_
          ring
      _ = ε ^ 2 * ∑ k ∈ W, ∑ m ∈ W, P k m * (s k ^ 2 * d k ^ 2) := by rw [hswap]; ring
      _ ≤ ε ^ 2 * (S * ∑ k ∈ W, s k ^ 2 * d k ^ 2) :=
          mul_le_mul_of_nonneg_left hrow' (sq_nonneg ε)
      _ = ε ^ 2 * S * ∑ k ∈ W, s k ^ 2 * d k ^ 2 := by ring
  have := neg_abs_le (∑ k ∈ W, ∑ m ∈ W, (s k - s m) ^ 2 * B k m * d k * d m)
  linarith

theorem weighted_coercivity_general (W : Finset ℤ) (s : ℤ → ℝ) {ε : ℝ} (P : ℤ → ℤ → ℝ)
    (B : ℤ → ℤ → ℝ) (d h μ : ℤ → ℝ) {μ₀ S : ℝ}
    (hsym : ∀ k ∈ W, ∀ m ∈ W, B k m = B m k)
    (hpsd : ∀ x : ℤ → ℝ, 0 ≤ ∑ k ∈ W, ∑ m ∈ W, B k m * x k * x m)
    (hss : ∀ k m : ℤ, (s k - s m) ^ 2 * |B k m| ≤ ε ^ 2 * P k m * (s k * s m))
    (hP : ∀ k m, 0 ≤ P k m)
    (hPsym : ∀ k ∈ W, ∀ m ∈ W, P k m = P m k)
    (hrow : ∀ k ∈ W, ∑ m ∈ W, P k m ≤ S)
    (hμ : ∀ k ∈ W, μ₀ ≤ μ k)
    (hh : ∀ k ∈ W, h k = ∑ m ∈ W, B k m * d m + μ k * d k)
    (hsmall : ε ^ 2 * S ≤ μ₀) :
    μ₀ / 2 * ∑ k ∈ W, s k ^ 2 * d k ^ 2 ≤ ∑ k ∈ W, s k ^ 2 * d k * h k := by
  have hsplit := quad_split W B s d hsym
  have hcorr := correction_lower_general W B s d ε S P hsym hss hP hPsym hrow
  have hpos := hpsd (fun k => s k * d k)
  have hexp : ∑ k ∈ W, s k ^ 2 * d k * h k =
      ∑ k ∈ W, s k ^ 2 * d k * ∑ m ∈ W, B k m * d m +
        ∑ k ∈ W, μ k * (s k ^ 2 * d k ^ 2) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [hh k hk]; ring
  have hdiag : μ₀ * ∑ k ∈ W, s k ^ 2 * d k ^ 2 ≤ ∑ k ∈ W, μ k * (s k ^ 2 * d k ^ 2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun k hk =>
      mul_le_mul_of_nonneg_right (hμ k hk) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hX : 0 ≤ ∑ k ∈ W, s k ^ 2 * d k ^ 2 :=
    Finset.sum_nonneg fun k _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  rw [hexp, hsplit]
  nlinarith


/-- The last energy step at arbitrary order, derived from the generic
weighted coercivity rather than assumed as a squared central estimate. -/
theorem centre_energy (W : Finset ℤ) (j : ℤ) (hj : j ∈ W)
    (s d h μ : ℤ → ℝ) (hsj : s j = 1) (B P : ℤ → ℤ → ℝ)
    {ε S μ₀ : ℝ} (hμ₀ : 0 < μ₀)
    (hsym : ∀ k ∈ W, ∀ m ∈ W, B k m = B m k)
    (hpsd : ∀ x : ℤ → ℝ, 0 ≤ ∑ k ∈ W, ∑ m ∈ W, B k m*x k*x m)
    (hss : ∀ k m, (s k-s m)^2*|B k m| ≤ ε^2*P k m*(s k*s m))
    (hP : ∀ k m, 0 ≤ P k m)
    (hPsym : ∀ k ∈ W, ∀ m ∈ W, P k m = P m k)
    (hrow : ∀ k ∈ W, ∑ m ∈ W, P k m ≤ S)
    (hμ : ∀ k ∈ W, μ₀ ≤ μ k)
    (hh : ∀ k ∈ W, h k = ∑ m ∈ W, B k m*d m+μ k*d k)
    (hsmall : ε^2*S ≤ μ₀) :
    d j^2 ≤ 4/μ₀^2 * ∑ k ∈ W, s k^2*h k^2 := by
  have hc := weighted_coercivity_general W s P B d h μ hsym hpsd hss hP hPsym hrow hμ hh hsmall
  have he := energy_of_coercive W (fun k => s k^2) d h hμ₀ (fun k _ => sq_nonneg _) hc
  have hj' := Finset.single_le_sum (f := fun k => s k^2*d k^2)
    (fun k _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hj
  rw [hsj,one_pow,one_mul] at hj'
  exact hj'.trans he

end UniformLanczos.Rate516Weighted
#print axioms UniformLanczos.Rate516Weighted.pow_sub_one_bound
#print axioms UniformLanczos.Rate516Weighted.ratio_bound
#print axioms UniformLanczos.Rate516Weighted.ratio_bound_delta
#print axioms UniformLanczos.Rate516Weighted.weightRoot_self
#print axioms UniformLanczos.Rate516Weighted.weight_pair_ordered
#print axioms UniformLanczos.Rate516Weighted.weight_pair
#print axioms UniformLanczos.Rate516Weighted.weight_comparison
#print axioms UniformLanczos.Rate516Weighted.correction_lower_general
#print axioms UniformLanczos.Rate516Weighted.weighted_coercivity_general
#print axioms UniformLanczos.Rate516Weighted.centre_energy
