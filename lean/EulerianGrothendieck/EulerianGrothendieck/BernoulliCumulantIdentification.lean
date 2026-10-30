import EulerianGrothendieck.CumulantBounds
import Mathlib.NumberTheory.Bernoulli

/-! # Task F, part 1: uniform cumulants are Bernoulli numbers, at every order

Convention check.  `V033.UniformSum.evenEGF = ∑_r E U^{2r}/(2r)! · y^r` (with `y = s²`),
`cumulantSeries = evenEGF'/evenEGF` (logarithmic derivative in `y`), and
`standardUniformCumulant n = 12^{n+1} · coeff_n(cumulantSeries)`.  With
`log E(12 y) = ∑_{j ≥ 1} a_j y^j`, the logarithmic derivative gives
`standardUniformCumulant (j-1) = j a_j`.

Main results:
* `cumulantCoefficient_bernoulli`: `coeff_n(cumulantSeries) = B_{2n+2}/(2(2n+2)!)`;
* `standardUniformCumulant_bernoulli`:
  `standardUniformCumulant n = 3^{n+1} 2^{2n+1} B_{2n+2}/(2n+2)!`;
* `uniformLogCoefficient` `a_j := 3^j 2^{2j-1} B_{2j}/(j (2j)!)` and
  `standardUniformCumulant_eq_mul_logCoefficient`: `standardUniformCumulant (j-1) = j a_j`.

The proof: `G = e^x · 2x/(e^{2x}-1)` satisfies `G · (e^x - e^{-x}) = 2x`; this forces `G` to be
even, so `∑_m binom(N,m) 2^m B_m = 0` for odd `N`, which is exactly the coefficient identity
`C · evenEGF = evenEGF'` for `C = ∑ B_{2n+2}/(2(2n+2)!) yⁿ`; `C = cumulantSeries` since
`evenEGF` is invertible. -/

noncomputable section
open scoped BigOperators Nat
open PowerSeries Finset
namespace EulerianGrothendieck

/-- The real Bernoulli power series `∑ B_n xⁿ/n!` (`B₁ = -1/2`). -/
def realBernoulliSeries : PowerSeries ℝ := bernoulliPowerSeries ℝ

theorem coeff_realBernoulliSeries (n : ℕ) :
    coeff n realBernoulliSeries = (bernoulli n : ℝ) / (n ! : ℝ) := by
  simp [realBernoulliSeries, bernoulliPowerSeries, coeff_mk]

theorem rescale_C' (a r : ℝ) : rescale a (C r) = C r := by
  ext n
  rw [coeff_rescale, coeff_C]
  split_ifs with h <;> simp [h]

/-- `G = e^x · β(2x)`. -/
def evenBernoulliSeries : PowerSeries ℝ := exp ℝ * rescale (2:ℝ) realBernoulliSeries

/-- `S = e^x - e^{-x}`. -/
def sinhSeries : PowerSeries ℝ := exp ℝ - rescale (-1:ℝ) (exp ℝ)

theorem rescale_two_exp_sub_one :
    rescale (2:ℝ) (exp ℝ) - 1 = exp ℝ * sinhSeries := by
  have h1 := exp_mul_exp_eq_exp_add (A := ℝ) 1 1
  have h2 := exp_mul_exp_eq_exp_add (A := ℝ) 1 (-1)
  rw [rescale_one] at h1 h2
  simp only [RingHom.id_apply] at h1 h2
  rw [show (1:ℝ) + 1 = 2 by norm_num] at h1
  rw [show (1:ℝ) + -1 = 0 by norm_num, rescale_zero] at h2
  simp only [RingHom.coe_comp, Function.comp_apply, constantCoeff_exp, map_one] at h2
  rw [sinhSeries, mul_sub, h2, ← h1]

theorem evenBernoulli_mul_sinh : evenBernoulliSeries * sinhSeries = C (2:ℝ) * X := by
  have h := congrArg (rescale (2:ℝ)) (bernoulliPowerSeries_mul_exp_sub_one ℝ)
  rw [map_mul, map_sub, map_one, rescale_X] at h
  rw [evenBernoulliSeries, mul_comm (exp ℝ), mul_assoc, ← rescale_two_exp_sub_one]
  exact h

theorem sinhSeries_ne_zero : sinhSeries ≠ 0 := by
  intro h
  have := congrArg (coeff 1) h
  norm_num [sinhSeries, coeff_rescale, coeff_exp] at this

theorem rescale_neg_sinh : rescale (-1:ℝ) sinhSeries = -sinhSeries := by
  rw [sinhSeries, map_sub, rescale_rescale, show (-1:ℝ) * -1 = 1 by norm_num, rescale_one,
    RingHom.id_apply]
  ring

theorem evenBernoulli_even : rescale (-1:ℝ) evenBernoulliSeries = evenBernoulliSeries := by
  have h := congrArg (rescale (-1:ℝ)) evenBernoulli_mul_sinh
  rw [map_mul, rescale_neg_sinh, map_mul, rescale_C', rescale_neg_one_X] at h
  have h2 : (rescale (-1:ℝ) evenBernoulliSeries - evenBernoulliSeries) * sinhSeries = 0 := by
    rw [sub_mul, evenBernoulli_mul_sinh]
    linear_combination -h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact sub_eq_zero.mp h3
  · exact absurd h3 sinhSeries_ne_zero

theorem coeff_evenBernoulli (N : ℕ) :
    coeff N evenBernoulliSeries =
      ∑ m ∈ range (N+1), (2:ℝ) ^ m * (bernoulli m : ℝ) / ((m ! : ℝ) * ((N - m) ! : ℝ)) := by
  rw [evenBernoulliSeries, coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => coeff i (exp ℝ) * coeff j (rescale (2:ℝ) realBernoulliSeries)) N]
  rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro m hm
  have hmN : m ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  rw [show N + 1 - 1 - m = N - m by omega, show N - (N - m) = m by omega]
  rw [coeff_exp, coeff_rescale, coeff_realBernoulliSeries]
  simp only [one_div, map_inv₀, map_natCast]
  have h1 : ((N - m) ! : ℝ) ≠ 0 := by positivity
  have h2 : (m ! : ℝ) ≠ 0 := by positivity
  field_simp <;> ring

/-- **`∑_{m ≤ N} 2^m B_m /(m!(N-m)!) = 0` for odd `N`.** -/
theorem odd_bernoulli_identity (N : ℕ) (hN : Odd N) :
    ∑ m ∈ range (N+1), (2:ℝ) ^ m * (bernoulli m : ℝ) / ((m ! : ℝ) * ((N - m) ! : ℝ)) = 0 := by
  rw [← coeff_evenBernoulli]
  have h := congrArg (coeff N) evenBernoulli_even
  rw [coeff_rescale, hN.neg_one_pow] at h
  linarith

theorem bernoulli_odd_zero (n : ℕ) (hodd : Odd n) (hn : 1 < n) : bernoulli n = 0 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by omega), bernoulli'_odd_eq_zero hodd hn]

theorem sum_range_two_mul (f : ℕ → ℝ) (n : ℕ) :
    ∑ m ∈ range (2 * n), f m = ∑ k ∈ range n, (f (2 * k) + f (2 * k + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n+1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    ring

/-- The even-index Bernoulli sum extracted from the odd identity at `N = 2r+3`. -/
theorem even_bernoulli_sum (r : ℕ) :
    ∑ k ∈ range (r+1), (4:ℝ) ^ (k+1) * (bernoulli (2*k+2) : ℝ) /
        (((2*k+2) ! : ℝ) * ((2*r+1-2*k) ! : ℝ)) =
      (2*r+2 : ℝ) / ((2*r+3) ! : ℝ) := by
  have hodd := odd_bernoulli_identity (2*r+3) ⟨r+1, by ring⟩
  set f : ℕ → ℝ := fun m => (2:ℝ) ^ m * (bernoulli m : ℝ) / ((m ! : ℝ) * ((2*r+3 - m) ! : ℝ))
    with hf
  have hsum : ∑ m ∈ range (2*r+3+1), f m = 0 := hodd
  rw [show 2*r+3+1 = 2*(r+1+1) by ring, sum_range_two_mul, Finset.sum_add_distrib,
    Finset.sum_range_succ' (fun k => f (2*k)) (r+1),
    Finset.sum_range_succ' (fun k => f (2*k+1)) (r+1)] at hsum
  have hoddzero : ∑ k ∈ range (r+1), f (2*(k+1)+1) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    simp only [hf]
    rw [bernoulli_odd_zero _ ⟨k+1, by ring⟩ (by omega)]
    simp
  have hf0 : f (2*0) = 1 / ((2*r+3) ! : ℝ) := by
    simp only [hf]
    simp
  have hf1 : f (2*0+1) = -1 / ((2*r+2) ! : ℝ) := by
    simp only [hf]
    rw [show 2*0+1 = 1 by rfl, bernoulli_one, show 2*r+3-1 = 2*r+2 by omega]
    simp
    ring
  have hsame : ∑ k ∈ range (r+1), f (2*(k+1)) =
      ∑ k ∈ range (r+1), (4:ℝ) ^ (k+1) * (bernoulli (2*k+2) : ℝ) /
        (((2*k+2) ! : ℝ) * ((2*r+1-2*k) ! : ℝ)) := by
    apply Finset.sum_congr rfl
    intro k _
    simp only [hf]
    rw [show 2*(k+1) = 2*k+2 by ring, show 2*r+3-(2*k+2) = 2*r+1-2*k by omega,
      show (2:ℝ) ^ (2*k+2) = 4 ^ (k+1) by
        rw [show 2*k+2 = 2*(k+1) by ring, pow_mul]; norm_num]
  rw [hoddzero, hf0, hf1, hsame] at hsum
  have hfac : ((2*r+3) ! : ℝ) = (2*r+3) * ((2*r+2) ! : ℝ) := by
    rw [show 2*r+3 = (2*r+2)+1 by ring, Nat.factorial_succ]; push_cast; ring
  have hpos : (0:ℝ) < ((2*r+2) ! : ℝ) := by positivity
  have e : (1:ℝ) / ((2*r+3) ! : ℝ) + (0 + -1 / ((2*r+2) ! : ℝ)) = -((2*r+2 : ℝ) / ((2*r+3) ! : ℝ)) := by
    rw [hfac]
    field_simp <;> ring
  linarith

/-- The candidate logarithmic-derivative coefficients `B_{2n+2}/(2(2n+2)!)`. -/
def bernoulliCumulant (n : ℕ) : ℝ := (bernoulli (2*n+2) : ℝ) / (2 * ((2*n+2) ! : ℝ))

theorem evenEGF_coeff_closed (r : ℕ) :
    coeff r V033.UniformSum.evenEGF = 1 / ((4:ℝ) ^ r * ((2*r+1) ! : ℝ)) := by
  rw [V033.UniformSum.evenEGF_coeff, V033.UniformSum.singleMoment_even,
    Nat.factorial_succ]
  push_cast
  have h1 : ((2*r) ! : ℝ) ≠ 0 := by positivity
  field_simp

/-- The coefficient identity `∑_{k ≤ r} C_k E_{r-k} = (r+1) E_{r+1}`. -/
theorem bernoulliCumulant_convolution (r : ℕ) :
    ∑ k ∈ range (r+1), bernoulliCumulant k * coeff (r - k) V033.UniformSum.evenEGF =
      (r + 1 : ℝ) * coeff (r+1) V033.UniformSum.evenEGF := by
  have hterm : ∀ k ∈ range (r+1),
      bernoulliCumulant k * coeff (r - k) V033.UniformSum.evenEGF =
        ((4:ℝ) ^ (k+1) * (bernoulli (2*k+2) : ℝ) / (((2*k+2) ! : ℝ) * ((2*r+1-2*k) ! : ℝ))) /
          (2 * 4 ^ (r+1)) := by
    intro k hk
    have hkr : k ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [bernoulliCumulant, evenEGF_coeff_closed, show 2*(r-k)+1 = 2*r+1-2*k by omega,
      show (4:ℝ) ^ (r+1) = 4 ^ (r-k) * 4 ^ (k+1) by rw [← pow_add]; congr 1; omega]
    have h1 : ((2*k+2) ! : ℝ) ≠ 0 := by positivity
    have h2 : ((2*r+1-2*k) ! : ℝ) ≠ 0 := by positivity
    have h3 : (4:ℝ) ^ (r-k) ≠ 0 := by positivity
    have h4 : (4:ℝ) ^ (k+1) ≠ 0 := by positivity
    field_simp <;> ring
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, even_bernoulli_sum, evenEGF_coeff_closed,
    show 2*(r+1)+1 = 2*r+3 by ring]
  have h1 : ((2*r+3) ! : ℝ) ≠ 0 := by positivity
  have h2 : (4:ℝ) ^ (r+1) ≠ 0 := by positivity
  field_simp <;> ring

/-- **`coeff_n(cumulantSeries) = B_{2n+2}/(2(2n+2)!)`** for every `n`. -/
theorem cumulantCoefficient_bernoulli (n : ℕ) :
    V033.UniformSum.cumulantCoefficient n = bernoulliCumulant n := by
  have hC : PowerSeries.mk bernoulliCumulant * V033.UniformSum.evenEGF =
      derivative ℝ V033.UniformSum.evenEGF := by
    ext r
    rw [coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => coeff i (PowerSeries.mk bernoulliCumulant) * coeff j V033.UniformSum.evenEGF) r,
      coeff_derivative]
    simp only [coeff_mk]
    rw [bernoulliCumulant_convolution]
    ring
  have hE : V033.UniformSum.evenEGF ≠ 0 := by
    intro h
    have := V033.UniformSum.evenEGF_constant
    rw [h] at this
    simp at this
  have heq : PowerSeries.mk bernoulliCumulant = V033.UniformSum.cumulantSeries := by
    have h2 := V033.UniformSum.cumulant_identity
    rw [← h2] at hC
    exact mul_right_cancel₀ hE hC
  unfold V033.UniformSum.cumulantCoefficient
  rw [← heq, coeff_mk]

/-- **`standardUniformCumulant n = 3^{n+1} 2^{2n+1} B_{2n+2}/(2n+2)!`** for every `n`. -/
theorem standardUniformCumulant_bernoulli (n : ℕ) :
    standardUniformCumulant n =
      (3:ℝ) ^ (n+1) * 2 ^ (2*n+1) * (bernoulli (2*n+2) : ℝ) / ((2*n+2) ! : ℝ) := by
  rw [standardUniformCumulant, cumulantCoefficient_bernoulli, bernoulliCumulant]
  have h4 : (4:ℝ) ^ (n+1) = 2 ^ (2*n+1) * 2 := by
    rw [← pow_succ, show (4:ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
    first | done | (congr 1 <;> omega)
  have h12 : (12:ℝ) ^ (n+1) = 3 ^ (n+1) * 2 ^ (2*n+1) * 2 := by
    rw [show (12:ℝ) = 3 * 4 by norm_num, mul_pow, h4]
    ring
  rw [h12]
  have h1 : ((2*n+2) ! : ℝ) ≠ 0 := by positivity
  field_simp <;> ring

/-- The coefficients `a_j = 3^j 2^{2j-1} B_{2j}/(j (2j)!)` of the manuscript. -/
def uniformLogCoefficient (j : ℕ) : ℝ :=
  (3:ℝ) ^ j * 2 ^ (2*j-1) * (bernoulli (2*j) : ℝ) / (j * ((2*j) ! : ℝ))

/-- **The link of the manuscript's convention**: `standardUniformCumulant (j-1) = j a_j`. -/
theorem standardUniformCumulant_eq_mul_logCoefficient (j : ℕ) (hj : 1 ≤ j) :
    standardUniformCumulant (j-1) = j * uniformLogCoefficient j := by
  obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
  rw [show n + 1 - 1 = n by omega, standardUniformCumulant_bernoulli, uniformLogCoefficient,
    show 2*(n+1) = 2*n+2 by ring, show 2*n+2-1 = 2*n+1 by omega]
  have h0 : ((n+1 : ℕ) : ℝ) ≠ 0 := by positivity
  have h1 : ((2*n+2) ! : ℝ) ≠ 0 := by positivity
  field_simp

theorem uniformLogCoefficient_two : uniformLogCoefficient 2 = -1/20 := by
  have h := standardUniformCumulant_eq_mul_logCoefficient 2 (by norm_num)
  rw [show 2 - 1 = 1 by rfl, standardUniformCumulant_one] at h
  push_cast at h
  linarith

end EulerianGrothendieck
