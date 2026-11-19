import Manuscript15.KrapivskyLuckLaplaceKernel

/-! M14/M15 Binet spectral expansion: the actual interchange of the
scalar Dirichlet resolvent series and Laplace integral. Classical Binet
(DLMF 5.9.10_2) is a separate identification with the Stirling remainder. -/

open MeasureTheory Set Real ArithmeticFunction
open scoped BigOperators

noncomputable section
namespace Manuscripts14And15.KrapivskyLuck

/-- Normalized spectral integrand with zero padding for both indices. -/
def spectralIntegrand (n k : ℕ) (t : ℝ) : ℝ :=
  if n = 0 ∨ k = 0 then 0 else
    (2 * (n : ℝ)) * laplaceIntegrand (n * k) ((n : ℝ) * t)

/-- The actual Dirichlet spectral denominator, including the normalization by n. -/
theorem spectralIntegrand_formula (n k : ℕ) (hn : n ≠ 0) (hk : k ≠ 0) (t : ℝ) :
    spectralIntegrand n k t =
      (2 / (n : ℝ)) * Real.exp (-(n : ℝ) * t) /
        (t^2 + 4 * Real.pi^2 * (k : ℝ)^2) := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hk' : 0 < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hd : 0 < t^2 + 4 * Real.pi^2 * (k : ℝ)^2 := by positivity
  have hd' : 0 < ((n : ℝ) * t)^2 + 4 * Real.pi^2 * ((n : ℝ) * (k : ℝ))^2 := by positivity
  simp only [spectralIntegrand, hn, hk, or_self, ite_false, laplaceIntegrand, Nat.cast_mul]
  rw [← neg_mul]
  field_simp [hn'.ne', hd.ne', hd'.ne'] <;> ring

theorem spectralIntegrand_nonneg (n k : ℕ) (t : ℝ) : 0 ≤ spectralIntegrand n k t := by
  unfold spectralIntegrand
  split
  · exact le_rfl
  · exact mul_nonneg (by positivity) (laplaceIntegrand_nonneg _ _)

theorem spectralIntegrand_integrable (n k : ℕ) :
    IntegrableOn (spectralIntegrand n k) (Ioi 0) := by
  by_cases hn : n = 0
  · have heq : spectralIntegrand n k = fun _ : ℝ => (0 : ℝ) := by
      funext t
      simp [spectralIntegrand, hn]
    rw [heq]
    simp [IntegrableOn]
  by_cases hk : k = 0
  · have heq : spectralIntegrand n k = fun _ : ℝ => (0 : ℝ) := by
      funext t
      simp [spectralIntegrand, hk]
    rw [heq]
    simp [IntegrableOn]
  have hn' : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have h := (laplaceIntegrand_integrable (n*k) (Nat.mul_ne_zero hn hk))
  have h' : IntegrableOn (fun t : ℝ => laplaceIntegrand (n*k) ((n : ℝ)*t)) (Ioi 0) :=
    (integrableOn_Ioi_comp_mul_left_iff (laplaceIntegrand (n*k)) 0 hn').2 (by simpa using h)
  have heq : spectralIntegrand n k = fun t : ℝ =>
      (2 * (n : ℝ)) * laplaceIntegrand (n*k) ((n : ℝ)*t) := by
    funext t
    simp [spectralIntegrand, hn, hk]
  rw [heq]
  exact h'.const_mul (2 * (n : ℝ))

/-- Substitution u=nt, with exact Jacobian. -/
theorem spectralIntegrand_integral (n k : ℕ) :
    (∫ t : ℝ in Ioi 0, spectralIntegrand n k t) = laplaceKernel (n*k) := by
  by_cases hn : n = 0
  · simp [spectralIntegrand, laplaceKernel, hn]
  by_cases hk : k = 0
  · simp [spectralIntegrand, laplaceKernel, hk]
  have hn' : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  simp only [spectralIntegrand, hn, hk, or_self, ite_false]
  rw [integral_const_mul, integral_comp_mul_left_Ioi _ _ hn']
  simp only [mul_zero, smul_eq_mul, laplaceKernel, Nat.mul_ne_zero hn hk, ite_false]
  field_simp [hn'.ne'] <;> ring

/-- The positive spectral row is summable, not merely assumed to be so. -/
theorem laplaceKernel_row_summable (n : ℕ) :
    Summable (fun k : ℕ => laplaceKernel (n*k)) := by
  have hs : Summable (fun k : ℕ => 1 / (k : ℝ)^2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  apply (hs.mul_left ((2 / (4 * Real.pi^2)) * (1 / (n : ℝ)^2))).of_norm_bounded
  intro k
  rw [Real.norm_eq_abs, abs_of_nonneg (laplaceKernel_nonneg _)]
  calc
    _ ≤ (2 / (4 * Real.pi^2)) * (1 / ((n*k : ℕ) : ℝ)^2) := laplaceKernel_bound _
    _ = _ := by
      rw [Nat.cast_mul]
      by_cases hn : (n : ℝ) = 0
      · simp [hn]
      by_cases hk : (k : ℝ) = 0
      · simp [hk]
      field_simp [Real.pi_ne_zero, hn, hk] <;> ring

/-- Actual absolute integral norm sum, needed for the Bochner Fubini theorem. -/
theorem spectralIntegrand_integral_norm_summable (n : ℕ) :
    Summable (fun k : ℕ => ∫ t : ℝ in Ioi 0, ‖spectralIntegrand n k t‖) := by
  simp_rw [Real.norm_eq_abs, abs_of_nonneg (spectralIntegrand_nonneg _ _ _),
    spectralIntegrand_integral]
  exact laplaceKernel_row_summable n

/-- The normalized scalar spectral remainder as an actual integral. -/
def normalizedSpectralRemainder (n : ℕ) : ℝ :=
  ∫ t : ℝ in Ioi 0, ∑' k : ℕ, spectralIntegrand n k t

/-- Unconditional exchange of the actual infinite spectral series and integral. -/
theorem normalizedSpectralRemainder_eq (n : ℕ) :
    normalizedSpectralRemainder n = ∑' k : ℕ, laplaceKernel (n*k) := by
  unfold normalizedSpectralRemainder
  have h := integral_tsum_of_summable_integral_norm
    (spectralIntegrand_integrable n) (spectralIntegrand_integral_norm_summable n)
  rw [← h]
  simp only [spectralIntegrand_integral]

/-- Actual normalized spectral expression, before the independent Binet identification. -/
theorem normalizedSpectralRemainder_formula (n : ℕ) (hn : n ≠ 0) :
    normalizedSpectralRemainder n =
      ∫ t : ℝ in Ioi 0, ∑' k : ℕ,
        if k = 0 then 0 else
          (2 / (n : ℝ)) * Real.exp (-(n : ℝ) * t) /
            (t^2 + 4 * Real.pi^2 * (k : ℝ)^2) := by
  unfold normalizedSpectralRemainder
  congr 1
  funext t
  apply tsum_congr
  intro k
  by_cases hk : k = 0
  · simp [spectralIntegrand, hk]
  · simpa [hk] using spectralIntegrand_formula n k hn hk t

/-- The Möbius sum of the normalized spectral remainders, with no summability assumption. -/
theorem normalizedSpectralRemainder_mobius :
    (∑' n : ℕ, (↑(moebius n) : ℝ) * normalizedSpectralRemainder n) =
      2 * ∫ u : ℝ in Ioi 0, Real.exp (-u) / (u^2 + 4 * Real.pi^2) := by
  simp_rw [normalizedSpectralRemainder_eq, ← tsum_mul_left]
  rw [← laplaceKernel_abs_summable.of_norm.tsum_prod]
  exact laplaceKernel_mobius_cancellation

end Manuscripts14And15.KrapivskyLuck

#print axioms Manuscripts14And15.KrapivskyLuck.spectralIntegrand_formula
#print axioms Manuscripts14And15.KrapivskyLuck.spectralIntegrand_nonneg
#print axioms Manuscripts14And15.KrapivskyLuck.spectralIntegrand_integrable
#print axioms Manuscripts14And15.KrapivskyLuck.spectralIntegrand_integral
#print axioms Manuscripts14And15.KrapivskyLuck.laplaceKernel_row_summable
#print axioms Manuscripts14And15.KrapivskyLuck.spectralIntegrand_integral_norm_summable
#print axioms Manuscripts14And15.KrapivskyLuck.normalizedSpectralRemainder_eq
#print axioms Manuscripts14And15.KrapivskyLuck.normalizedSpectralRemainder_formula
#print axioms Manuscripts14And15.KrapivskyLuck.normalizedSpectralRemainder_mobius
