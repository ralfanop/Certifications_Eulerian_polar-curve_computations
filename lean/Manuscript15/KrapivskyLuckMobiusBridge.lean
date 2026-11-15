import Mathlib

/-!
# Shared Möbius regrouping for Manuscripts 14 and 15

The analytic Binet / Laplace kernel identity is a separate obligation.
Here we prove the divisor cancellation and the infinite regrouping for an
actually summable double family. Zero indices are padded with K 0 = 0.
-/

open scoped BigOperators
open ArithmeticFunction

namespace Manuscripts14And15.KrapivskyLuck

/-- The Möbius coefficients on a positive multiplicative fibre sum to a delta. -/
theorem mobius_fibre_delta (m : ℕ) (hm : 0 < m) :
    (∑ p ∈ m.divisorsAntidiagonal, (↑(moebius p.1) : ℝ)) =
      if m = 1 then 1 else 0 := by
  classical
  have h := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := fun n : ℕ => if n = 1 then (1 : ℝ) else 0)
    (g := fun _ : ℕ => (1 : ℝ))).mp (by
      intro n hn
      rw [Finset.sum_eq_single 1]
      · simp
      · intro b _ hb
        simp [hb]
      · intro hnot
        exact (hnot (Nat.mem_divisors.mpr ⟨one_dvd n, ne_of_gt hn⟩)).elim) m hm
  simpa using h

/-- Cancellation of an arbitrary real kernel on a positive multiplicative fibre. -/
theorem weighted_fibre_delta (K : ℕ → ℝ) (m : ℕ) (hm : 0 < m) :
    (∑ p ∈ m.divisorsAntidiagonal,
      (↑(moebius p.1) : ℝ) * K (p.1 * p.2)) =
      if m = 1 then K 1 else 0 := by
  classical
  calc
    _ = ∑ p ∈ m.divisorsAntidiagonal, (↑(moebius p.1) : ℝ) * K m := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [(Nat.mem_divisorsAntidiagonal.mp hp).1]
    _ = (∑ p ∈ m.divisorsAntidiagonal, (↑(moebius p.1) : ℝ)) * K m := by
      rw [Finset.sum_mul]
    _ = _ := by
      rw [mobius_fibre_delta m hm]
      by_cases h : m = 1 <;> simp [h]

/-- The actual (possibly infinite) multiplicative fibre, including zero padding. -/
theorem fibre_tsum_delta (K : ℕ → ℝ) (hK : K 0 = 0) (m : ℕ) :
    (∑' p : (fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' ({m} : Set ℕ),
      (↑(moebius p.val.1) : ℝ) * K (p.val.1 * p.val.2)) =
      if m = 1 then K 1 else 0 := by
  classical
  by_cases hm : m = 0
  · subst m
    have hz (p : (fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' ({0} : Set ℕ)) :
        p.val.1 * p.val.2 = 0 := p.property
    simp [hz, hK]
  · have heq : (fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' ({m} : Set ℕ) =
        (↑m.divisorsAntidiagonal : Set (ℕ × ℕ)) := by
      ext p
      simp [Nat.mem_divisorsAntidiagonal, hm]
    rw [heq]
    change (∑' p : ↥m.divisorsAntidiagonal,
        (↑(moebius p.val.1) : ℝ) * K (p.val.1 * p.val.2)) = _
    rw [tsum_fintype, Finset.sum_finset_coe]
    exact weighted_fibre_delta K m (Nat.pos_of_ne_zero hm)

/-- Infinite Möbius cancellation. Summability is an explicit analytic obligation,
not an axiom, and the result uses the unconditional sum over all pairs. -/
theorem mobius_kernel_tsum (K : ℕ → ℝ) (hK : K 0 = 0)
    (h : Summable (fun p : ℕ × ℕ => (↑(moebius p.1) : ℝ) * K (p.1 * p.2))) :
    (∑' p : ℕ × ℕ, (↑(moebius p.1) : ℝ) * K (p.1 * p.2)) = K 1 := by
  classical
  have hf := h.hasSum.tsum_fiberwise (fun p : ℕ × ℕ => p.1 * p.2)
  have hd := hf.tsum_eq
  rw [← hd]
  simp_rw [fibre_tsum_delta K hK]
  rw [tsum_eq_single 1]
  intro n hn
  simp [hn]

/-- Pointwise trig reduction underpinning M15's sine-integral energy formula. -/
theorem sinc_square_kernel (t : ℝ) (ht : t ≠ 0) :
    (Real.sin (t / 2) / (t / 2)) ^ 2 =
      2 * (1 - Real.cos t) / t ^ 2 := by
  have hc := Real.cos_two_mul (t / 2)
  rw [show 2 * (t / 2) = t by ring] at hc
  have hs := Real.sin_sq_add_cos_sq (t / 2)
  field_simp
  nlinarith

end Manuscripts14And15.KrapivskyLuck

#print axioms Manuscripts14And15.KrapivskyLuck.mobius_fibre_delta
#print axioms Manuscripts14And15.KrapivskyLuck.weighted_fibre_delta
#print axioms Manuscripts14And15.KrapivskyLuck.fibre_tsum_delta
#print axioms Manuscripts14And15.KrapivskyLuck.mobius_kernel_tsum
#print axioms Manuscripts14And15.KrapivskyLuck.sinc_square_kernel
