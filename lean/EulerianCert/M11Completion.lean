import EulerianCert.FourierSeries
import EulerianCert.Bracket
import EulerianCert.M11OddFinite
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-!
# Manuscript 11: outstanding exact Lean 4 checks

Source: author-supplied `Manuscript_11_20261123_Eq33_24decimali(2).zip`,
`11/11.tex`, Proposition 3.4 and Remark 3.16.

This file contains ONLY mathematical claims stated in that source. No
numerical FLINT/Arb work, no reproof of classical Plancherel/Pythagoras.
All finite certificates use kernel `decide`, never `native_decide`.
-/

open Real Set Finset
open EulerianCert
open EulerianCert.FourierSeries
open EulerianCert.Bracket
open EulerianCert.FourierModes

noncomputable section
namespace EulerianCert.M11Completion

private def gap (n : ℕ) (θ : ℝ) : ℝ :=
  (-1 : ℝ) ^ n * cE n * Real.cos ((n + 1 : ℝ) * θ) + cE n

private lemma gap_nonneg (n : ℕ) (θ : ℝ) : 0 ≤ gap n θ := by
  unfold gap
  have h := EulerianCert.term_ge cE_nonneg n θ
  linarith

private lemma gap_sum (N : ℕ) (θ : ℝ) :
    S N θ - S N π = ∑ n ∈ Finset.range N, gap n θ := by
  calc
    S N θ - S N π =
        ∑ n ∈ Finset.range N,
          (A (n + 1) * Real.cos ((n + 1 : ℕ) * θ) -
           A (n + 1) * Real.cos ((n + 1 : ℕ) * π)) := by
      simp only [S]
      rw [Finset.sum_sub_distrib]
      ring
    _ = ∑ n ∈ Finset.range N, gap n θ := by
      apply Finset.sum_congr rfl
      intro n _
      simp only [A_succ_eq]
      push_cast
      have hp := (EulerianCert.term_pi (c := cE) n)
      dsimp [gap]
      rw [hp]
      ring

/-- Proposition 3.4: equality of a nonconstant Fourier truncation at the
endpoint minimum forces the first harmonic to attain its unique minimum. -/
theorem S_min_cos_unique (N : ℕ) (hN : 1 ≤ N) (θ : ℝ)
    (heq : S N θ = S N π) : Real.cos θ = -1 := by
  have hzero : (∑ n ∈ Finset.range N, gap n θ) = 0 := by
    rw [← gap_sum]
    linarith
  have hz : (0 : ℕ) ∈ Finset.range N := Finset.mem_range.mpr (by omega)
  have hle : gap 0 θ ≤ ∑ n ∈ Finset.range N, gap n θ :=
    Finset.single_le_sum (fun n _ => gap_nonneg n θ) hz
  have hfirst : gap 0 θ = 0 := by
    have hp := gap_nonneg 0 θ
    linarith
  have hfactor : cE 0 * (1 + Real.cos θ) = 0 := by
    simp only [gap, pow_zero, one_mul, Nat.cast_zero, zero_add] at hfirst
    calc
      cE 0 * (1 + Real.cos θ) = cE 0 * Real.cos θ + cE 0 := by ring
      _ = 0 := by simpa [gap] using hfirst
  have hcos : 1 + Real.cos θ = 0 :=
    (mul_eq_zero.mp hfactor).resolve_left (ne_of_gt (cE_pos 0))
  linarith

/-- On the manuscript's closed angular interval the minimum occurs only at the endpoints. -/
theorem S_min_endpoint_unique (N : ℕ) (hN : 1 ≤ N) (θ : ℝ)
    (hθ : θ ∈ Set.Icc (-π) π) (heq : S N θ = S N π) :
    θ = -π ∨ θ = π := by
  have hc := S_min_cos_unique N hN θ heq
  rcases le_total 0 θ with hp | hn
  · right
    have h := Real.arccos_cos hp hθ.2
    rw [hc, Real.arccos_neg_one] at h
    exact h.symm
  · left
    have h := Real.arccos_cos (show 0 ≤ -θ by linarith) (show -θ ≤ π by linarith [hθ.1])
    rw [Real.cos_neg, hc, Real.arccos_neg_one] at h
    linarith

/-- Proposition 3.4: for N=0 the truncation is constant. -/
theorem S_zero_constant (θ : ℝ) : S 0 θ = S 0 π := by
  simp [S]

/-- Remark 3.16: the two exactly coincident initial central slopes. -/
theorem c3_c5_exact :
    cn 3 1 = (1 / 2 : ℝ) ∧ cn 5 2 = (1 / 2 : ℝ) := by
  have h30 : E 3 0 = 1 := by decide +kernel
  have h31 : E 3 1 = 4 := by decide +kernel
  have h51 : E 5 1 = 26 := by decide +kernel
  have h52 : E 5 2 = 66 := by decide +kernel
  constructor
  · norm_num [cn, h30, h31]
  · norm_num [cn, h51, h52]

/-- Remark 3.16: exact finite integer comparison for all successive odd
central slopes from n=5 to n=1001 (498 adjacent comparisons).
The cross-multiplied inequality eliminates factorials and is mathematically
equivalent to strict increase provided the two central differences are
positive (positivity is checked in this same proposition).
This is a *kernel* computation, not an Arb certificate. -/
theorem odd_central_finite_integer_certificate :
    ∀ j : Fin 498,
      let n : ℕ := 5 + 2 * (j : ℕ)
      let k : ℕ := 2 + (j : ℕ)
      E n (k - 1) < E n k ∧
      E (n + 2) k < E (n + 2) (k + 1) ∧
      (n + 3) * (E (n + 2) (k + 1) - E (n + 2) k) <
        (n + 2) * (n + 1) ^ 2 * (E n k - E n (k - 1)) := by
  intro j
  obtain ⟨h1, h2, hI⟩ := M11OddFinite.all_odd_steps j
  dsimp [M11OddFinite.oddStep, M11OddFinite.centralGap] at h1 h2 hI
  have hk : (5 + 2 * (j : ℕ) - 1) / 2 = 2 + (j : ℕ) := by omega
  have hk' : (5 + 2 * (j : ℕ) + 2 - 1) / 2 = 2 + (j : ℕ) + 1 := by omega
  rw [hk] at h1 hI
  rw [hk', Nat.add_sub_cancel] at h2 hI
  exact ⟨by omega, by omega, hI⟩

end EulerianCert.M11Completion
