/-
Manuscript 15 — genuine punctured-neighbourhood limit of the cusp
quotient, conditional only on the two precise characteristic-function
asymptotic inputs. This is a Filter.Tendsto proof, not merely a
rational-expression simplification.

The remaining probabilistic lemma is to establish the normalized
second-order characteristic-function expansion from finite variance.
-/
import Mathlib

open Filter Topology
noncomputable section
namespace Manuscript15

def cuspX (a : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  a * t * (1 - f (2 * t))

def cuspY (a : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  a * t ^ 2 / 2 * (f t) ^ 2

def cuspQ (a : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  (cuspX a f t) ^ 2 / (cuspY a f t) ^ 3

/-- Exact factorisation of the quotient for any nonzero scale,
    nonzero parameter and nonvanishing characteristic value. -/
theorem cusp_quotient_factorization
    (a t : ℝ) (f : ℝ → ℝ)
    (ha : a ≠ 0) (ht : t ≠ 0) (hf : f t ≠ 0) :
    cuspQ a f t =
      (8 / a) * (((1 - f (2 * t)) / t ^ 2) ^ 2 / (f t) ^ 6) := by
  unfold cuspQ cuspX cuspY
  field_simp [ha, ht, hf]
  <;> ring

/-- The full cusp quotient limit follows from the true real
    second-moment characteristic asymptotics. The hypotheses are
    explicit rather than an unproved implicit measure-theoretic step. -/
theorem cusp_quotient_tendsto
    (a sigma2 : ℝ) (f : ℝ → ℝ)
    (ha : a ≠ 0)
    (hsecond :
      Tendsto (fun t : ℝ => (1 - f (2 * t)) / t ^ 2)
        (nhdsWithin 0 ({0}ᶜ)) (𝓝 (2 * sigma2)))
    (hzero :
      Tendsto f (nhdsWithin 0 ({0}ᶜ)) (𝓝 1)) :
    Tendsto (cuspQ a f)
      (nhdsWithin 0 ({0}ᶜ))
      (𝓝 (32 * sigma2 ^ 2 / a)) := by
  let L := nhdsWithin (0 : ℝ) ({0}ᶜ)
  have hpow : Tendsto
      (fun t : ℝ => ((1 - f (2 * t)) / t ^ 2) ^ 2)
      L (𝓝 ((2 * sigma2) ^ 2)) := hsecond.pow 2
  have hf6 : Tendsto (fun t : ℝ => (f t) ^ 6)
      L (𝓝 ((1 : ℝ) ^ 6)) := hzero.pow 6
  have hdiv : Tendsto
      (fun t : ℝ =>
        (8 / a) * (((1 - f (2 * t)) / t ^ 2) ^ 2 / (f t) ^ 6))
      L
      (𝓝 ((8 / a) * (((2 * sigma2) ^ 2) / ((1 : ℝ) ^ 6)))) :=
    tendsto_const_nhds.mul (hpow.div hf6 (by norm_num))
  have hnonzero_t : ∀ᶠ t : ℝ in L, t ≠ 0 := by
    change ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) ({0}ᶜ), t ≠ 0
    filter_upwards [self_mem_nhdsWithin] with t ht
    simpa using ht
  have hnonzero_f : ∀ᶠ t : ℝ in L, f t ≠ 0 :=
    hzero.eventually_ne (by norm_num : (1 : ℝ) ≠ 0)
  have hcongr : (cuspQ a f) =ᶠ[L]
      (fun t : ℝ =>
        (8 / a) * (((1 - f (2 * t)) / t ^ 2) ^ 2 / (f t) ^ 6)) := by
    filter_upwards [hnonzero_t, hnonzero_f] with t ht hf
    exact cusp_quotient_factorization a t f ha ht hf
  have hlim := hdiv.congr' hcongr.symm
  convert hlim using 1 <;> ring

#print axioms Manuscript15.cusp_quotient_factorization
#print axioms Manuscript15.cusp_quotient_tendsto

end Manuscript15
