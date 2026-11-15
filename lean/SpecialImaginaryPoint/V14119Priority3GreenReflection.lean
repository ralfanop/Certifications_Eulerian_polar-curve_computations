import Mathlib

/-!
# M14 §6: reflection splitting of the actual Dirichlet Green kernel

Alternative to Sobolev seam gluing (PR #284). The classical kernels for
the positive second derivative operator -d²/dt² are used explicitly.
The two interval integrals below are genuine Lebesgue interval integrals,
not finite spectral surrogates. Here f is a continuous real density;
extension to complex L² classes, weak derivatives and the unbounded
domain realization is still required.

References: A. Zettl, Sturm-Liouville Theory, AMS 2005, §4.11,
Theorem 4.11.1; M. A. Al-Gwaiz, Sturm–Liouville Theory and its
Applications, second ed. 2026, §2.4.1. Classical identities.
-/
noncomputable section
open MeasureTheory Set

namespace Manuscript14Priority3.GreenReflection

def K2 (s t : ℝ) : ℝ := min s t - s * t / 2
def KD (s t : ℝ) : ℝ := min s t - s * t
def KDN (s t : ℝ) : ℝ := min s t

theorem cross_kernel (s t : ℝ) (hs : s ≤ 1) (ht : t ≤ 1) :
    K2 s (2 - t) = s * t / 2 := by
  unfold K2
  rw [min_eq_left (by linarith : s ≤ 2 - t)]
  ring

theorem reflected_first (s t : ℝ) (hs : s ≤ 1) (ht : t ≤ 1) :
    K2 (2 - s) t = K2 s (2 - t) := by
  rw [cross_kernel s t hs ht]
  unfold K2
  rw [min_eq_right (by linarith : t ≤ 2 - s)]
  ring

theorem reflected_both (s t : ℝ) : K2 (2 - s) (2 - t) = K2 s t := by
  unfold K2
  rcases le_total s t with h | h
  · rw [min_eq_right (by linarith : 2 - t ≤ 2 - s), min_eq_left h]
    ring
  · rw [min_eq_left (by linarith : 2 - s ≤ 2 - t), min_eq_right h]
    ring

theorem odd_kernel (s t : ℝ) (hs : s ≤ 1) (ht : t ≤ 1) :
    K2 s t - K2 s (2 - t) = KD s t := by
  rw [cross_kernel s t hs ht]
  unfold K2 KD
  ring

theorem even_kernel (s t : ℝ) (hs : s ≤ 1) (ht : t ≤ 1) :
    K2 s t + K2 s (2 - t) = KDN s t := by
  rw [cross_kernel s t hs ht]
  unfold K2 KDN
  ring

private theorem continuous_kernel (s : ℝ) : Continuous (K2 s) := by
  unfold K2
  exact (continuous_const.min continuous_id).sub
    ((continuous_const.mul continuous_id).div_const 2)

private theorem continuous_reflect : Continuous (fun t : ℝ => 2 - t) :=
  continuous_const.sub continuous_id

/-- Actual interval reflection, using the Lebesgue change of variables. -/
theorem split_reflection (F : ℝ → ℝ) (hF : Continuous F) :
    (∫ t in (0:ℝ)..2, F t) = ∫ t in (0:ℝ)..1, (F t + F (2 - t)) := by
  have hr : (∫ t in (0:ℝ)..1, F (2 - t)) = ∫ t in (1:ℝ)..2, F t := by
    simpa only [show (2:ℝ) - 1 = 1 by norm_num, sub_zero] using
      (intervalIntegral.integral_comp_sub_left (a := (0:ℝ)) (b := 1) F 2)
  calc
    (∫ t in (0:ℝ)..2, F t) =
        (∫ t in (0:ℝ)..1, F t) + (∫ t in (1:ℝ)..2, F t) :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hF.intervalIntegrable 0 1) (hF.intervalIntegrable 1 2)).symm
    _ = (∫ t in (0:ℝ)..1, F t) + (∫ t in (0:ℝ)..1, F (2 - t)) := by rw [← hr]
    _ = ∫ t in (0:ℝ)..1, (F t + F (2 - t)) := by
      exact (intervalIntegral.integral_add (hF.intervalIntegrable 0 1)
        ((hF.comp continuous_reflect).intervalIntegrable 0 1)).symm

def apply2 (f : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ t in (0:ℝ)..2, K2 s t * f t

/-- Genuine integral-level antisymmetric Green intertwining, before L² completion. -/
theorem odd_green_integral (f : ℝ → ℝ) (hf : Continuous f) (s : ℝ)
    (hs : s ≤ 1) :
    apply2 f s - apply2 f (2 - s) =
      ∫ t in (0:ℝ)..1, KD s t * (f t - f (2 - t)) := by
  let F : ℝ → ℝ := fun t => K2 s t * f t
  let H : ℝ → ℝ := fun t => K2 (2 - s) t * f t
  have hF : Continuous F := (continuous_kernel s).mul hf
  have hH : Continuous H := (continuous_kernel (2 - s)).mul hf
  change (∫ t in (0:ℝ)..2, F t) - (∫ t in (0:ℝ)..2, H t) = _
  rw [split_reflection F hF, split_reflection H hH]
  change (∫ t in (0:ℝ)..1, (F + F ∘ (fun t => 2 - t)) t) -
      (∫ t in (0:ℝ)..1, (H + H ∘ (fun t => 2 - t)) t) = _
  rw [← intervalIntegral.integral_sub
    ((hF.add (hF.comp continuous_reflect)).intervalIntegrable 0 1)
    ((hH.add (hH.comp continuous_reflect)).intervalIntegrable 0 1)]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0:ℝ) 1 := by
    simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using ht
  change K2 s t * f t + K2 s (2 - t) * f (2 - t) -
      (K2 (2 - s) t * f t + K2 (2 - s) (2 - t) * f (2 - t)) =
      KD s t * (f t - f (2 - t))
  rw [reflected_first s t hs ht'.2, reflected_both s t,
    ← odd_kernel s t hs ht'.2]
  ring

/-- Genuine integral-level symmetric Green intertwining, before L² completion. -/
theorem even_green_integral (f : ℝ → ℝ) (hf : Continuous f) (s : ℝ)
    (hs : s ≤ 1) :
    apply2 f s + apply2 f (2 - s) =
      ∫ t in (0:ℝ)..1, KDN s t * (f t + f (2 - t)) := by
  let F : ℝ → ℝ := fun t => K2 s t * f t
  let H : ℝ → ℝ := fun t => K2 (2 - s) t * f t
  have hF : Continuous F := (continuous_kernel s).mul hf
  have hH : Continuous H := (continuous_kernel (2 - s)).mul hf
  change (∫ t in (0:ℝ)..2, F t) + (∫ t in (0:ℝ)..2, H t) = _
  rw [split_reflection F hF, split_reflection H hH]
  change (∫ t in (0:ℝ)..1, (F + F ∘ (fun t => 2 - t)) t) +
      (∫ t in (0:ℝ)..1, (H + H ∘ (fun t => 2 - t)) t) = _
  rw [← intervalIntegral.integral_add
    ((hF.add (hF.comp continuous_reflect)).intervalIntegrable 0 1)
    ((hH.add (hH.comp continuous_reflect)).intervalIntegrable 0 1)]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0:ℝ) 1 := by
    simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using ht
  change K2 s t * f t + K2 s (2 - t) * f (2 - t) +
      (K2 (2 - s) t * f t + K2 (2 - s) (2 - t) * f (2 - t)) =
      KDN s t * (f t + f (2 - t))
  rw [reflected_first s t hs ht'.2, reflected_both s t,
    ← even_kernel s t hs ht'.2]
  ring

#print axioms cross_kernel
#print axioms reflected_first
#print axioms reflected_both
#print axioms odd_kernel
#print axioms even_kernel
#print axioms split_reflection
#print axioms odd_green_integral
#print axioms even_green_integral

end Manuscript14Priority3.GreenReflection
