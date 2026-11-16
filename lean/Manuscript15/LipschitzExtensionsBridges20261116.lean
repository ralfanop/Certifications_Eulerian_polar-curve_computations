import Mathlib

/-! Algebraic and domain-aware bridge lemmas for the new §8.
No claim of a constructed Dirichlet Laplacian or metric asymptotic. -/
open scoped BigOperators
namespace Manuscript15.LipschitzExtensions

theorem cusp_power_inequality (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x^2+y^2)^3 ≤ 2*(x^3+y^3)^2 := by
  have h : 0 ≤ (x-y)^2*(x^4+2*x^3*y+2*x*y^3+y^4) := by positivity
  calc
    (x^2+y^2)^3 ≤ (x^2+y^2)^3 +
        (x-y)^2*(x^4+2*x^3*y+2*x*y^3+y^4) := le_add_of_nonneg_right h
    _ = _ := by ring

/-- Cubed version of the cross-branch Hölder estimate, avoiding fractional
powers and exposing precisely the metric bounds that must be proved. -/
theorem cusp_cross_bound (x y C c dIn dOut : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hC : 0 ≤ C) (hc : 0 < c)
    (hi : 0 ≤ dIn) (ho : 0 ≤ dOut)
    (hI : dIn ≤ C/2*(x^2+y^2))
    (hO : c*(x^3+y^3) ≤ dOut) :
    c^2*dIn^3 ≤ C^3/4*dOut^2 := by
  have hp := cusp_power_inequality x y hx hy
  have h1 : dIn^3 ≤ (C/2*(x^2+y^2))^3 := by gcongr
  have h2 : (c*(x^3+y^3))^2 ≤ dOut^2 := by gcongr
  calc
    c^2*dIn^3 ≤ c^2*(C/2*(x^2+y^2))^3 :=
      mul_le_mul_of_nonneg_left h1 (sq_nonneg c)
    _ = c^2*C^3/8*(x^2+y^2)^3 := by ring
    _ ≤ c^2*C^3/8*(2*(x^3+y^3)^2) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = C^3/4*(c*(x^3+y^3))^2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by positivity)

noncomputable def grid (R : ℝ) (N j : ℕ) : ℝ := -R+(j:ℝ)*(2*R/N)

theorem grid_step (R : ℝ) (N j : ℕ) :
    grid R N (j+1)-grid R N j = 2*R/N := by
  unfold grid
  push_cast
  ring

theorem grid_separation (R : ℝ) (N j k : ℕ)
    (hR : 0 ≤ R) (h : j ≠ k) :
    2*R/N ≤ |grid R N j-grid R N k| := by
  have hh : 0 ≤ 2*R/(N:ℝ) := by positivity
  have hs : (1:ℝ) ≤ |(j:ℝ)-(k:ℝ)| := by
    rcases lt_or_gt_of_ne h with hj | hk
    · have hnat : j+1 ≤ k := hj
      have hr : (j:ℝ)+1 ≤ k := by exact_mod_cast hnat
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have hnat : k+1 ≤ j := hk
      have hr : (k:ℝ)+1 ≤ j := by exact_mod_cast hnat
      rw [abs_of_nonneg (by linarith)]
      linarith
  rw [show grid R N j-grid R N k = ((j:ℝ)-(k:ℝ))*(2*R/N) by unfold grid; ring,
      abs_mul, abs_of_nonneg hh]
  simpa using mul_le_mul_of_nonneg_right hs hh

/-- The two neighboring binomial edge weights give the internal vertex
weight, before normalization. Boundary weights follow from choose_zero
and choose_self. -/
theorem adjacent_pascal (N j : ℕ) :
    (N.choose j : ℝ) + (N.choose (j+1) : ℝ) = ((N+1).choose (j+1) : ℝ) := by
  rw [Nat.choose_succ_succ, Nat.cast_add]

/-- Binomial Fourier polynomial, valid for every N, not finite testing. -/
theorem signed_binomial_polynomial (N : ℕ) (z : ℂ) :
    (∑ j ∈ Finset.range (N+1), (-z)^j * (N.choose j : ℂ)) = (1-z)^N := by
  have h := add_pow (-z) (1:ℂ) N
  simpa [sub_eq_add_neg, add_comm] using h.symm

/-- Domain-aware resolvent reduction: Adom/Hdom describe the genuine
operator domains once supplied. The intertwining and inverse relations
are explicit hypotheses, not a construction of the PDE operators. -/
theorem channel_resolvent_bridge
    {E F : Type*} [AddCommGroup E] [AddCommGroup F]
    [Module ℝ E] [Module ℝ F]
    (Adom : Set E) (Hdom : Set F) (A : E → E) (H : F → F)
    (U : E →ₗ[ℝ] F) (V : F → E) (R : F → F) (S : E → E)
    (l s : ℝ)
    (hU : ∀ x ∈ Adom, U x ∈ Hdom)
    (hinter : ∀ x ∈ Adom, H (U x) = U (A x + l • x))
    (hSdom : ∀ x, S x ∈ Adom)
    (hS : ∀ x, A (S x)+(l+s) • S x=x)
    (hR : ∀ y ∈ Hdom, R (H y+s • y)=y)
    (hV : ∀ x, V (U x)=x) (x : E) :
    V (R (U x)) = S x := by
  have hD := hSdom x
  have he : H (U (S x))+s • U (S x)=U x := by
    rw [hinter _ hD, ← U.map_smul, ← U.map_add]
    rw [add_assoc, ← add_smul, hS]
  have h := hR _ (hU _ hD)
  rw [he] at h
  rw [h, hV]

end Manuscript15.LipschitzExtensions
#print axioms Manuscript15.LipschitzExtensions.cusp_power_inequality
#print axioms Manuscript15.LipschitzExtensions.cusp_cross_bound
#print axioms Manuscript15.LipschitzExtensions.grid_step
#print axioms Manuscript15.LipschitzExtensions.grid_separation
#print axioms Manuscript15.LipschitzExtensions.adjacent_pascal
#print axioms Manuscript15.LipschitzExtensions.signed_binomial_polynomial
#print axioms Manuscript15.LipschitzExtensions.channel_resolvent_bridge
