import Mathlib

/-!
Manuscript 16, "REFERENCES_REPAIRED_FINAL", §2.3.
Source equations: feff-pullback, feff-levicivita (scalar rescaling),
feff-equiv-P (abstract invariant-domain bijection), and
feff-eigen (resonant parity and dimension).
No actual differential-geometric intertwining is claimed.
-/
namespace Manuscript16.FeffermanAdditional20261123

/-- The coframe calculation: -dτ²+(σ₀-dτ)²+σ₁²+σ₂²
is the displayed symmetric-product Fefferman expression. -/
theorem pullback_coframe_expansion (sigma0 sigma1 sigma2 dt : ℝ) :
    -dt ^ 2 + (sigma0 - dt) ^ 2 + sigma1 ^ 2 + sigma2 ^ 2 =
      sigma0 ^ 2 + sigma1 ^ 2 + sigma2 ^ 2 - 2 * sigma0 * dt := by
  ring

/-- Curvature scaling for 2g_F = Φ*g_E, given Scal(g_E)=6. -/
theorem scalar_curvature_constant_rescaling :
    (6 : ℝ) / (1 / 2) = 12 := by
  norm_num

/-- The resonance restriction is exactly equivalence of parities,
provided the spatial Hopf weight is congruent to the degree. -/
theorem shifted_resonance_parity_iff (ell n k : ℤ)
    (hweight : (k - ell) % 2 = 0)
    (hres : ell ^ 2 - (n - k) ^ 2 = 0) :
    (n + ell) % 2 = 0 ↔ ell % 2 = 0 := by
  have hfactor : (ell - n + k) * (ell + n - k) = 0 := by
    nlinarith [hres]
  rcases mul_eq_zero.mp hfactor with h1 | h2 <;> omega

/-- Two distinct temporal branches, each with spatial multiplicity
d_ell = 2(ell²-1), give 4(ell²-1). -/
theorem paired_resonance_multiplicity (ell : ℕ) :
    2 * (2 * (ell ^ 2 - 1)) = 4 * (ell ^ 2 - 1) := by
  ring

/-- The naturality statement for deck-fixed subspaces, expressed
at the correct level of abstract bijections. -/
theorem fixed_iff_under_conjugacy {X : Type*}
    (P : X ≃ X) (A I : X → X)
    (hconj : ∀ x, I (P x) = P (A x)) (x : X) :
    I (P x) = P x ↔ A x = x := by
  rw [hconj x]
  exact P.injective.eq_iff

/-- Exact invertible transport preserves the algebraic kernel.
The domain of an unbounded differential operator is not inferred. -/
theorem conjugation_kernel_iff {X : Type*} [Zero X]
    (P : X ≃ X) (W : X → X) (hzero : P 0 = 0) (x : X) :
    P (W (P.symm x)) = 0 ↔ W (P.symm x) = 0 := by
  constructor
  · intro h
    apply P.injective
    simpa [hzero] using h
  · intro h
    simpa [h, hzero]

#print axioms Manuscript16.FeffermanAdditional20261123.pullback_coframe_expansion
#print axioms Manuscript16.FeffermanAdditional20261123.scalar_curvature_constant_rescaling
#print axioms Manuscript16.FeffermanAdditional20261123.shifted_resonance_parity_iff
#print axioms Manuscript16.FeffermanAdditional20261123.paired_resonance_multiplicity
#print axioms Manuscript16.FeffermanAdditional20261123.fixed_iff_under_conjugacy
#print axioms Manuscript16.FeffermanAdditional20261123.conjugation_kernel_iff
end Manuscript16.FeffermanAdditional20261123
