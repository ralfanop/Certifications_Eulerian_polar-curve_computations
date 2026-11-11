import SpecialImaginaryPoint.V14119Priority3DirichletNegativeFredholmZeros
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Priority 3 — COMPLETE spectral zero set of the true universal CFC S₁ Dirichlet Fredholm determinant

For every complex spectral parameter lambda, including zero,
  det_F(I + lambda A_D⁻¹) = 0
      iff
  lambda = -(k*pi)^2 for a NONZERO integer k.

This is the actual representation-independent CFC Schatten-S₁
Fredholm determinant of the genuine Dirichlet inverse spectral
operator on l², constructed as the true limit of finite Hilbert
compression determinants. The proof uses existence of complex
square roots, exact imaginary-integer sinh zeros, their converse,
and normalization det_F(I)=1.

No comparison with the unbounded differential operator on L²(0,1),
nor with a zeta-regularized determinant, is assumed.
-/

noncomputable section

namespace Manuscript14Priority3.DirichletCompleteSpectralZeroSet

open Filter Topology
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.UniversalDirichletSinh
open Manuscript14Priority3.DirichletFredholmZeroLattice
open Manuscript14Priority3.DirichletNegativeFredholmZeros

/-- Complete zero set of the universal genuine CFC-S₁ Dirichlet
inverse Fredholm determinant, in the FULL complex spectral plane. -/
theorem universal_dirichlet_fredholm_zero_iff_negative_pi_square
    (shift : ℂ) :
    fredholmDet inverseTraceClass shift = 0 ↔
      ∃ k : ℤ, k ≠ 0 ∧
        shift = -(((k : ℂ) * (Real.pi : ℂ)) ^ 2) := by
  constructor
  · intro hdet
    obtain ⟨z, hzsq⟩ :=
      IsAlgClosed.exists_pow_nat_eq shift (by decide : 0 < (2 : ℕ))
    have hz0 : z ≠ 0 := by
      intro hz0
      have hshiftzero : shift = 0 := by
        rw [← hzsq, hz0]
        norm_num
      rw [hshiftzero, fredholmDet_zero] at hdet
      exact one_ne_zero hdet
    have hdetz : fredholmDet inverseTraceClass (z ^ 2) = 0 := by
      simpa only [hzsq] using hdet
    obtain ⟨k, hk0, hk⟩ :=
      (dirichlet_fredholm_square_zero_iff_integer_pi_I z hz0).mp hdetz
    refine ⟨k, hk0, ?_⟩
    calc
      shift = z ^ 2 := hzsq.symm
      _ = ((k : ℂ) * (Real.pi : ℂ) * Complex.I) ^ 2 := by
        rw [hk]
      _ = -(((k : ℂ) * (Real.pi : ℂ)) ^ 2) := by
        rw [mul_pow, Complex.I_sq]
        ring
  · rintro ⟨k, hk0, hk⟩
    rw [hk]
    exact genuine_dirichlet_fredholm_vanishes_at_negative_eigenvalues k hk0

#print axioms Manuscript14Priority3.DirichletCompleteSpectralZeroSet.universal_dirichlet_fredholm_zero_iff_negative_pi_square

end Manuscript14Priority3.DirichletCompleteSpectralZeroSet
