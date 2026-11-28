import Mathlib

/-! M15 Proposition 10.13, (568)-(570): bounded Hilbert-space Riesz
realization of the radiative kernel criterion, in arbitrary dimension.
The construction of the physical PEC H(curl) solenoidal variational space,
exact lead radiation trace and the equivalence to the open-guide Maxwell
operator are not asserted by this abstract result. -/

noncomputable section
namespace Manuscript15.MaxwellRadiativeKernel20261127

open scoped InnerProductSpace

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem hermitian_quadratic_im_zero (H : E →L[ℂ] E)
    (hH : H.adjoint = H) (u : E) :
    (inner ℂ u (H u)).im = 0 := by
  have h := ContinuousLinearMap.adjoint_inner_right H u u
  rw [hH] at h
  have hi := inner_im_symm (𝕜 := ℂ) u (H u)
  rw [← h] at hi
  change (inner ℂ u (H u)).im = -(inner ℂ u (H u)).im at hi
  linarith

theorem radiative_kernel_pointwise (H : E →L[ℂ] E) (C : E →L[ℂ] F)
    (hH : H.adjoint = H) (u : E) :
    H u - Complex.I • C.adjoint (C u) = 0 ↔ H u = 0 ∧ C u = 0 := by
  constructor
  · intro hz
    have h := congrArg (fun v : E => inner ℂ u v) hz
    rw [inner_sub_right, inner_smul_right,
      ContinuousLinearMap.adjoint_inner_right, inner_zero_right] at h
    have hi := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      zero_mul, one_mul, zero_add, add_zero, Complex.zero_im,
      hermitian_quadratic_im_zero H hH u, inner_self_eq_norm_sq] at hi
    have hself : (inner ℂ (C u) (C u)).re = ‖C u‖^2 := by
      first
      | change RCLike.re (inner ℂ (C u) (C u)) = ‖C u‖^2
        exact inner_self_eq_norm_sq (𝕜 := ℂ) (C u)
      | rw [inner_self_eq_norm_sq_to_K]; simp
    rw [hself] at hi
    have hc : C u = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg (C u)])
    have hhu : H u = 0 := by simpa [hc] using hz
    exact ⟨hhu,hc⟩
  · rintro ⟨hu,hc⟩
    simp [hu,hc]

theorem radiative_kernel_intersection (H : E →L[ℂ] E) (C : E →L[ℂ] F)
    (hH : H.adjoint = H) :
    (H - Complex.I • C.adjoint.comp C).ker = H.ker ⊓ C.ker := by
  ext u
  change H u - Complex.I • C.adjoint (C u) = 0 ↔ H u = 0 ∧ C u = 0
  exact radiative_kernel_pointwise H C hH u

theorem radiative_coercive_exclusion (H : E →L[ℂ] E) (C : E →L[ℂ] F)
    (hH : H.adjoint = H) (δ : ℝ) (hδ : 0 < δ)
    (hbound : ∀ u : E, δ*‖u‖^2 ≤ ‖H u‖^2+‖C u‖^2)
    (u : E) (hu : H u - Complex.I • C.adjoint (C u) = 0) :
    u = 0 := by
  obtain ⟨h1,h2⟩ := (radiative_kernel_pointwise H C hH u).mp hu
  have h := hbound u
  rw [h1,h2,norm_zero] at h
  have hn : ‖u‖^2 ≤ 0 := by
    by_contra! hp
    have hpos := mul_pos hδ hp
    have hz : δ * ‖u‖^2 ≤ 0 := by simpa using h
    exact (not_lt_of_ge hz) hpos
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg u])

end Manuscript15.MaxwellRadiativeKernel20261127

#print axioms Manuscript15.MaxwellRadiativeKernel20261127.hermitian_quadratic_im_zero
#print axioms Manuscript15.MaxwellRadiativeKernel20261127.radiative_kernel_pointwise
#print axioms Manuscript15.MaxwellRadiativeKernel20261127.radiative_kernel_intersection
#print axioms Manuscript15.MaxwellRadiativeKernel20261127.radiative_coercive_exclusion
