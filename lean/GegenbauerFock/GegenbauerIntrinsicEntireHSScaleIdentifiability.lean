import GegenbauerFock.GegenbauerIntrinsicEntireHSStrictMonotonicity

/-!
# V007 — unique recovery of the Gaussian width from scalar S₂/Gram mass

The intrinsic entire-Fock transform has exactly the same pointwise
Fourier–Bochner entire output at different positive Gaussian widths;
however its Gaussian-Hilbert S₂ energy varies *strictly* with width.

Thus equality of exact scalar Hilbert–Schmidt energies or genuine
intrinsic source-Gram diagonal traces (for a common complete source
Hilbert basis) uniquely determines the Gaussian width α>0.

This is scalar parameter identifiability only: it does NOT contradict
the independently certified ill-posed reconstruction of the L² input
function from the compact ultraspherical-Fock transform.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- For fixed positive ultraspherical λ, equality of the actual
analytic Gaussian Fock S₂ masses forces equality of Gaussian scales. -/
theorem C_intrinsicEntire_HS_energy_identifies_alpha
    (lam alpha₁ alpha₂ : ℝ)
    (hlam : 0 < lam) (ha₁ : 0 < alpha₁) (ha₂ : 0 < alpha₂)
    {ι : Type*}
    (b : HilbertBasis ι ℂ (Lp ℂ 2 (Ultraspherical.measure lam)))
    (heq :
      (∑' i : ι, ‖C_intrinsicEntire lam alpha₁ hlam ha₁ (b i)‖ ^ 2) =
        ∑' i : ι, ‖C_intrinsicEntire lam alpha₂ hlam ha₂ (b i)‖ ^ 2) :
    alpha₁ = alpha₂ := by
  rcases lt_trichotomy alpha₁ alpha₂ with hlt | hequal | hgt
  · have hstrict :=
      C_intrinsicEntire_HS_energy_strictAnti_alpha
        lam alpha₁ alpha₂ hlam ha₁ ha₂ hlt b
    exact False.elim (hstrict.ne heq.symm)
  · exact hequal
  · have hstrict :=
      C_intrinsicEntire_HS_energy_strictAnti_alpha
        lam alpha₂ alpha₁ hlam ha₂ ha₁ hgt b
    exact False.elim (hstrict.ne heq)

/-- The full positive intrinsic source-Gram real diagonal trace
likewise uniquely identifies the positive Gaussian scale. -/
theorem C_intrinsicEntire_Gram_trace_identifies_alpha
    (lam alpha₁ alpha₂ : ℝ)
    (hlam : 0 < lam) (ha₁ : 0 < alpha₁) (ha₂ : 0 < alpha₂)
    {ι : Type*}
    (b : HilbertBasis ι ℂ (Lp ℂ 2 (Ultraspherical.measure lam)))
    (heq :
      (∑' i : ι, RCLike.re (inner ℂ
        (C_intrinsicEntire_gram lam alpha₁ hlam ha₁ (b i)) (b i))) =
        ∑' i : ι, RCLike.re (inner ℂ
          (C_intrinsicEntire_gram lam alpha₂ hlam ha₂ (b i)) (b i))) :
    alpha₁ = alpha₂ := by
  rcases lt_trichotomy alpha₁ alpha₂ with hlt | hequal | hgt
  · have hstrict :=
      C_intrinsicEntire_Gram_trace_strictAnti_alpha
        lam alpha₁ alpha₂ hlam ha₁ ha₂ hlt b
    exact False.elim (hstrict.ne heq.symm)
  · exact hequal
  · have hstrict :=
      C_intrinsicEntire_Gram_trace_strictAnti_alpha
        lam alpha₂ alpha₁ hlam ha₂ ha₁ hgt b
    exact False.elim (hstrict.ne heq)

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_HS_energy_identifies_alpha
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_Gram_trace_identifies_alpha

end GegenbauerFock.GeneralUltrasphericalFock
