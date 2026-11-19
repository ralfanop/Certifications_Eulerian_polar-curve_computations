import Mathlib

/-! M16 §13: isometric transport of actual coefficient-space operators through
Mathlib's HilbertBasis. The basis is an explicit input; its construction from
the Maxwell and Dirac eigenfields is a separate geometric obligation. -/
namespace Manuscript16.V166HilbertSpectralTransport

abbrev L2 (ι : Type*) := lp (fun _ : ι => ℂ) 2
variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

noncomputable def transport (b : HilbertBasis ι ℂ H)
    (T : L2 ι →L[ℂ] L2 ι) : H →L[ℂ] H :=
  b.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (T.comp b.repr.toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] theorem transport_apply (b : HilbertBasis ι ℂ H)
    (T : L2 ι →L[ℂ] L2 ι) (x : H) :
    transport b T x = b.repr.symm (T (b.repr x)) := rfl

theorem transport_norm (b : HilbertBasis ι ℂ H)
    (T : L2 ι →L[ℂ] L2 ι) : ‖transport b T‖ = ‖T‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
    intro x
    rw [transport_apply, b.repr.symm.norm_map, ← b.repr.norm_map x]
    exact T.le_opNorm _
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (transport b T))
    intro y
    have h := (transport b T).le_opNorm (b.repr.symm y)
    simpa only [transport_apply, b.repr.apply_symm_apply, b.repr.symm.norm_map] using h

theorem transport_sub (b : HilbertBasis ι ℂ H)
    (T R : L2 ι →L[ℂ] L2 ι) :
    transport b (T-R) = transport b T - transport b R := by
  apply ContinuousLinearMap.ext
  intro x
  simp

theorem transport_error (b : HilbertBasis ι ℂ H)
    (T R : L2 ι →L[ℂ] L2 ι) :
    ‖transport b T - transport b R‖ = ‖T-R‖ := by
  rw [← transport_sub, transport_norm]

theorem transport_eigenvector (b : HilbertBasis ι ℂ H)
    (T : L2 ι →L[ℂ] L2 ι) (d : ι → ℂ) [DecidableEq ι]
    (hT : ∀ i, T (lp.single 2 i 1) = d i • lp.single 2 i 1) (i : ι) :
    transport b T (b i) = d i • b i := by
  rw [transport_apply, b.repr_self, hT i, map_smul, b.repr_symm_single]

/-- Finite-rank factors are carried to actual bounded factors of the
same dimension, with identical operator-norm error. -/
theorem transport_rank_factor (b : HilbertBasis ι ℂ H)
    (T : L2 ι →L[ℂ] L2 ι) (n : ℕ)
    (F : L2 ι →L[ℂ] (Fin n → ℂ)) (G : (Fin n → ℂ) →L[ℂ] L2 ι) :
    ∃ F' : H →L[ℂ] (Fin n → ℂ), ∃ G' : (Fin n → ℂ) →L[ℂ] H,
      ‖transport b T - G'.comp F'‖ = ‖T - G.comp F‖ := by
  refine ⟨F.comp b.repr.toContinuousLinearEquiv.toContinuousLinearMap,
    b.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp G, ?_⟩
  have he : transport b (G.comp F) =
      (b.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp G).comp
        (F.comp b.repr.toContinuousLinearEquiv.toContinuousLinearMap) := by
    ext x
    rfl
  rw [← he]
  exact transport_error b T (G.comp F)

#print axioms transport_apply
#print axioms transport_norm
#print axioms transport_sub
#print axioms transport_error
#print axioms transport_eigenvector
#print axioms transport_rank_factor
end Manuscript16.V166HilbertSpectralTransport
