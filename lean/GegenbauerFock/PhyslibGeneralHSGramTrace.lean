import GegenbauerFock.PhyslibHilbertSchmidtCompat

/-!
# V007 — generic Hilbert--Schmidt-to-trace-class Gram bridge

This module removes the ultraspherical restriction from the positive
S₂ -> S₁ construction. For arbitrary complete complex Hilbert spaces
E and F, an actual basis-independent Hilbert--Schmidt map T : E -> F
has a CFC-absolute trace-class Gram T†T on E. Moreover its Gram also
belongs to the upstream-compatible Hilbert--Schmidt endomorphism class.

The trace norm identity is evaluated in the *precise basis carried by
the Physlib trace-class witness*. No unproved general basis-independence
of CFC trace, additivity, Banach completion or unrestricted S₁ ideal
law is assumed.

Pinned Lean v4.35.0-rc3 and existing Mathlib only. No new axioms.
-/

noncomputable section

namespace ProbabilisticTheory

open GegenbauerFock

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

private theorem gramBridge_re_inner_swap (x y : E) :
    (inner ℂ x y).re = (inner ℂ y x).re := by
  calc
    (inner ℂ x y).re = (star (inner ℂ y x)).re :=
      congrArg Complex.re (inner_conj_symm (𝕜 := ℂ) x y).symm
    _ = (inner ℂ y x).re := by
      simp only [Complex.star_def, Complex.conj_re]

/-- Every rectangular Hilbert--Schmidt operator between arbitrary complete
complex Hilbert spaces has a genuinely CFC-absolute trace-class Gram.
No finite-rank hypothesis or particular Gegenbauer--Fock kernel is used. -/
theorem isTraceClass_adjoint_comp_self_of_isHS
    (T : E →L[ℂ] F) (hT : HilbertSchmidtBasis.IsHS T) :
    IsTraceClass (T.adjoint.comp T) := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ E
  have hp : 0 ≤ T.adjoint.comp T :=
    (ContinuousLinearMap.nonneg_iff_isPositive).2
      (ContinuousLinearMap.isPositive_adjoint_comp_self T)
  have hs : Summable (fun i : w =>
      (inner ℂ (b i) ((T.adjoint.comp T) (b i))).re) := by
    have henergy : Summable (fun i : w => ‖T (b i)‖ ^ 2) := hT b
    apply henergy.congr
    intro i
    have hn : ‖T (b i)‖ ^ 2 =
        (inner ℂ ((T.adjoint.comp T) (b i)) (b i)).re := by
      simpa only [GegenbauerFock.HilbertGram.gram, RCLike.re_eq_complex_re] using
        (GegenbauerFock.HilbertGram.gram_norm_sq T (b i))
    exact hn.trans
      (gramBridge_re_inner_swap ((T.adjoint.comp T) (b i)) (b i))
  exact isTraceClass_of_nonneg_of_summable (T.adjoint.comp T) hp b hs

/-- The true CFC trace norm of an abstract Hilbert--Schmidt Gram equals
the complete squared-image energy in its *witness-selected* Hilbert basis.
This identity holds in infinite dimension, not just for finite matrices. -/
theorem traceNorm_adjoint_comp_self_eq_witness_energy
    (T : E →L[ℂ] F) (hT : HilbertSchmidtBasis.IsHS T) :
    traceNorm (T.adjoint.comp T)
      (isTraceClass_adjoint_comp_self_of_isHS T hT) =
      ∑' i : (isTraceClass_adjoint_comp_self_of_isHS T hT).choose,
        ‖T ((isTraceClass_adjoint_comp_self_of_isHS T hT).choose_spec.choose i)‖ ^ 2 := by
  let h := isTraceClass_adjoint_comp_self_of_isHS T hT
  have hp : 0 ≤ T.adjoint.comp T :=
    (ContinuousLinearMap.nonneg_iff_isPositive).2
      (ContinuousLinearMap.isPositive_adjoint_comp_self T)
  rw [traceNorm_eq_diagonal_of_nonneg (T.adjoint.comp T) hp h]
  apply tsum_congr
  intro i
  have hn := GegenbauerFock.HilbertGram.gram_norm_sq T (h.choose_spec.choose i)
  have hn' : ‖T (h.choose_spec.choose i)‖ ^ 2 =
      (inner ℂ ((T.adjoint.comp T) (h.choose_spec.choose i))
        (h.choose_spec.choose i)).re := by
    simpa only [GegenbauerFock.HilbertGram.gram, RCLike.re_eq_complex_re] using hn
  exact (gramBridge_re_inner_swap (h.choose_spec.choose i)
    ((T.adjoint.comp T) (h.choose_spec.choose i))).trans hn'.symm

/-- Generic abstract bridge into both source-compatible Schatten
predicates: an arbitrary rectangular S₂ map has a Gram in S₁ ∩ S₂. -/
theorem adjoint_comp_self_in_S1_and_S2_of_isHS
    (T : E →L[ℂ] F) (hT : HilbertSchmidtBasis.IsHS T) :
    IsTraceClass (T.adjoint.comp T) ∧
      HilbertSchmidt.IsHilbertSchmidt (T.adjoint.comp T) := by
  constructor
  · exact isTraceClass_adjoint_comp_self_of_isHS T hT
  · obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ E
    refine ⟨w, b, ?_⟩
    exact (HilbertSchmidtBasis.isHS_comp_left T hT T.adjoint) b

#print axioms ProbabilisticTheory.isTraceClass_adjoint_comp_self_of_isHS
#print axioms ProbabilisticTheory.traceNorm_adjoint_comp_self_eq_witness_energy
#print axioms ProbabilisticTheory.adjoint_comp_self_in_S1_and_S2_of_isHS

end ProbabilisticTheory
