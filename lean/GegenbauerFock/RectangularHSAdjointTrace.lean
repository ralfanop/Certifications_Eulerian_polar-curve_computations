import GegenbauerFock.PhyslibGeneralHSGramTrace
import GegenbauerFock.PhyslibTraceBasisIndependence

/-!
# V007 — rectangular Hilbert–Schmidt adjoints and both Gram trace classes

An independently reusable infinite-dimensional theorem:
if T : E → F is Hilbert–Schmidt between arbitrary *distinct* complete
complex Hilbert spaces, so is its Hilbert adjoint T† : F → E.
The proof is by Parseval twice and the nonnegative double-series
Tonelli interchange; no finite-dimensionality or canonical bases.

As an immediate application, both T†T and TT† are genuinely CFC
trace-class (and source-compatible S₂) endomorphisms. This module
depends on the separate generic S₂-to-S₁ Gram bridge, and imports
neither upstream Physlib nor any changed Lean/Mathlib revision.

New declarations are candidates until their exact-sha CI and
#print axioms audit have succeeded.
-/

noncomputable section

namespace GegenbauerFock.HilbertSchmidtBasis

open scoped InnerProductSpace

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The rectangular analogue of Parseval/Fubini for a Hilbert–Schmidt
operator and its adjoint. The source and output bases can even be
indexed by unrelated types. -/
theorem hasSum_adjoint_energy_rectangular
    (T : E →L[ℂ] F)
    {ι κ : Type*} (b : HilbertBasis ι ℂ E) (c : HilbertBasis κ ℂ F)
    (hT : Summable (fun i : ι => ‖T (b i)‖ ^ 2)) :
    HasSum (fun j : κ => ‖T.adjoint (c j)‖ ^ 2)
      (∑' i : ι, ‖T (b i)‖ ^ 2) := by
  classical
  let W : ι → κ → ℝ := fun i j => ‖inner ℂ (c j) (T (b i))‖ ^ 2
  have hWnonneg : 0 ≤ Function.uncurry W := fun _ => sq_nonneg _
  have hrow : ∀ i : ι, HasSum (W i) (‖T (b i)‖ ^ 2) := by
    intro i
    exact ProbabilisticTheory.hasSum_norm_sq_inner_basis c (T (b i))
  have hcol : ∀ j : κ,
      HasSum (fun i : ι => W i j) (‖T.adjoint (c j)‖ ^ 2) := by
    intro j
    have e1 : ∀ i : ι,
        inner ℂ (c j) (T (b i)) = inner ℂ (T.adjoint (c j)) (b i) :=
      fun i => (ContinuousLinearMap.adjoint_inner_left T (b i) (c j)).symm
    have key : (fun i : ι => W i j) =
        fun i : ι => ‖inner ℂ (b i) (T.adjoint (c j))‖ ^ 2 := by
      funext i
      show ‖inner ℂ (c j) (T (b i))‖ ^ 2 = _
      rw [e1 i, ← inner_conj_symm (b i) (T.adjoint (c j)),
        RCLike.norm_conj]
    rw [key]
    exact ProbabilisticTheory.hasSum_norm_sq_inner_basis b (T.adjoint (c j))
  have hjoint : Summable (Function.uncurry W) := by
    rw [summable_prod_of_nonneg hWnonneg]
    refine ⟨fun i => (hrow i).summable, ?_⟩
    have heq : (fun i : ι => ∑' j : κ, W i j) =
        fun i : ι => ‖T (b i)‖ ^ 2 :=
      funext fun i => (hrow i).tsum_eq
    show Summable fun i : ι => ∑' j : κ, W i j
    rwa [heq]
  have hswap :=
    hjoint.tsum_comm' (fun i => (hrow i).summable)
      (fun j => (hcol j).summable)
  have hLHS : ∑' j : κ, ∑' i : ι, W i j =
      ∑' j : κ, ‖T.adjoint (c j)‖ ^ 2 :=
    tsum_congr fun j => (hcol j).tsum_eq
  have hRHS : ∑' i : ι, ∑' j : κ, W i j =
      ∑' i : ι, ‖T (b i)‖ ^ 2 :=
    tsum_congr fun i => (hrow i).tsum_eq
  have hEq : (∑' j : κ, ‖T.adjoint (c j)‖ ^ 2) =
      ∑' i : ι, ‖T (b i)‖ ^ 2 := by
    rw [← hLHS, ← hRHS]
    exact hswap
  let V : κ → ι → ℝ := fun j i => W i j
  have hVnonneg : 0 ≤ Function.uncurry V := fun _ => sq_nonneg _
  have hjointV : Summable (Function.uncurry V) := by
    have hcomp : Function.uncurry V =
        Function.uncurry W ∘ (Equiv.prodComm κ ι) := by
      funext p
      simp [Function.uncurry, V, Equiv.prodComm]
    rw [hcomp]
    exact (Equiv.prodComm κ ι).summable_iff.mpr hjoint
  have hcolSummable : Summable
      (fun j : κ => ‖T.adjoint (c j)‖ ^ 2) := by
    have hpair := (summable_prod_of_nonneg hVnonneg).mp hjointV
    have h2 : Summable (fun j : κ => ∑' i : ι, V j i) := hpair.2
    have heq2 : (fun j : κ => ∑' i : ι, V j i) =
        fun j : κ => ‖T.adjoint (c j)‖ ^ 2 :=
      funext fun j => (hcol j).tsum_eq
    rwa [heq2] at h2
  rw [← hEq]
  exact hcolSummable.hasSum

/-- Hilbert–Schmidt membership survives Hilbert adjunction also when
the domain and codomain are distinct Hilbert spaces. -/
theorem isHS_adjoint_rectangular
    (T : E →L[ℂ] F) (hT : IsHS T) : IsHS T.adjoint := by
  intro κ c
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ E
  exact (hasSum_adjoint_energy_rectangular T b c (hT b)).summable

/-- Source and target Gram operators are both genuine trace class,
and both belong to the source-compatible Hilbert–Schmidt ideal. -/
theorem bothGrams_in_S1_and_S2
    (T : E →L[ℂ] F) (hT : IsHS T) :
    (ProbabilisticTheory.IsTraceClass (T.adjoint.comp T) ∧
      ProbabilisticTheory.HilbertSchmidt.IsHilbertSchmidt
        (T.adjoint.comp T)) ∧
    (ProbabilisticTheory.IsTraceClass (T.comp T.adjoint) ∧
      ProbabilisticTheory.HilbertSchmidt.IsHilbertSchmidt
        (T.comp T.adjoint)) := by
  constructor
  · exact ProbabilisticTheory.adjoint_comp_self_in_S1_and_S2_of_isHS T hT
  · have hstar : IsHS T.adjoint := isHS_adjoint_rectangular T hT
    simpa only [ContinuousLinearMap.adjoint_adjoint] using
      (ProbabilisticTheory.adjoint_comp_self_in_S1_and_S2_of_isHS
        T.adjoint hstar)

#print axioms GegenbauerFock.HilbertSchmidtBasis.hasSum_adjoint_energy_rectangular
#print axioms GegenbauerFock.HilbertSchmidtBasis.isHS_adjoint_rectangular
#print axioms GegenbauerFock.HilbertSchmidtBasis.bothGrams_in_S1_and_S2

end GegenbauerFock.HilbertSchmidtBasis
