import SharedCore.FredholmCompactParametrix
import Mathlib.Analysis.Normed.Operator.Fredholm.Open
import Mathlib.Analysis.Normed.Module.Complemented
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# Atkinson's criterion and compact-perturbation index stability

For actual bounded operators between arbitrary complete complex Hilbert
spaces, compact two-sided parametrix defects are equivalent to Mathlib's
full `IsFredholm` predicate. Compact perturbations preserve Fredholmness
and the integer index, with no small-norm or normality hypothesis.

The closed-range and finite-defect argument is imported from
`SharedCore.FredholmCompactParametrix` (PR #455). The converse uses
Mathlib's continuous finite-rank quasi-inverse. Index invariance uses
Mathlib's local constancy of the Fredholm index along a connected path.
These are classical results, formalized here to discharge gate F8.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SharedCore.FredholmAtkinson

open Submodule Topology
open scoped LinearMap.FiniteRangeSetoid

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- A bounded map with finite-dimensional range is compact. -/
theorem compact_of_finite_range (T : E →L[ℂ] F)
    (hT : T.toLinearMap.HasFiniteRange) : IsCompactOperator T := by
  haveI : FiniteDimensional ℂ T.range := Module.Finite.of_fg hT
  have hId : IsCompactOperator (id : T.range → T.range) :=
    isCompactOperator_id_iff_finiteDimensional.mpr (inferInstance : FiniteDimensional ℂ T.range)
  exact (hId.comp_clm T.rangeRestrict).clm_comp T.range.subtypeL

/-- Compact parametrices imply the full Fredholm predicate, including the
quotient cokernel, strictness, and complemented kernel. -/
theorem isFredholm_of_compact_parametrix (T : E →L[ℂ] F) (S : F →L[ℂ] E)
    (hL : IsCompactOperator ((1 : E →L[ℂ] E) - S.comp T))
    (hR : IsCompactOperator ((1 : F →L[ℂ] F) - T.comp S)) : T.IsFredholm := by
  obtain ⟨hclosed, hker, hperp⟩ :=
    FredholmParametrix.fredholm_components_of_compact_parametrix T S hL hR
  have hclosed' : IsClosed (T.range : Set F) := hclosed
  letI : CompleteSpace T.range := hclosed'.completeSpace_coe
  letI : T.range.HasOrthogonalProjection := .ofCompleteSpace T.range
  letI : CompleteSpace T.ker := T.isClosed_ker.completeSpace_coe
  letI : T.ker.HasOrthogonalProjection := .ofCompleteSpace T.ker
  letI : FiniteDimensional ℂ T.rangeᗮ := hperp
  refine ⟨?_, hclosed', hker, ?_, ?_⟩
  · rw [isStrictMap_iff_isQuotientMap_rangeFactorization]
    exact T.rangeRestrict.isQuotientMap T.toLinearMap.surjective_rangeRestrict
  · exact Submodule.FG.cofg_of_isCompl T.range.isCompl_orthogonal.symm .of_finite
  · exact Submodule.ClosedComplemented.of_isCompl_isClosed
      T.ker.isCompl_orthogonal T.isClosed_ker T.ker.isClosed_orthogonal

/-- Every Fredholm operator admits a bounded two-sided parametrix with
compact defects; in fact Mathlib supplies finite-rank defects. -/
theorem exists_compact_parametrix (T : E →L[ℂ] F) (hT : T.IsFredholm) :
    ∃ S : F →L[ℂ] E,
      IsCompactOperator ((1 : E →L[ℂ] E) - S.comp T) ∧
      IsCompactOperator ((1 : F →L[ℂ] F) - T.comp S) := by
  obtain ⟨S, hS⟩ := hT.exists_isQuasiInverse
  refine ⟨S, ?_, ?_⟩
  · apply compact_of_finite_range
    exact LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange.mp (Setoid.symm hS.1)
  · apply compact_of_finite_range
    exact LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange.mp (Setoid.symm hS.2)

/-- Atkinson's criterion for arbitrary bounded operators between complete
complex Hilbert spaces, expressed through a compact two-sided parametrix. -/
theorem isFredholm_iff_compact_parametrix (T : E →L[ℂ] F) :
    T.IsFredholm ↔ ∃ S : F →L[ℂ] E,
      IsCompactOperator ((1 : E →L[ℂ] E) - S.comp T) ∧
      IsCompactOperator ((1 : F →L[ℂ] F) - T.comp S) := by
  exact ⟨exists_compact_parametrix T, fun ⟨S, hL, hR⟩ =>
    isFredholm_of_compact_parametrix T S hL hR⟩

/-- Arbitrarily large compact perturbations preserve Fredholmness. -/
theorem isFredholm_add_compact (T P : E →L[ℂ] F)
    (hT : T.IsFredholm) (hP : IsCompactOperator P) : (T + P).IsFredholm := by
  obtain ⟨S, hL, hR⟩ := exists_compact_parametrix T hT
  apply isFredholm_of_compact_parametrix (T + P) S
  · have he : (1 : E →L[ℂ] E) - S.comp (T + P) =
        (1 - S.comp T) - S.comp P := by
      rw [ContinuousLinearMap.comp_add]
      abel
    rw [he]
    exact hL.sub (hP.clm_comp S)
  · have he : (1 : F →L[ℂ] F) - (T + P).comp S =
        (1 - T.comp S) - P.comp S := by
      rw [ContinuousLinearMap.add_comp]
      abel
    rw [he]
    exact hR.sub (hP.comp_clm S)

/-- Compact perturbations preserve the actual integer Fredholm index.
The proof includes all points of the affine path, also noninvertible ones. -/
theorem index_add_compact (T P : E →L[ℂ] F)
    (hT : T.IsFredholm) (hP : IsCompactOperator P) : (T + P).index = T.index := by
  let A : ℂ → E →L[ℂ] F := fun t => T + t • P
  have hA : Continuous A := continuous_const.add (continuous_id.smul continuous_const)
  have hF (t : ℂ) : (A t).IsFredholm := isFredholm_add_compact T (t • P) hT (hP.smul t)
  have hIndex : Continuous (fun t : ℂ => (A t).index) :=
    continuous_iff_continuousAt.mpr fun t => (hF t).index_continuousAt.comp hA.continuousAt
  have hconstant := (IsLocallyConstant.iff_continuous _).mpr hIndex
  simpa [A] using hconstant.apply_eq_of_preconnectedSpace 1 0

/-- Both conclusions of compact-perturbation stability, in one theorem. -/
theorem compact_perturbation_stability (T P : E →L[ℂ] F)
    (hT : T.IsFredholm) (hP : IsCompactOperator P) :
    (T + P).IsFredholm ∧ (T + P).index = T.index :=
  ⟨isFredholm_add_compact T P hT hP, index_add_compact T P hT hP⟩

/-- Fredholmness is equivalent before and after a compact perturbation. -/
theorem isFredholm_add_compact_iff (T P : E →L[ℂ] F)
    (hP : IsCompactOperator P) : (T + P).IsFredholm ↔ T.IsFredholm := by
  constructor
  · intro h
    simpa using isFredholm_add_compact (T + P) (-P) h hP.neg
  · exact fun h => isFredholm_add_compact T P h hP

/-- Every nonzero scalar shift of an arbitrary compact operator is
Fredholm of index zero, including exceptional spectral parameters. -/
theorem compact_shift_isFredholm_index_zero (K : E →L[ℂ] E)
    (hK : IsCompactOperator K) (μ : ℂ) (hμ : μ ≠ 0) :
    (μ • (1 : E →L[ℂ] E) - K).IsFredholm ∧
      (μ • (1 : E →L[ℂ] E) - K).index = 0 := by
  have hInv : (μ • (1 : E →L[ℂ] E)).IsInvertible := by
    apply ContinuousLinearMap.IsInvertible.of_inverse (g := μ⁻¹ • (1 : E →L[ℂ] E))
    · ext x
      simp [smul_smul, hμ]
    · ext x
      simp [smul_smul, hμ]
  have hzero : (μ • (1 : E →L[ℂ] E)).index = 0 :=
    LinearMap.index_of_bijective hInv.bijective
  simpa only [← sub_eq_add_neg, hzero] using
    compact_perturbation_stability (μ • (1 : E →L[ℂ] E)) (-K) hInv.isFredholm hK.neg

#print axioms compact_of_finite_range
#print axioms isFredholm_of_compact_parametrix
#print axioms exists_compact_parametrix
#print axioms isFredholm_iff_compact_parametrix
#print axioms isFredholm_add_compact
#print axioms index_add_compact
#print axioms compact_perturbation_stability
#print axioms isFredholm_add_compact_iff
#print axioms compact_shift_isFredholm_index_zero

end SharedCore.FredholmAtkinson
