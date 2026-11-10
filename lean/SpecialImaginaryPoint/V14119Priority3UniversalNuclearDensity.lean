import SpecialImaginaryPoint.V14119Priority3ArbitraryNuclearRankOne
import GegenbauerFock.PhyslibTraceClassHSFactorization
import GegenbauerFock.PhyslibHilbertSchmidtAdditive
import GegenbauerFock.PhyslibTraceClassOperatorEmbedding

/-!
# Manuscript 14.119 Priority 3 — ALL CFC S₁ maps have nuclear rank-one expansions

This module closes the reverse direction of the arbitrary rank-one
nuclear-series construction. On the actual infinite-dimensional
complex ℓ² Hilbert space, every genuine CFC-absolute Schatten S₁
operator has a certified polar Hilbert–Schmidt factorization
T = R*S. Choose a complete Hilbert basis for the first HS factor.
Then the actual rank-one operators
  |R eᵢ⟩⟨S† eᵢ|
sum to T, and their nuclear costs
  ∑ᵢ ‖R eᵢ‖ ‖S† eᵢ‖
are finite by 2ab ≤ a²+b² and the certified S₂ basis energies.

Each arbitrary rank-one term is a true CFC Schatten S₁ element
with exactly the product cost norm, by the preceding module.
The genuine S₁ sum converges to T, not merely in operator norm.
Thus finite partial rank-one sums are S₁-dense in the entire
CFC Schatten S₁ class, including nonnormal operators.

The summation index is the witness Hilbert-basis set w; the
finite approximants are a directed net over Finset w. This
avoids assuming a countable enumeration of an arbitrary witness basis.

This does NOT yet provide a uniform determinant perturbation
bound or the universal Fredholm determinant. It is its density
prerequisite, not a substitute for its determinant construction.
-/

noncomputable section

namespace Manuscript14Priority3.NuclearRankOne
open Filter Topology InnerProductSpace
open scoped ComplexOrder lp
open Manuscript14Priority3.TraceClassModel

/-- The forgetful map from actual CFC Schatten S₁ to bounded Hilbert
operators is bounded and complex-linear, with sharp constant 1.
It can therefore send arbitrary unconditional S₁ sums to genuine
operator-norm sums, including non-countable index types. -/
def operatorLinear :
    ProbabilisticTheory.TraceClass H →ₗ[ℂ] (H →L[ℂ] H) where
  toFun T := T.1
  map_add' T V := ProbabilisticTheory.TraceClass.add_operator T V
  map_smul' c T := ProbabilisticTheory.TraceClass.smul_operator c T

def operatorCLM :
    ProbabilisticTheory.TraceClass H →L[ℂ] (H →L[ℂ] H) :=
  operatorLinear.mkContinuous 1 (by
    intro T
    simpa only [one_mul] using
      (ProbabilisticTheory.TraceClass.operator_norm_le_trace_norm T))

@[simp] theorem operatorCLM_apply
    (T : ProbabilisticTheory.TraceClass H) :
    operatorCLM T = T.1 := rfl

/-- Every finite family of arbitrary nuclear rank-one CFC S₁
elements is the corresponding EXACT finite sum of genuine
bounded Hilbert rank-one maps. -/
theorem nuclear_finset_operator {ι : Type*}
    (s : Finset ι) (u v : ι → H) :
    ((∑ i ∈ s, rankOneS1 (u i) (v i)) :
       ProbabilisticTheory.TraceClass H).1 =
      ∑ i ∈ s, (rankOne ℂ (u i) (v i) : H →L[ℂ] H) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi,
        ProbabilisticTheory.TraceClass.add_operator, ih]
      rw [rankOneS1_operator]

/-- An unconditional nuclear expansion indexed by ANY type
defines the same true CFC-S₁ element as its convergent
bounded-operator Hilbert rank-one expansion. -/
theorem nuclear_tsum_operator {ι : Type*}
    (u v : ι → H)
    (hcost : Summable (fun i : ι => ‖u i‖ * ‖v i‖)) :
    ((∑' i : ι, rankOneS1 (u i) (v i)) :
      ProbabilisticTheory.TraceClass H).1 =
       ∑' i : ι, (rankOne ℂ (u i) (v i) : H →L[ℂ] H) := by
  have hS1 : Summable (fun i : ι => rankOneS1 (u i) (v i)) := by
    apply Summable.of_norm
    exact hcost.congr (fun i => (rankOneS1_norm_eq (u i) (v i)).symm)
  have hOp : Summable
      (fun i : ι => (rankOne ℂ (u i) (v i) : H →L[ℂ] H)) := by
    apply Summable.of_norm
    simpa only [norm_rankOne] using hcost
  have hMapped := hS1.hasSum.mapL operatorCLM
  have heq :
      (fun i : ι => operatorCLM (rankOneS1 (u i) (v i))) =
        (fun i : ι => (rankOne ℂ (u i) (v i) : H →L[ℂ] H)) := by
    funext i
    exact rankOneS1_operator (u i) (v i)
  rw [heq] at hMapped
  have hValue := hMapped.tsum_eq
  exact hValue.symm

/-- THE REVERSE NUCLEAR REPRESENTATION for every actual CFC S₁ map:
there exist arbitrary Hilbert vectors uᵢ,vᵢ, with absolutely summable
nuclear costs, whose true Schatten S₁ rank-one series is exactly T.
The basis index may be an arbitrary set of Hilbert vectors. -/
theorem traceClass_nuclear_representation
    (T : ProbabilisticTheory.TraceClass H) :
    ∃ (w : Set H) (c : HilbertBasis w ℂ H)
        (u v : w → H),
      Summable (fun i : w => ‖u i‖ * ‖v i‖) ∧
      (∑' i : w, rankOneS1 (u i) (v i)) = T := by
  obtain ⟨R, S, hR, hS, hRS⟩ :=
    ProbabilisticTheory.traceClass_exists_HS_mul_HS T.1 T.2
  obtain ⟨w, c, hRsum⟩ := hR
  have hSstar : ProbabilisticTheory.HilbertSchmidt.IsHilbertSchmidt S.adjoint :=
    ProbabilisticTheory.HilbertSchmidt.isHilbertSchmidt_adjoint S hS
  have hSstarSum :
      Summable (fun i : w => ‖S.adjoint (c i)‖ ^ 2) :=
    ProbabilisticTheory.HilbertSchmidt.summable_norm_sq_apply_of_hilbertBasis
      w c hSstar
  let u : w → H := fun i => R (c i)
  let v : w → H := fun i => S.adjoint (c i)
  have hcost : Summable (fun i : w => ‖u i‖ * ‖v i‖) := by
    apply Summable.of_nonneg_of_le
    · intro i
      positivity
    · intro i
      change ‖R (c i)‖ * ‖S.adjoint (c i)‖ ≤
        ‖R (c i)‖ ^ 2 + ‖S.adjoint (c i)‖ ^ 2
      nlinarith [sq_nonneg (‖R (c i)‖ - ‖S.adjoint (c i)‖),
        sq_nonneg (‖R (c i)‖),
        sq_nonneg (‖S.adjoint (c i)‖)]
    · exact hRsum.add hSstarSum
  have hOpSummable :
      Summable (fun i : w =>
        (rankOne ℂ (u i) (v i) : H →L[ℂ] H)) := by
    apply Summable.of_norm
    simpa only [norm_rankOne] using hcost
  have hOpSum :
      (∑' i : w, (rankOne ℂ (u i) (v i) : H →L[ℂ] H)) =
        R * S := by
    apply ContinuousLinearMap.ext
    intro x
    rw [tsum_apply hOpSummable x]
    have hMap := (c.hasSum_repr (S x)).mapL R
    have hterm (i : w) :
        (rankOne ℂ (u i) (v i)) x =
          R (c.repr (S x) i • c i) := by
      change inner ℂ (S.adjoint (c i)) x • R (c i) =
        R (c.repr (S x) i • c i)
      rw [map_smul, c.repr_apply_apply]
      rw [ContinuousLinearMap.adjoint_inner_left S x (c i)]
    have heq :
        (fun i : w => (rankOne ℂ (u i) (v i)) x) =
          (fun i : w => R (c.repr (S x) i • c i)) := by
      funext i
      exact hterm i
    rw [heq]
    exact hMap.tsum_eq
  refine ⟨w, c, u, v, hcost, ?_⟩
  apply Subtype.ext
  calc
    ((∑' i : w, rankOneS1 (u i) (v i)) :
        ProbabilisticTheory.TraceClass H).1 =
        ∑' i : w, (rankOne ℂ (u i) (v i) : H →L[ℂ] H) :=
      nuclear_tsum_operator u v hcost
    _ = R * S := hOpSum
    _ = T.1 := hRS

/-- Genuine S₁ finite-rank DENSITY:
each arbitrary CFC trace-class operator is the trace-norm limit
of a directed net of ACTUAL finite sums of rank-one Hilbert operators.
No self-adjointness, positivity or diagonalizability assumptions. -/
theorem traceClass_finiteRank_dense
    (T : ProbabilisticTheory.TraceClass H) :
    ∃ (w : Set H) (u v : w → H),
      Tendsto
        (fun s : Finset w => ∑ i ∈ s, rankOneS1 (u i) (v i))
        atTop (𝓝 T) := by
  obtain ⟨w, c, u, v, hcost, heq⟩ :=
    traceClass_nuclear_representation T
  have hterms : Summable (fun i : w => rankOneS1 (u i) (v i)) := by
    apply Summable.of_norm
    exact hcost.congr (fun i => (rankOneS1_norm_eq (u i) (v i)).symm)
  refine ⟨w, u, v, ?_⟩
  rw [← heq]
  exact hterms.hasSum

#print axioms Manuscript14Priority3.NuclearRankOne.operatorCLM_apply
#print axioms Manuscript14Priority3.NuclearRankOne.nuclear_finset_operator
#print axioms Manuscript14Priority3.NuclearRankOne.nuclear_tsum_operator
#print axioms Manuscript14Priority3.NuclearRankOne.traceClass_nuclear_representation
#print axioms Manuscript14Priority3.NuclearRankOne.traceClass_finiteRank_dense

end Manuscript14Priority3.NuclearRankOne
