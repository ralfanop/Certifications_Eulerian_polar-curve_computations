import SpecialImaginaryPoint.V14119Priority3UniversalNuclearDensity
import GegenbauerFock.PhyslibTraceNormSqrtAbsEnergy
import GegenbauerFock.PhyslibTraceClassHSFactorization

/-!
# Manuscript 14.119 Priority 3 — optimal nuclear cost equals true CFC S₁ norm

For arbitrary nonnormal, nonpositive, non-diagonal genuine CFC-S₁
Hilbert maps, sharpen the certified universal nuclear representation
to a decomposition with EXACTLY OPTIMAL nuclear mass

   T = ∑ᵢ |uᵢ⟩⟨vᵢ|     (convergence in true CFC S₁),
   ∑ᵢ ‖uᵢ‖ ‖vᵢ‖ = ‖T‖₁.

The upper bound uses the specific canonical polar factorization
T=UQ², Q=sqrt(|T|), and pointwise contraction
‖U(Qeᵢ)‖ ≤ ‖Qeᵢ‖. Thus the cost is bounded by the exact
squared HS energy Σ‖Qeᵢ‖², already certified equal to the
source-compatible CFC trace norm on EVERY Hilbert basis.

The lower bound is valid for EVERY absolutely summable rank-one
representation and is immediate from actual S₁ triangle inequality
and the exact rank-one trace-norm formula. Together these
statements prove optimal nuclear cost equals genuine trace norm,
not only that CFC S₁ is a subspace of nuclear operators.

This is the missing optimal-nuclear-norm bridge for uniform
Fredholm determinant perturbation estimates. The determinant
perturbation inequality itself is NOT asserted here.
-/

noncomputable section

namespace Manuscript14Priority3.NuclearRankOne

open Filter Topology InnerProductSpace
open scoped ComplexOrder lp
open Manuscript14Priority3.TraceClassModel

/-- Every absolutely summable rank-one representation of an
ACTUAL CFC-S₁ map has nuclear cost at least its true CFC
trace norm. No positivity, diagonality or orthogonality needed. -/
theorem nuclear_mass_ge_traceNorm
    {ι : Type*} (u v : ι → H)
    (hcost : Summable (fun i : ι => ‖u i‖ * ‖v i‖))
    (T : ProbabilisticTheory.TraceClass H)
    (hT : (∑' i : ι, rankOneS1 (u i) (v i)) = T) :
    ‖T‖ ≤ ∑' i : ι, ‖u i‖ * ‖v i‖ := by
  have hsum : Summable (fun i : ι => rankOneS1 (u i) (v i)) := by
    apply Summable.of_norm
    exact hcost.congr (fun i => (rankOneS1_norm_eq (u i) (v i)).symm)
  calc
    ‖T‖ = ‖∑' i : ι, rankOneS1 (u i) (v i)‖ := by rw [hT]
    _ ≤ ∑' i : ι, ‖rankOneS1 (u i) (v i)‖ :=
      norm_tsum_le_tsum_norm hsum.norm
    _ = ∑' i : ι, ‖u i‖ * ‖v i‖ := by
      apply tsum_congr
      intro i
      exact rankOneS1_norm_eq (u i) (v i)

/-- CANONICAL POLAR nuclear decomposition with cost at most
the true CFC Schatten-S₁ norm. The witnessing basis is the
actual complete Hilbert basis from the trace-class witness,
and the rank-one series converges in the actual CFC S₁ Banach norm. -/
theorem traceClass_exists_nuclear_cost_le_traceNorm
    (T : ProbabilisticTheory.TraceClass H) :
    ∃ (w : Set H) (c : HilbertBasis w ℂ H)
        (u v : w → H),
      Summable (fun i : w => ‖u i‖ * ‖v i‖) ∧
      (∑' i : w, rankOneS1 (u i) (v i)) = T ∧
      (∑' i : w, ‖u i‖ * ‖v i‖) ≤ ‖T‖ := by
  let Q : H →L[ℂ] H := CFC.sqrt (CFC.abs T.1)
  let U : H →L[ℂ] H := Polar.polarFactor T.1
  let R : H →L[ℂ] H := U * Q
  let S : H →L[ℂ] H := Q
  let w : Set H := T.2.choose
  let c : HilbertBasis w ℂ H := T.2.choose_spec.choose
  have hQselfadjoint : IsSelfAdjoint Q :=
    IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (CFC.abs T.1))
  have hQstar : Q.adjoint = Q :=
    (ContinuousLinearMap.star_eq_adjoint Q).symm.trans hQselfadjoint
  have hQsum : Summable (fun i : w => ‖Q (c i)‖ ^ 2) :=
    ProbabilisticTheory.summable_sqrt_abs_basisEnergy T.1 T.2 c
  have henergy :
      (∑' i : w, ‖Q (c i)‖ ^ 2) = ‖T‖ := by
    calc
      (∑' i : w, ‖Q (c i)‖ ^ 2) =
          ProbabilisticTheory.traceNorm T.1 T.2 :=
        (ProbabilisticTheory.traceNorm_eq_sqrt_abs_basisEnergy
          T.1 T.2 c).symm
      _ = ‖T‖ :=
        (ProbabilisticTheory.TraceClass.norm_eq_genuineTraceNorm T).symm
  have hQQ : Q * Q = CFC.abs T.1 :=
    CFC.sqrt_mul_sqrt_self (CFC.abs T.1) (CFC.abs_nonneg T.1)
  have hRS : R * S = T.1 := by
    calc
      R * S = U * (Q * Q) := by simp only [R, S, mul_assoc]
      _ = U * CFC.abs T.1 := by rw [hQQ]
      _ = T.1 := Polar.polarFactor_mul_absOperator T.1
  let u : w → H := fun i => R (c i)
  let v : w → H := fun i => S.adjoint (c i)
  have hv (i : w) : v i = Q (c i) := by
    change Q.adjoint (c i) = Q (c i)
    rw [hQstar]
  have hu (i : w) : u i = U (Q (c i)) := rfl
  have hpoint (i : w) :
      ‖u i‖ * ‖v i‖ ≤ ‖Q (c i)‖ ^ 2 := by
    calc
      ‖u i‖ * ‖v i‖ =
          ‖U (Q (c i))‖ * ‖Q (c i)‖ := by rw [hu, hv]
      _ ≤ ‖Q (c i)‖ * ‖Q (c i)‖ :=
        mul_le_mul_of_nonneg_right
          (Polar.polarFactor_norm_le T.1 (Q (c i)))
          (norm_nonneg _)
      _ = ‖Q (c i)‖ ^ 2 := by ring
  have hcost : Summable (fun i : w => ‖u i‖ * ‖v i‖) := by
    apply Summable.of_nonneg_of_le
    · intro i
      positivity
    · exact hpoint
    · exact hQsum
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
  have hTsum :
      (∑' i : w, rankOneS1 (u i) (v i)) = T := by
    apply Subtype.ext
    calc
      ((∑' i : w, rankOneS1 (u i) (v i)) :
          ProbabilisticTheory.TraceClass H).1 =
          ∑' i : w, (rankOne ℂ (u i) (v i) : H →L[ℂ] H) :=
        nuclear_tsum_operator u v hcost
      _ = R * S := hOpSum
      _ = T.1 := hRS
  have hmass :
      (∑' i : w, ‖u i‖ * ‖v i‖) ≤ ‖T‖ := by
    calc
      (∑' i : w, ‖u i‖ * ‖v i‖) ≤
          ∑' i : w, ‖Q (c i)‖ ^ 2 :=
        hcost.tsum_le_tsum hpoint hQsum
      _ = ‖T‖ := henergy
  exact ⟨w, c, u, v, hcost, hTsum, hmass⟩

/-- Optimal nuclear mass of an arbitrary, potentially nonnormal
complex CFC Schatten-S₁ map is EXACTLY its genuine CFC trace norm.
No spectral diagonalization, finite-dimensional replacement or
nonstandard axioms are involved. -/
theorem traceClass_exists_optimal_nuclear_representation
    (T : ProbabilisticTheory.TraceClass H) :
    ∃ (w : Set H) (c : HilbertBasis w ℂ H)
        (u v : w → H),
      Summable (fun i : w => ‖u i‖ * ‖v i‖) ∧
      (∑' i : w, rankOneS1 (u i) (v i)) = T ∧
      (∑' i : w, ‖u i‖ * ‖v i‖) = ‖T‖ := by
  obtain ⟨w, c, u, v, hcost, hTsum, hle⟩ :=
    traceClass_exists_nuclear_cost_le_traceNorm T
  have hge := nuclear_mass_ge_traceNorm u v hcost T hTsum
  exact ⟨w, c, u, v, hcost, hTsum, le_antisymm hle hge⟩

#print axioms Manuscript14Priority3.NuclearRankOne.nuclear_mass_ge_traceNorm
#print axioms Manuscript14Priority3.NuclearRankOne.traceClass_exists_nuclear_cost_le_traceNorm
#print axioms Manuscript14Priority3.NuclearRankOne.traceClass_exists_optimal_nuclear_representation

end Manuscript14Priority3.NuclearRankOne
