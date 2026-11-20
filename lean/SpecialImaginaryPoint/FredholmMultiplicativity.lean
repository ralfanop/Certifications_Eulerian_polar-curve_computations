import SharedCore.FiniteFredholmProduct
import SpecialImaginaryPoint.V14119Priority3UniversalFredholmComplexScaleCovariance
import SpecialImaginaryPoint.V14119Priority3FiniteNuclearConcatenation
import GegenbauerFock.PhyslibTraceClassComplexNonUnitalAlgebra
import GegenbauerFock.PhyslibTraceClassSandwichContinuous

/-!
# Multiplicativity of the genuine CFC Fredholm determinant

The finite proof factors a joined Gram matrix into block triangular
matrices. Density in the actual trace norm and continuous multiplication
then extend the identity to arbitrary nonnormal trace-class operators.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Manuscript14Priority3.FredholmMultiplicativity

open Filter Topology InnerProductSpace
open scoped InnerProductSpace
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.NuclearRankOne
open Manuscript14Priority3.FiniteNuclearFredholm
open Manuscript14Priority3.FiniteNuclearConcatenation
open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.UniversalFredholmJointVariation
open Manuscript14Priority3.UniversalFredholmComplexScaleCovariance
open ProbabilisticTheory.TraceClass

theorem left_rankOneS1 (A : H →L[ℂ] H) (u v : H) :
    sandwichContinuous A 1 (rankOneS1 u v) = rankOneS1 (A u) v := by
  apply Subtype.ext
  rw [sandwichContinuous_apply, sandwich_operator, rankOneS1_operator, rankOneS1_operator]
  ext x
  simp [rankOne_apply]

theorem left_finiteNuclear (A : H →L[ℂ] H) (m : ℕ) (u v : Fin m → H) :
    sandwichContinuous A 1 (finiteNuclear m u v) =
      finiteNuclear m (fun i => A (u i)) v := by
  simp only [finiteNuclear, map_sum, left_rankOneS1]

theorem joined_finiteNuclear_product (m n : ℕ) (u v : Fin m → H) (x y : Fin n → H) :
    finiteNuclear (m + n) (Fin.append u
      (fun j => x j + SharedCore.FiniteFredholmProduct.nuclearOp u v (x j)))
      (Fin.append v y) = finiteNuclear m u v + finiteNuclear n x y +
        finiteNuclear m u v * finiteNuclear n x y := by
  have hu : (fun j => x j + SharedCore.FiniteFredholmProduct.nuclearOp u v (x j)) =
      (fun j => (1 + (finiteNuclear m u v).1) (x j)) := by
    funext j
    rw [finiteNuclear_operator]
    rfl
  rw [finiteNuclear_append_eq_add, hu, ← left_finiteNuclear]
  apply Subtype.ext
  change (finiteNuclear m u v).1 +
      (1 + (finiteNuclear m u v).1) * (finiteNuclear n x y).1 * 1 =
    ((finiteNuclear m u v).1 + (finiteNuclear n x y).1) +
      (finiteNuclear m u v).1 * (finiteNuclear n x y).1
  noncomm_ring

theorem fredholmDet_mul_finite (m n : ℕ) (u v : Fin m → H) (x y : Fin n → H) :
    fredholmDet (finiteNuclear m u v + finiteNuclear n x y +
      finiteNuclear m u v * finiteNuclear n x y) 1 =
      fredholmDet (finiteNuclear m u v) 1 * fredholmDet (finiteNuclear n x y) 1 := by
  rw [← joined_finiteNuclear_product, fredholmDet_finiteNuclear,
    fredholmDet_finiteNuclear, fredholmDet_finiteNuclear]
  have hgram (k : ℕ) (a b : Fin k → H) :
      Manuscript14Priority3.FiniteNuclearFredholm.gram k a b =
        SharedCore.FiniteFredholmProduct.pairingMatrix b a := rfl
  simp only [one_smul, hgram]
  exact SharedCore.FiniteFredholmProduct.joined_gram_det u v x y

theorem fredholmDet_continuous_operator :
    Continuous (fun T : ProbabilisticTheory.TraceClass H => fredholmDet T 1) := by
  apply continuous_iff_continuousAt.mpr
  intro S
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hb (T : ProbabilisticTheory.TraceClass H) :
      ‖fredholmDet T 1 - fredholmDet S 1‖ ≤ ‖T - S‖ * Real.exp (‖S‖ + ‖T - S‖) := by
    simpa only [norm_one, one_mul] using universalFredholm_two_operators_diff_norm_le T S 1
  have hn : Continuous (fun T : ProbabilisticTheory.TraceClass H => ‖T - S‖) :=
    (continuous_id.sub continuous_const).norm
  have hc : Continuous (fun T : ProbabilisticTheory.TraceClass H =>
      ‖T - S‖ * Real.exp (‖S‖ + ‖T - S‖)) :=
    hn.mul (Real.continuous_exp.comp (continuous_const.add hn))
  have hlim : Tendsto (fun T : ProbabilisticTheory.TraceClass H =>
      ‖T - S‖ * Real.exp (‖S‖ + ‖T - S‖)) (𝓝 S) (𝓝 0) := by
    simpa using hc.tendsto S
  exact squeeze_zero (fun T => norm_nonneg _) hb hlim

/-- Genuine multiplicativity for every two CFC trace-class operators.
The identity operator is used only in B(H), never asserted to be S₁. -/
theorem fredholmDet_multiplicative (T S : ProbabilisticTheory.TraceClass H) :
    fredholmDet (T + S + T * S) 1 = fredholmDet T 1 * fredholmDet S 1 := by
  have hfinite (T : ProbabilisticTheory.TraceClass H) (hT : T ∈ finiteSector) :
      ∀ S : ProbabilisticTheory.TraceClass H,
        fredholmDet (T + S + T * S) 1 = fredholmDet T 1 * fredholmDet S 1 := by
    obtain ⟨m, u, v, rfl⟩ := hT
    intro S
    refine finiteSector_dense.induction
      (P := fun S => fredholmDet (finiteNuclear m u v + S + finiteNuclear m u v * S) 1 =
        fredholmDet (finiteNuclear m u v) 1 * fredholmDet S 1) ?_ ?_ S
    · rintro S ⟨n, x, y, rfl⟩
      exact fredholmDet_mul_finite m n u v x y
    · exact isClosed_eq
        (fredholmDet_continuous_operator.comp
          ((continuous_const.add continuous_id).add (continuous_const.mul continuous_id)))
        (continuous_const.mul fredholmDet_continuous_operator)
  refine finiteSector_dense.induction
    (P := fun T => fredholmDet (T + S + T * S) 1 = fredholmDet T 1 * fredholmDet S 1)
    (fun T hT => hfinite T hT S) ?_ T
  exact isClosed_eq
    (fredholmDet_continuous_operator.comp
      ((continuous_id.add continuous_const).add (continuous_id.mul continuous_const)))
    (fredholmDet_continuous_operator.mul continuous_const)

theorem fredholmDet_zero_operator : fredholmDet (0 : ProbabilisticTheory.TraceClass H) 1 = 1 := by
  simpa only [zero_smul, mul_zero, fredholmDet_zero] using
    universalFredholm_operator_smul (0 : ProbabilisticTheory.TraceClass H) 0 1

#print axioms left_rankOneS1
#print axioms left_finiteNuclear
#print axioms joined_finiteNuclear_product
#print axioms fredholmDet_mul_finite
#print axioms fredholmDet_continuous_operator
#print axioms fredholmDet_multiplicative
#print axioms fredholmDet_zero_operator

end Manuscript14Priority3.FredholmMultiplicativity
