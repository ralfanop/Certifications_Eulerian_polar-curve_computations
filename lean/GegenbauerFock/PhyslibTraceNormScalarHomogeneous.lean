import GegenbauerFock.PhyslibTraceBasisIndependence
import GegenbauerFock.PhyslibTraceClassScalar

/-!
# V007 — homogeneous CFC trace norm for arbitrary S1 operators

The basis-independent trace-norm theorem permits comparison of
`traceNorm (c • T)` and `traceNorm T` on ONE common arbitrary complete
Hilbert basis.  Together with `CFC.abs_smul` this establishes genuine
complex absolute homogeneity of the Physlib-compatible trace norm on
the *entire* (possibly non-selfadjoint) trace class.

No general additive closure or trace-norm triangle inequality is used
or claimed.  This module is a new independent extension of the S1
foundation and does not change earlier approved V007 checkpoints.
-/

noncomputable section

namespace ProbabilisticTheory

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Exact complex absolute homogeneity of the infinite-dimensional
CFC trace norm, for arbitrary (not necessarily positive) S1 maps. -/
theorem traceNorm_smul_general (c : ℂ) (T : H →L[ℂ] H)
    (hT : IsTraceClass T) :
    traceNorm (c • T) (isTraceClass_smul c hT) =
      ‖c‖ * traceNorm T hT := by
  let b := hT.choose_spec.choose
  have habs : CFC.abs (c • T) = ‖c‖ • CFC.abs T :=
    CFC.abs_smul c T
  have hdiag (i : hT.choose) :
      (inner ℂ (b i) (CFC.abs (c • T) (b i))).re =
        ‖c‖ * (inner ℂ (b i) (CFC.abs T (b i))).re := by
    rw [habs, smul_apply,
      RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_right]
    simp [Complex.mul_re]
  calc
    traceNorm (c • T) (isTraceClass_smul c hT) =
        ∑' i : hT.choose,
          (inner ℂ (b i) (CFC.abs (c • T) (b i))).re :=
      traceNorm_eq_of_hilbertBasis (isTraceClass_smul c hT) b
    _ = ∑' i : hT.choose,
          ‖c‖ * (inner ℂ (b i) (CFC.abs T (b i))).re := by
      apply tsum_congr
      intro i
      exact hdiag i
    _ = ‖c‖ * (∑' i : hT.choose,
          (inner ℂ (b i) (CFC.abs T (b i))).re) := tsum_mul_left
    _ = ‖c‖ * traceNorm T hT := by
      rw [← traceNorm_eq_of_hilbertBasis hT b]

/-- The exact CFC trace norm is invariant under additive negation,
for every trace-class operator on every complete complex Hilbert space. -/
theorem traceNorm_neg_general (T : H →L[ℂ] H)
    (hT : IsTraceClass T) :
    traceNorm (-T) (isTraceClass_neg hT) = traceNorm T hT := by
  have h := traceNorm_smul_general (-1 : ℂ) T hT
  simpa only [neg_one_smul, norm_neg, norm_one, one_mul] using h

#print axioms ProbabilisticTheory.traceNorm_smul_general
#print axioms ProbabilisticTheory.traceNorm_neg_general

end ProbabilisticTheory

namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Exact absolute homogeneity for the proof-carrying S1 carrier. -/
theorem traceNorm_smul_general (c : ℂ) (T : TraceClass H) :
    traceNorm H (c • T) = ‖c‖ * traceNorm H T :=
  ProbabilisticTheory.traceNorm_smul_general c T.1 T.2

#print axioms ProbabilisticTheory.TraceClass.traceNorm_smul_general

end ProbabilisticTheory.TraceClass
