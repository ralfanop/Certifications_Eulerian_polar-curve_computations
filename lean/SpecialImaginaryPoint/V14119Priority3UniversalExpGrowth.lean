import SpecialImaginaryPoint.V14119Priority3UniversalTraceNormContinuity
import SpecialImaginaryPoint.V14119Priority3FiniteGramEntireGrowth
import SpecialImaginaryPoint.V14119Priority3FinsetNuclearReindex

/-!
# Priority 3 — sharp universal exponential growth of the genuine CFC-S₁ Fredholm determinant

This establishes the full infinite-dimensional version of the sharp
dimension-free finite mixed Gram bound of PR #109:

  ‖det(I+zT)‖ ≤ exp(‖z‖ ‖T‖₁)

for EVERY genuine CFC Schatten-S₁ Hilbert operator T, all complex z,
and no normality, positivity, selfadjointness, finite-rank or
invertibility assumption.

The proof is not a formal replacement of nuclear cost by the trace
norm: it uses the certified EXISTENCE of an actual optimal polar
nuclear decomposition of any T and genuine finite truncations with
each presentation mass ≤ ‖T‖₁. The finite exponential estimate is
already kernel-certified; continuity of the UNIVERSAL determinant in
true trace norm lets us pass the bound to the actual operator T.

The finite-shift and infinite determinant theorem names differ, but
their mixed Gram matrices agree definitionally, entry by entry.
No dimension factors, nonstandard axioms, or background hypothesis.
-/

noncomputable section

namespace Manuscript14Priority3.UniversalExpGrowth

open Filter Topology
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.FiniteNuclearFredholm
open Manuscript14Priority3.FiniteGramEntireGrowth
open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.UniversalTraceNormContinuity
open Manuscript14Priority3.FinsetNuclearReindex

/-- Sharp dimension-free exponential bound, for the ACTUAL
finite-nuclear intrinsic CFC-S₁ Fredholm determinant, obtained
from the certified genuine mixed Gram bound. -/
theorem fredholmDet_finiteNuclear_growth (m : ℕ)
    (u v : Fin m → H) (z : ℂ) :
    ‖fredholmDet (finiteNuclear m u v) z‖ ≤
      Real.exp (‖z‖ * ∑ i : Fin m, ‖u i‖ * ‖v i‖) := by
  rw [fredholmDet_finiteNuclear]
  change
    ‖(1 + z • Manuscript14Priority3.ComplexGramMinorBridge.mixedGram u v).det‖ ≤
      Real.exp (‖z‖ * ∑ i : Fin m, ‖u i‖ * ‖v i‖)
  exact mixedGram_det_shift_norm_le_exp u v z

/-- The sharp, no-dimension-factor exponential determinant growth
bound on EVERY infinite-dimensional genuine CFC-S₁ operator.
The constant uses its EXACT trace norm, never a nonoptimal
representation cost. -/
theorem universal_fredholmDet_growth
    (T : ProbabilisticTheory.TraceClass H) (z : ℂ) :
    ‖fredholmDet T z‖ ≤ Real.exp (‖z‖ * ‖T‖) := by
  obtain ⟨w, u, v, _hcost, hlim, hmass⟩ :=
    traceClass_exists_optimal_fin_presentations T
  let A : Finset w → ProbabilisticTheory.TraceClass H :=
    fun s => finiteNuclear s.card
      (finsetVectors s u) (finsetVectors s v)
  have hlimit :
      Tendsto (fun s : Finset w => fredholmDet (A s) z)
        atTop (𝓝 (fredholmDet T z)) :=
    ((fredholmDet_continuous_traceNorm z).tendsto T).comp hlim
  have hbound (s : Finset w) :
      ‖fredholmDet (A s) z‖ ≤ Real.exp (‖z‖ * ‖T‖) := by
    have hfinite :=
      fredholmDet_finiteNuclear_growth s.card
        (finsetVectors s u) (finsetVectors s v) z
    have hscale :
        ‖z‖ * (∑ i : Fin s.card,
          ‖finsetVectors s u i‖ * ‖finsetVectors s v i‖) ≤
          ‖z‖ * ‖T‖ :=
      mul_le_mul_of_nonneg_left (hmass s) (norm_nonneg z)
    calc
      ‖fredholmDet (A s) z‖ ≤
          Real.exp (‖z‖ * ∑ i : Fin s.card,
            ‖finsetVectors s u i‖ * ‖finsetVectors s v i‖) := hfinite
      _ ≤ Real.exp (‖z‖ * ‖T‖) :=
        Real.exp_le_exp.mpr hscale
  exact le_of_tendsto hlimit.norm
    (Filter.Eventually.of_forall hbound)

#print axioms Manuscript14Priority3.UniversalExpGrowth.fredholmDet_finiteNuclear_growth
#print axioms Manuscript14Priority3.UniversalExpGrowth.universal_fredholmDet_growth

end Manuscript14Priority3.UniversalExpGrowth
