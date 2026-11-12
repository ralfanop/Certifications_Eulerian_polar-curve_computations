import SpecialImaginaryPoint.V14119Priority3UniversalFredholmEntire
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Priority 3 — every zero of the genuine universal trace-class Fredholm determinant is isolated

For EVERY genuine complex CFC Schatten-S₁ Hilbert operator T,
including nonnormal, nonselfadjoint and noninvertible examples,
its universal Fredholm determinant z ↦ det_F(I+zT) is entire and
satisfies det_F(I)=1.

It follows, without any spectral enumeration or positivity
hypothesis, that its zero set has NO finite accumulation point:
at every complex spectral parameter z₀, the determinant is nonzero
throughout a sufficiently small punctured neighborhood of z₀.

The proof is not the vacuous local dichotomy for arbitrary analytic
functions. It EXCLUDES the identically-zero germ by the global
identity theorem on the connected complex plane and the independent
normalization at zero. The only axioms are standard Lean/Mathlib axioms.
-/

noncomputable section

namespace Manuscript14Priority3.UniversalIsolatedSpectralZeros

open Filter Topology Set
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.UniversalFredholmEntire

/-- For an arbitrary actual infinite-dimensional CFC Schatten-S₁
operator, every Fredholm determinant zero is isolated. More strongly,
the determinant has no other zeros near ANY fixed spectral point
once that fixed point itself is removed. -/
theorem universal_fredholmDet_eventually_ne_zero_punctured
    (T : ProbabilisticTheory.TraceClass H) (z₀ : ℂ) :
    ∀ᶠ z in 𝓝[≠] z₀, fredholmDet T z ≠ 0 := by
  have hanalytic : AnalyticOnNhd ℂ (fredholmDet T) Set.univ :=
    (universal_fredholmDet_entire T).differentiableOn.analyticOnNhd
      isOpen_univ
  rcases (hanalytic z₀ (Set.mem_univ z₀)).eventually_eq_zero_or_eventually_ne_zero
      with hvanishes | hnonzero
  · have hidentically :
        EqOn (fredholmDet T) 0 Set.univ :=
      hanalytic.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        isPreconnected_univ (Set.mem_univ z₀) hvanishes
    have hzero : fredholmDet T 0 = (0 : ℂ) :=
      hidentically (Set.mem_univ (0 : ℂ))
    rw [fredholmDet_zero] at hzero
    exact (one_ne_zero hzero).elim
  · exact hnonzero

#print axioms Manuscript14Priority3.UniversalIsolatedSpectralZeros.universal_fredholmDet_eventually_ne_zero_punctured

end Manuscript14Priority3.UniversalIsolatedSpectralZeros
