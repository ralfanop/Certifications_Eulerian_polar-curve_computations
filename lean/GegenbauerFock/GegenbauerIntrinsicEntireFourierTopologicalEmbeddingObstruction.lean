import GegenbauerFock.GegenbauerIntrinsicEntireFourierProductTopologyNoInverse
import GegenbauerFock.GegenbauerIntrinsicEntireFourierUniqueness

/-!
# V007 — a continuous injective Fourier transform which is not continuously invertible

The genuine ultraspherical Fourier–Bochner integral, without coefficient
surrogates, maps the full ultraspherical L² Hilbert space continuously
into complex-valued functions on the ENTIRE complex plane, equipped
with their product (pointwise-convergence) topology.

The map is rigorously injective, since these original complex Fourier
data uniquely determine the source. Nevertheless no globally defined
(even nonlinear) left inverse to this map is continuous at the zero
function. This precise distinction between continuous forward data,
exact uniqueness, and inverse instability is proved using the true
Bochner formula, continuity of the entire coherent evaluation, and
the separately established normalized approximate-null source sequence.

No finite-sample injectivity, surjectivity, or stable source
reconstruction is asserted.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The ACTUAL ultraspherical Fourier–Bochner transform is a continuous
map into all complex functions equipped with the pointwise topology. -/
theorem ultraspherical_fourierBochner_productTopology_continuous
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    Continuous (ultraspherical_fourierBochner_function lam) := by
  apply continuous_pi
  intro z
  have hfunc :
      (fun f : Lp ℂ 2 (Ultraspherical.measure lam) =>
        ultraspherical_fourierBochner_function lam f z) =
      (fun f : Lp ℂ 2 (Ultraspherical.measure lam) =>
        FockEvaluation.evaluation alpha ha z (C lam alpha hlam ha f)) := by
    funext f
    exact (evaluatedOperator_eq_integral lam alpha hlam ha z f).symm
  rw [hfunc]
  exact (FockEvaluation.evaluation alpha ha z).continuous.comp
    (C lam alpha hlam ha).continuous

/-- The genuine Fourier–Bochner integral separates all ultraspherical
L² source classes; the full complex Fourier function is injective. -/
theorem ultraspherical_fourierBochner_productTopology_injective
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    Function.Injective (ultraspherical_fourierBochner_function lam) := by
  intro f g h
  apply ultraspherical_fourierBochner_injective lam alpha hlam ha f g
  intro z
  exact congrFun h z

/-- A complete genuine Fourier–Bochner transform can be continuous and
injective without admitting a continuous inverse, even allowing
nonlinear reconstruction from ALL complex frequencies. -/
theorem ultraspherical_fourierBochner_continuous_injective_inverse_unstable
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    Continuous (ultraspherical_fourierBochner_function lam) ∧
    Function.Injective (ultraspherical_fourierBochner_function lam) ∧
    ¬ ∃ r : (ℂ → ℂ) → Lp ℂ 2 (Ultraspherical.measure lam),
      Continuous r ∧
      ∀ f : Lp ℂ 2 (Ultraspherical.measure lam),
        r (ultraspherical_fourierBochner_function lam f) = f := by
  exact ⟨ultraspherical_fourierBochner_productTopology_continuous
      lam alpha hlam ha,
    ultraspherical_fourierBochner_productTopology_injective
      lam alpha hlam ha,
    ultraspherical_fourierBochner_no_continuous_global_reconstruction
      lam alpha hlam ha⟩

#print axioms GegenbauerFock.GeneralUltrasphericalFock.ultraspherical_fourierBochner_productTopology_continuous
#print axioms GegenbauerFock.GeneralUltrasphericalFock.ultraspherical_fourierBochner_productTopology_injective
#print axioms GegenbauerFock.GeneralUltrasphericalFock.ultraspherical_fourierBochner_continuous_injective_inverse_unstable

end GegenbauerFock.GeneralUltrasphericalFock
