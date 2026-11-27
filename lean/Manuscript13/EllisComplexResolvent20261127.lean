import Mathlib
import Manuscript13.EllisParsevalTonelli20261126
import Manuscript13.MellinPlancherelMultiplier20261124

/-! M13 Corollary 4.12 (74)–(77), source 13/13.tex of
Manuscript_13_20261126_PROP44_EQ50_SPACING(2).zip.
Actual complex L² Fourier multiplier realization of the shifted
free Laplacian, and actual weighted operator. The domain is the
Fourier graph (not yet identified with weak-derivative H²).
The identification with the Green convolution, complex trace-class
spectral theorem and Fredholm product remain separate obligations.
-/
open MeasureTheory Filter Set
namespace Manuscript13.EllisComplexResolvent20261127
noncomputable section
open Manuscript13.MellinPlancherelMultiplier20261124 (mulOperator mulOperator_ae mulOperator_norm_le)
open Manuscript13.EllisFourier20261124 (potential)
open Manuscript13.EllisBirman20261124 (potential_nonneg)
abbrev H := Lp ℂ 2 (volume : Measure ℝ)

def fourier : H ≃ₗᵢ[ℂ] H := Lp.fourierTransformₗᵢ ℝ ℂ

def symbol (κ x : ℝ) : ℝ := (2 * Real.pi * x)^2 + κ^2

theorem symbol_pos (κ x : ℝ) (hk : 0 < κ) : 0 < symbol κ x := by
  unfold symbol
  positivity

def multiplier (κ x : ℝ) : ℂ := ((1 / symbol κ x : ℝ) : ℂ)

theorem multiplier_measurable (κ : ℝ) : Measurable (multiplier κ) := by
  unfold multiplier symbol
  fun_prop

theorem multiplier_bound (κ : ℝ) (hk : 0 < κ) (x : ℝ) :
    ‖multiplier κ x‖ ≤ 1 / κ^2 := by
  rw [multiplier, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg zero_le_one (symbol_pos κ x hk).le)]
  apply one_div_le_one_div_of_le (by positivity : 0 < κ^2)
  unfold symbol
  nlinarith [sq_nonneg (2 * Real.pi * x)]

theorem symbol_mul_multiplier (κ x : ℝ) (hk : 0 < κ) :
    (symbol κ x : ℂ) * multiplier κ x = 1 := by
  have hs : symbol κ x ≠ 0 := ne_of_gt (symbol_pos κ x hk)
  unfold multiplier
  push_cast
  field_simp [hs]

def spectralResolvent (κ : ℝ) (hk : 0 < κ) : H →L[ℂ] H :=
  mulOperator (multiplier κ) (multiplier_measurable κ) (1 / κ^2)
    (by positivity) (Eventually.of_forall (multiplier_bound κ hk))

def freeResolvent (κ : ℝ) (hk : 0 < κ) : H →L[ℂ] H :=
  fourier.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((spectralResolvent κ hk).comp fourier.toContinuousLinearEquiv.toContinuousLinearMap)

theorem freeResolvent_apply (κ : ℝ) (hk : 0 < κ) (f : H) :
    freeResolvent κ hk f = fourier.symm (spectralResolvent κ hk (fourier f)) := rfl

theorem freeResolvent_fourier_ae (κ : ℝ) (hk : 0 < κ) (f : H) :
    (fun x => fourier (freeResolvent κ hk f) x) =ᵐ[volume]
      (fun x => multiplier κ x * fourier f x) := by
  rw [freeResolvent_apply, LinearIsometryEquiv.apply_symm_apply]
  exact mulOperator_ae _ _ _ _ _ _

theorem freeResolvent_norm_le (κ : ℝ) (hk : 0 < κ) :
    ‖freeResolvent κ hk‖ ≤ 1 / κ^2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  rw [freeResolvent_apply, fourier.symm.norm_map]
  calc
    _ ≤ ‖spectralResolvent κ hk‖ * ‖fourier f‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ (1 / κ^2) * ‖f‖ := by
      rw [fourier.norm_map]
      exact mul_le_mul_of_nonneg_right (mulOperator_norm_le _ _ _ _ _) (norm_nonneg _)

/-- The graph of the shifted free operator in Fourier variables. -/
def shiftedGraph (κ : ℝ) (u f : H) : Prop :=
  (fun x => (symbol κ x : ℂ) * fourier u x) =ᵐ[volume] (fun x => fourier f x)

theorem freeResolvent_graph (κ : ℝ) (hk : 0 < κ) (f : H) :
    shiftedGraph κ (freeResolvent κ hk f) f := by
  unfold shiftedGraph
  filter_upwards [freeResolvent_fourier_ae κ hk f] with x hx
  rw [hx, ← mul_assoc, symbol_mul_multiplier κ x hk, one_mul]

theorem freeResolvent_graph_unique (κ : ℝ) (hk : 0 < κ) (u f : H)
    (h : shiftedGraph κ u f) : u = freeResolvent κ hk f := by
  apply fourier.injective
  apply Lp.ext
  filter_upwards [h, freeResolvent_fourier_ae κ hk f] with x hx hy
  rw [hy, ← hx, ← mul_assoc, mul_comm (multiplier κ x) (symbol κ x : ℂ),
    symbol_mul_multiplier κ x hk, one_mul]

def weight (a x : ℝ) : ℂ := (Real.sqrt (potential a x) : ℂ)

theorem weight_measurable (a : ℝ) : Measurable (weight a) := by
  unfold weight potential
  fun_prop

theorem potential_bound (a x : ℝ) (ha : 0 < a) :
    potential a x ≤ 1 / a^2 := by
  unfold potential
  apply (div_le_div_iff₀ (by positivity : 0 < (x^2+a^2)^2)
    (by positivity : 0 < a^2)).2
  nlinarith [sq_nonneg x, sq_nonneg (x^2), mul_nonneg (sq_nonneg x) (sq_nonneg a)]

theorem weight_bound (a x : ℝ) (ha : 0 < a) :
    ‖weight a x‖ ≤ 1 / a := by
  rw [weight, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have h := potential_bound a x ha
  have he : (1 / a)^2 = 1 / a^2 := by ring
  have hp : 0 ≤ 1 / a := by positivity
  nlinarith [Real.sq_sqrt (potential_nonneg a x), Real.sqrt_nonneg (potential a x)]

def weightOperator (a : ℝ) (ha : 0 < a) : H →L[ℂ] H :=
  mulOperator (weight a) (weight_measurable a) (1 / a) (by positivity)
    (Eventually.of_forall (fun x => weight_bound a x ha))

theorem weightOperator_ae (a : ℝ) (ha : 0 < a) (f : H) :
    (fun x => weightOperator a ha f x) =ᵐ[volume] (fun x => weight a x * f x) :=
  mulOperator_ae _ _ _ _ _ _

def birmanSchwinger (a κ : ℝ) (ha : 0 < a) (hk : 0 < κ) : H →L[ℂ] H :=
  (weightOperator a ha).comp ((freeResolvent κ hk).comp (weightOperator a ha))

theorem birmanSchwinger_apply (a κ : ℝ) (ha : 0 < a) (hk : 0 < κ) (f : H) :
    birmanSchwinger a κ ha hk f =
      weightOperator a ha (freeResolvent κ hk (weightOperator a ha f)) := rfl

end
end Manuscript13.EllisComplexResolvent20261127
#print axioms Manuscript13.EllisComplexResolvent20261127.fourier
#print axioms Manuscript13.EllisComplexResolvent20261127.symbol
#print axioms Manuscript13.EllisComplexResolvent20261127.symbol_pos
#print axioms Manuscript13.EllisComplexResolvent20261127.multiplier
#print axioms Manuscript13.EllisComplexResolvent20261127.multiplier_measurable
#print axioms Manuscript13.EllisComplexResolvent20261127.multiplier_bound
#print axioms Manuscript13.EllisComplexResolvent20261127.symbol_mul_multiplier
#print axioms Manuscript13.EllisComplexResolvent20261127.spectralResolvent
#print axioms Manuscript13.EllisComplexResolvent20261127.freeResolvent
#print axioms Manuscript13.EllisComplexResolvent20261127.freeResolvent_apply
#print axioms Manuscript13.EllisComplexResolvent20261127.freeResolvent_fourier_ae
#print axioms Manuscript13.EllisComplexResolvent20261127.freeResolvent_norm_le
#print axioms Manuscript13.EllisComplexResolvent20261127.shiftedGraph
#print axioms Manuscript13.EllisComplexResolvent20261127.freeResolvent_graph
#print axioms Manuscript13.EllisComplexResolvent20261127.freeResolvent_graph_unique
#print axioms Manuscript13.EllisComplexResolvent20261127.weight
#print axioms Manuscript13.EllisComplexResolvent20261127.weight_measurable
#print axioms Manuscript13.EllisComplexResolvent20261127.potential_bound
#print axioms Manuscript13.EllisComplexResolvent20261127.weight_bound
#print axioms Manuscript13.EllisComplexResolvent20261127.weightOperator
#print axioms Manuscript13.EllisComplexResolvent20261127.weightOperator_ae
#print axioms Manuscript13.EllisComplexResolvent20261127.birmanSchwinger
#print axioms Manuscript13.EllisComplexResolvent20261127.birmanSchwinger_apply
