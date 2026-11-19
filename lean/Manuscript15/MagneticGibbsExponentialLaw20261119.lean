import Manuscript15.MagneticGibbsRounding20261117
import Mathlib.Probability.Distributions.Exponential

/-! M15 §8.4. Actual Mathlib exponential measure, exact odd-lattice
atom masses and sharp infinity-cost primal transport. The latter is
the infimum of the achievable almost-everywhere displacement bounds,
equivalently the usual infimum of essential suprema. No assertion
about convergence of the finite magnetic field laws is made. -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
noncomputable section
namespace Manuscript15.MagneticGibbs.Rounding
open Manuscript15.Section27.Primal
open Manuscript15.MagneticGibbs

theorem exp_measure_Iio_real (r : ℝ) (hr : 0 < r) (a : ℝ) :
    (expMeasure r).real (Iio a) =
      if 0 ≤ a then 1 - Real.exp (-(r*a)) else 0 := by
  letI : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  letI : NullSingletonClass (expMeasure r) := by
    unfold expMeasure gammaMeasure
    infer_instance
  have he : Iic a \ {a} = Iio a := by
    ext x
    simp only [mem_sdiff, mem_Iic, mem_singleton_iff, mem_Iio]
    exact lt_iff_le_and_ne.symm
  have hn : (expMeasure r).real {a} = 0 := by
    simp [measureReal_def]
  rw [← he, measureReal_sdiff_null hn, ← cdf_eq_real, cdf_expMeasure_eq hr]

theorem exp_measure_Ico_real (r : ℝ) (hr : 0 < r) (a b : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) :
    (expMeasure r).real (Ico a b) =
      Real.exp (-(r*a)) - Real.exp (-(r*b)) := by
  letI : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  have he : Iio b \ Iio a = Ico a b := by
    ext x
    simp only [mem_sdiff, mem_Iio, mem_Ico, not_lt]
    exact and_comm
  have hs : Iio a ⊆ Iio b := fun x hx => lt_of_lt_of_le hx hab
  rw [← he, measureReal_sdiff hs measurableSet_Iio,
    exp_measure_Iio_real r hr a, exp_measure_Iio_real r hr b,
    if_pos ha, if_pos (ha.trans hab)]
  ring

/-- Atom masses of the actual pushforward of the exponential law. -/
theorem exp_round_atom_real (r : ℝ) (hr : 0 < r) (k : ℕ) :
    (Measure.map roundEnergy (expMeasure r)).real {oddLevel (k:ℤ)} =
      Real.exp (-2*r*(k:ℝ)) - Real.exp (-2*r*((k:ℝ)+1)) := by
  simp only [measureReal_def, round_atom_mass]
  change (expMeasure r).real (Ico (2*((k:ℤ):ℝ)) (2*((k:ℤ):ℝ)+2)) = _
  rw [exp_measure_Ico_real r hr _ _ (by positivity) (by linarith)]
  push_cast
  congr 1 <;> congr 1 <;> ring

theorem exp_round_atom_geometric (r : ℝ) (hr : 0 < r) (k : ℕ) :
    (Measure.map roundEnergy (expMeasure r)).real {oddLevel (k:ℤ)} =
       (1 - Real.exp (-2*r)) * Real.exp (-2*r*(k:ℝ)) := by
  rw [exp_round_atom_real r hr k]
  rw [show -2*r*((k:ℝ)+1) = -2*r + -2*r*(k:ℝ) by ring, Real.exp_add]
  ring

theorem exp_interval_positive (r : ℝ) (hr : 0 < r) (b : ℝ) (hb : 0 < b) :
    0 < (expMeasure r).real (Ico 0 b) := by
  rw [exp_measure_Ico_real r hr 0 b le_rfl hb.le]
  simp only [mul_zero, neg_zero, Real.exp_zero, sub_pos]
  exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos (mul_pos hr hb))

/-- All almost-sure bounds attainable by some genuine coupling. -/
def infinityBounds (μ ν : Measure ℝ) : Set ℝ :=
  {c | ∃ γ ∈ couplings μ ν, ∀ᵐ p ∂γ, |p.1-p.2| ≤ c}

def wassersteinInfinity (μ ν : Measure ℝ) : ℝ :=
  sInf (infinityBounds μ ν)

/-- Sharp W∞ for the actual exponential law and its odd rounding.
The lower bound tests a positive-mass interval near zero for every
candidate coupling, not just the graph coupling. -/
theorem round_wassersteinInfinity_exp (r : ℝ) (hr : 0 < r) :
    wassersteinInfinity (expMeasure r) (Measure.map roundEnergy (expMeasure r)) = 1 := by
  let μ := expMeasure r
  have hone : (1:ℝ) ∈ infinityBounds μ (Measure.map roundEnergy μ) := by
    refine ⟨Measure.map (fun x : ℝ => (x, roundEnergy x)) μ,
      Manuscript15.MagneticGibbs.GraphCoupling.graph_measure_coupling μ roundEnergy
        measurable_roundEnergy, ?_⟩
    filter_upwards [graph_cost_eq_ae μ] with p hp
    rw [hp]
    exact round_displacement_le_one p.1
  have hlow : ∀ c ∈ infinityBounds μ (Measure.map roundEnergy μ), 1 ≤ c := by
    intro c hc
    obtain ⟨γ,hγ,hbound⟩ := hc
    by_contra! hlt
    let b : ℝ := min 1 (1-c)
    have hb : 0 < b := lt_min (by norm_num) (by linarith)
    have hb1 : b ≤ 1 := min_le_left _ _
    have hbc : b ≤ 1-c := min_le_right _ _
    have hcost : ∀ᵐ p ∂γ, |p.1-roundEnergy p.1| ≤ c := by
      filter_upwards [coupling_nearest_ae μ γ hγ,hbound] with p hp hq
      exact hp.trans hq
    have hs : MeasurableSet {x : ℝ | |x-roundEnergy x| ≤ c} :=
      measurableSet_le (measurable_id.sub measurable_roundEnergy).abs measurable_const
    have hae : ∀ᵐ x ∂μ, |x-roundEnergy x| ≤ c := by
      rw [← hγ.1]
      exact (ae_map_iff measurable_fst.aemeasurable hs).2 hcost
    have hbad : μ {x : ℝ | ¬ |x-roundEnergy x| ≤ c} = 0 := ae_iff.mp hae
    have hsub : Ico (0:ℝ) b ⊆ {x : ℝ | ¬ |x-roundEnergy x| ≤ c} := by
      intro x hx
      have hx0 := hx.1
      have hxb := hx.2
      have hf : ⌊x/2⌋ = (0:ℤ) := Int.floor_eq_iff.mpr ⟨by simp; linarith, by simp; linarith⟩
      have hround : roundEnergy x = 1 := by simp [roundEnergy,hf,oddLevel]
      change ¬ |x-roundEnergy x| ≤ c
      rw [hround,abs_of_nonpos (by linarith : x-1 ≤ 0)]
      linarith
    have hz : μ (Ico 0 b) = 0 := measure_mono_null hsub hbad
    have hpos := exp_interval_positive r hr b hb
    change 0 < μ.real (Ico 0 b) at hpos
    rw [measureReal_def,hz,ENNReal.toReal_zero] at hpos
    exact (lt_irrefl 0) hpos
  change sInf (infinityBounds μ (Measure.map roundEnergy μ)) = 1
  exact le_antisymm (csInf_le ⟨1,hlow⟩ hone) (le_csInf ⟨1,hone⟩ hlow)

end Manuscript15.MagneticGibbs.Rounding

#print axioms Manuscript15.MagneticGibbs.Rounding.exp_measure_Iio_real
#print axioms Manuscript15.MagneticGibbs.Rounding.exp_measure_Ico_real
#print axioms Manuscript15.MagneticGibbs.Rounding.exp_round_atom_real
#print axioms Manuscript15.MagneticGibbs.Rounding.exp_round_atom_geometric
#print axioms Manuscript15.MagneticGibbs.Rounding.exp_interval_positive
#print axioms Manuscript15.MagneticGibbs.Rounding.round_wassersteinInfinity_exp
