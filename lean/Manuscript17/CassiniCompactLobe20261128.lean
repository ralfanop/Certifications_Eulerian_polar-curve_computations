import Mathlib
import Manuscript17.CassiniGlobalImage20261128
import Manuscript17.CassiniMeridianLength20261128

noncomputable section
namespace Manuscript17.CassiniCompactLobe

open Set
open Manuscript17.CassiniPolynomialLift Manuscript17.CassiniGlobalImage
open Manuscript17.CassiniMeridian

def closedLobe : Set (Fin 3 → ℝ) := {y | surface y}
def regularLobe : Set (Fin 3 → ℝ) := closedLobe \ {0}

theorem closed_lobe : IsClosed closedLobe := by
  unfold closedLobe surface
  exact isClosed_eq (by fun_prop) (by fun_prop)

theorem lobe_coordinate_bound (y : Fin 3 → ℝ) (hy : y ∈ closedLobe) (i : Fin 3) :
    |y i| ≤ 1 := by
  change y 2 = 2*(y 0)^2+2*(y 1)^2+(y 2)^2 at hy
  have h0 : 0 ≤ y 2 := by nlinarith [sq_nonneg (y 0),sq_nonneg (y 1),sq_nonneg (y 2)]
  have h1 : y 2 ≤ 1 := by
    by_contra! h
    nlinarith [sq_nonneg (y 0),sq_nonneg (y 1),mul_pos h (sub_pos.mpr h)]
  have h2 : (y 0)^2 ≤ 1 := by nlinarith [sq_nonneg (y 1),sq_nonneg (y 2)]
  have h3 : (y 1)^2 ≤ 1 := by nlinarith [sq_nonneg (y 0),sq_nonneg (y 2)]
  fin_cases i
  · rw [abs_le]
    constructor <;> nlinarith
  · rw [abs_le]
    constructor <;> nlinarith
  · rw [abs_of_nonneg h0]
    exact h1

theorem compact_lobe : IsCompact closedLobe := by
  apply (isCompact_Icc (a := fun _ : Fin 3 => (-1:ℝ)) (b := fun _ => (1:ℝ))).of_isClosed_subset closed_lobe
  intro y hy
  constructor
  · intro i
    exact (abs_le.mp (lobe_coordinate_bound y hy i)).1
  · intro i
    exact (abs_le.mp (lobe_coordinate_bound y hy i)).2

theorem origin_in_lobe : (0 : Fin 3 → ℝ) ∈ closedLobe := by
  simp [closedLobe,surface]

theorem regular_point_inverse (y : Fin 3 → ℝ) (hy : y ∈ regularLobe) :
    northern (inversePoint y) ∧ 0 < inversePoint y 2 ∧ imagePoint (inversePoint y) = y := by
  have hs : surface y := hy.1
  have hn : y ≠ 0 := hy.2
  have h := inverse_northern y hs hn
  have hi := image_inverse y hs hn
  have hp : 0 < inversePoint y 2 := by
    by_contra! hle
    have he : inversePoint y 2 = 0 := le_antisymm hle h.2
    have hz := (equator_collapse (inversePoint y) h).2 he
    exact hn (hi.symm.trans hz)
  exact ⟨h,hp,hi⟩

theorem approaching_meridian (s : ℝ) (hs : 0 < s) (ht : s < Real.pi/2) :
    imagePoint (latitude s 0) ∈ regularLobe := by
  have hsin : 0 < Real.sin s := Real.sin_pos_of_pos_of_lt_pi hs (by linarith [Real.pi_pos])
  have hn : northern (latitude s 0) := ⟨latitude_unit s 0,by simpa [latitude] using hsin.le⟩
  refine ⟨image_on_surface _ hn,?_⟩
  intro hz
  have he := (equator_collapse _ hn).1 hz
  simp [latitude] at he
  exact hsin.ne' he

theorem approach_continuous : Continuous (fun s : ℝ => imagePoint (latitude s 0)) := by
  apply continuous_pi
  intro i
  have hden : ∀ s : ℝ, 2-(latitude s 0 2)^2 ≠ 0 :=
    fun s => (denominator_pos _ (latitude_unit s 0)).ne'
  unfold imagePoint t
  have hc : Continuous (fun s : ℝ => latitude s 0 i) := by
    fin_cases i <;> simp [latitude] <;> fun_prop
  have ht : Continuous (fun s : ℝ => latitude s 0 2 / (2-(latitude s 0 2)^2)) := by
    apply Continuous.div
    · simp [latitude]; fun_prop
    · simp [latitude]; fun_prop
    · exact hden
  exact ht.mul hc

theorem approach_zero : imagePoint (latitude 0 0) = 0 := by
  funext i
  simp [imagePoint,t,latitude]

theorem origin_in_closure : (0 : Fin 3 → ℝ) ∈ closure regularLobe := by
  have ht : Filter.Tendsto (fun s : ℝ => imagePoint (latitude s 0))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa [approach_zero] using approach_continuous.continuousAt (x := (0:ℝ)).tendsto.mono_left nhdsWithin_le_nhds
  have he : ∀ᶠ s : ℝ in nhdsWithin 0 (Ioi 0), imagePoint (latitude s 0) ∈ regularLobe := by
    have hlt : ∀ᶠ s : ℝ in nhdsWithin 0 (Ioi 0), s < Real.pi/2 :=
      nhdsWithin_le_nhds (Iio_mem_nhds (by positivity))
    filter_upwards [self_mem_nhdsWithin, hlt] with s hs hp
    exact approaching_meridian s hs hp
  exact mem_closure_of_tendsto ht he

theorem closure_regular_lobe : closure regularLobe = closedLobe := by
  apply le_antisymm
  · exact closure_minimal (fun _ h => h.1) closed_lobe
  · intro y hy
    by_cases h : y = 0
    · simpa [h] using origin_in_closure
    · exact subset_closure ⟨hy,h⟩

/-- Completeness of the closed affine image for its ambient metric.
Identification with the intrinsic Riemannian length metric is separate. -/
theorem complete_closed_lobe : IsComplete closedLobe :=
  compact_lobe.isComplete

#print axioms closed_lobe
#print axioms lobe_coordinate_bound
#print axioms compact_lobe
#print axioms origin_in_lobe
#print axioms regular_point_inverse
#print axioms approaching_meridian
#print axioms approach_continuous
#print axioms approach_zero
#print axioms origin_in_closure
#print axioms closure_regular_lobe
#print axioms complete_closed_lobe
end Manuscript17.CassiniCompactLobe
