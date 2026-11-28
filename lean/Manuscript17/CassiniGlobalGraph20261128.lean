import Mathlib
import Manuscript17.CassiniPolynomialLift20261127
import Manuscript17.CassiniGlobalImage20261128

noncomputable section
namespace Manuscript17.CassiniGlobalGraph

open Set MeasureTheory
open Manuscript17.CassiniPolynomialLift
open Manuscript17.CassiniGlobalImage

/-! One global coordinate chart on the regular northern hemisphere,
including the pole. The disk is open. The metric is the actual tangent
pullback certified in #711, not an arbitrary density. -/
def disk : Set (ℝ × ℝ) := {p | p.1^2+p.2^2 < 1}
def height (p : ℝ × ℝ) : ℝ := Real.sqrt (1-p.1^2-p.2^2)
def graph (p : ℝ × ℝ) : Fin 3 → ℝ := ![p.1,p.2,height p]
def horizontal (x : Fin 3 → ℝ) : ℝ × ℝ := (x 0,x 1)
def regular : Set (Fin 3 → ℝ) := {x | sphereDot x x = 1 ∧ 0 < x 2}

theorem height_pos (p : ℝ × ℝ) (hp : p ∈ disk) : 0 < height p := by
  change p.1^2+p.2^2 < 1 at hp
  unfold height
  exact Real.sqrt_pos.2 (by linarith)

theorem height_sq (p : ℝ × ℝ) (hp : p ∈ disk) :
    height p^2 = 1-p.1^2-p.2^2 := by
  change p.1^2+p.2^2 < 1 at hp
  exact Real.sq_sqrt (by linarith)

theorem graph_regular (p : ℝ × ℝ) (hp : p ∈ disk) : graph p ∈ regular := by
  constructor
  · simp [graph,sphereDot]
    nlinarith [height_sq p hp]
  · simpa [graph] using height_pos p hp

theorem horizontal_graph (p : ℝ × ℝ) : horizontal (graph p) = p := by
  simp [horizontal,graph]

theorem horizontal_disk (x : Fin 3 → ℝ) (hx : x ∈ regular) : horizontal x ∈ disk := by
  change sphereDot x x = 1 ∧ 0 < x 2 at hx
  change (x 0)^2+(x 1)^2 < 1
  unfold sphereDot at hx
  nlinarith [sq_pos_of_pos hx.2]

theorem graph_horizontal (x : Fin 3 → ℝ) (hx : x ∈ regular) :
    graph (horizontal x) = x := by
  have hs := hx.1
  unfold sphereDot at hs
  have he : 1-(x 0)^2-(x 1)^2 = (x 2)^2 := by nlinarith
  funext i
  fin_cases i <;> simp [graph,horizontal,height,he,Real.sqrt_sq_eq_abs,abs_of_pos hx.2]

theorem graph_continuous : Continuous graph := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp [graph,height] <;> fun_prop

theorem horizontal_continuous : Continuous horizontal := by
  unfold horizontal
  fun_prop

def dx (p : ℝ × ℝ) : Fin 3 → ℝ := ![1,0,-p.1/height p]
def dy (p : ℝ × ℝ) : Fin 3 → ℝ := ![0,1,-p.2/height p]

theorem graph_dx (p : ℝ × ℝ) (hp : p ∈ disk) (i : Fin 3) :
    HasDerivAt (fun a => graph (a,p.2) i) (dx p i) p.1 := by
  have h : 0 < 1-p.1^2-p.2^2 := by
    change p.1^2+p.2^2 < 1 at hp
    linarith
  fin_cases i
  · simpa [graph,dx] using hasDerivAt_id' p.1
  · simpa [graph,dx] using hasDerivAt_const p.1 p.2
  · have hd := ((hasDerivAt_const p.1 (1:ℝ)).sub (hasDerivAt_pow 2 p.1)).sub
        (hasDerivAt_const p.1 (p.2^2))
    have hs := (Real.hasDerivAt_sqrt h.ne').comp p.1 hd
    convert hs using 1 <;> simp [graph,dx,height] <;> ring

theorem graph_dy (p : ℝ × ℝ) (hp : p ∈ disk) (i : Fin 3) :
    HasDerivAt (fun b => graph (p.1,b) i) (dy p i) p.2 := by
  have h : 0 < 1-p.1^2-p.2^2 := by
    change p.1^2+p.2^2 < 1 at hp
    linarith
  fin_cases i
  · simpa [graph,dy] using hasDerivAt_const p.2 p.1
  · simpa [graph,dy] using hasDerivAt_id' p.2
  · have hd := (hasDerivAt_const p.2 (1-p.1^2)).sub (hasDerivAt_pow 2 p.2)
    have hs := (Real.hasDerivAt_sqrt h.ne').comp p.2 hd
    convert hs using 1 <;> simp [graph,dy,height] <;> ring

theorem graph_tangent (p : ℝ × ℝ) (hp : p ∈ disk) :
    sphereDot (graph p) (dx p) = 0 ∧ sphereDot (graph p) (dy p) = 0 := by
  have h := (height_pos p hp).ne'
  constructor <;> simp [graph,dx,dy,sphereDot] <;> field_simp [h] <;> ring

def g11 (p : ℝ × ℝ) := (t (graph p))^2 * sphereDot (dx p) (dx p)
def g12 (p : ℝ × ℝ) := (t (graph p))^2 * sphereDot (dx p) (dy p)
def g22 (p : ℝ × ℝ) := (t (graph p))^2 * sphereDot (dy p) (dy p)
def density (p : ℝ × ℝ) := (t (graph p))^2 / height p

theorem gram_determinant (p : ℝ × ℝ) (hp : p ∈ disk) :
    g11 p*g22 p-(g12 p)^2 = (density p)^2 := by
  have h := (height_pos p hp).ne'
  have hs := height_sq p hp
  unfold g11 g12 g22 density
  simp [sphereDot,dx,dy]
  field_simp [h]
  linear_combination (t (graph p))^4 * (-hs)

theorem volume_density (p : ℝ × ℝ) (hp : p ∈ disk) :
    Real.sqrt (g11 p*g22 p-(g12 p)^2) = density p := by
  rw [gram_determinant p hp,Real.sqrt_sq_eq_abs]
  exact abs_of_nonneg (div_nonneg (sq_nonneg _) (height_pos p hp).le)

theorem density_formula (p : ℝ × ℝ) (hp : p ∈ disk) :
    density p = height p/(1+p.1^2+p.2^2)^2 := by
  have hs := height_sq p hp
  have hh := height_pos p hp
  have hq : 0 < 1+p.1^2+p.2^2 := by positivity
  unfold density t
  simp [graph]
  rw [show 2-height p^2 = 1+p.1^2+p.2^2 by linarith]
  field_simp [hh.ne',hq.ne']

/-- The global disk-volume construction, in a chart covering every
regular point (including the pole). -/
def diskVolume : Measure (ℝ × ℝ) :=
  ((volume : Measure (ℝ × ℝ)).restrict disk).withDensity
    (fun p => ENNReal.ofReal (density p))

def hemisphereVolume : Measure (Fin 3 → ℝ) := Measure.map graph diskVolume

theorem disk_measurable : MeasurableSet disk := by
  apply measurableSet_lt <;> fun_prop

theorem pole_zero : hemisphereVolume {![0,0,1]} = 0 := by
  rw [hemisphereVolume,Measure.map_apply graph_continuous.measurable (measurableSet_singleton _)]
  have he : graph ⁻¹' {(![0,0,1] : Fin 3 → ℝ)} ⊆ {(0,0)} := by
    intro p hp
    have h : graph p = ![0,0,1] := hp
    have hh := congrArg horizontal h
    simpa [horizontal_graph,horizontal] using hh
  apply le_antisymm _ (zero_le _)
  calc
    diskVolume (graph ⁻¹' {(![0,0,1] : Fin 3 → ℝ)}) ≤ diskVolume {(0,0)} :=
      measure_mono he
    _ = 0 := by
      unfold diskVolume
      rw [withDensity_apply _ (measurableSet_singleton _)]
      simp

#print axioms height_pos
#print axioms height_sq
#print axioms graph_regular
#print axioms horizontal_graph
#print axioms horizontal_disk
#print axioms graph_horizontal
#print axioms graph_continuous
#print axioms horizontal_continuous
#print axioms graph_dx
#print axioms graph_dy
#print axioms graph_tangent
#print axioms gram_determinant
#print axioms volume_density
#print axioms density_formula
#print axioms disk_measurable
#print axioms pole_zero
end Manuscript17.CassiniGlobalGraph
