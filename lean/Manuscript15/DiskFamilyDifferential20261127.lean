import Manuscript15.DiskFamilyCassiniTaylor20261127
import Manuscript15.DiskFamilyExtremizers20261127
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Differential identification of the signed curvature at the horizontal
tangent of the actual Cassini graph and lower circle. No assumed derivative. -/
noncomputable section
open Complex Filter Topology
namespace Manuscript15.DiskFamily20261127
open EulerianGrothendieck.ArcsinDisk

def innerCassini (t x : ℝ) : ℝ :=
  Real.sqrt ((1+t^2)^2+4*x^2)

def outerCassini (t x : ℝ) : ℝ := innerCassini t x-1-x^2

def cassiniSlopeFactor (t x : ℝ) : ℝ :=
  (2/innerCassini t x-1)/cassiniGraph t x

theorem innerCassini_pos (t x : ℝ) : 0 < innerCassini t x := by
  unfold innerCassini
  positivity

theorem innerCassini_zero (t : ℝ) : innerCassini t 0 = 1+t^2 := by
  unfold innerCassini
  simp only [zero_pow (by decide : (2:ℕ) ≠ 0),mul_zero,add_zero]
  exact Real.sqrt_sq (by positivity)

theorem outerCassini_zero (t : ℝ) : outerCassini t 0=t^2 := by
  unfold outerCassini
  rw [innerCassini_zero]
  ring

theorem cassiniGraph_zero {t : ℝ} (ht : 0 < t) : cassiniGraph t 0=t := by
  change Real.sqrt (outerCassini t 0)=t
  rw [outerCassini_zero,Real.sqrt_sq ht.le]

theorem outerCassini_pos {t x : ℝ} (h : x^2<t^2) : 0 < outerCassini t x := by
  have hle : 1+t^2 ≤ innerCassini t x := by
    unfold innerCassini
    calc
      1+t^2 = Real.sqrt ((1+t^2)^2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg x])
  unfold outerCassini
  linarith

theorem innerCassini_hasDerivAt (t x : ℝ) :
    HasDerivAt (innerCassini t) (4*x/innerCassini t x) x := by
  have h : HasDerivAt (fun u : ℝ => (1+t^2)^2+4*u^2) (8*x) x := by
    convert (((hasDerivAt_pow 2 x).const_mul 4).const_add ((1+t^2)^2)) using 1 <;> ring
  have hp : 0 < (1+t^2)^2+4*x^2 := by positivity
  have hh := h.sqrt hp.ne'
  convert hh using 1
  unfold innerCassini
  ring

theorem outerCassini_hasDerivAt (t x : ℝ) :
    HasDerivAt (outerCassini t) (4*x/innerCassini t x-2*x) x := by
  unfold outerCassini
  convert (((innerCassini_hasDerivAt t x).sub_const 1).sub (hasDerivAt_pow 2 x)) using 1 <;> ring

theorem cassini_hasDerivAt {t x : ℝ} (h : 0 < outerCassini t x) :
    HasDerivAt (cassiniGraph t) (x*cassiniSlopeFactor t x) x := by
  have hh := (outerCassini_hasDerivAt t x).sqrt h.ne'
  change HasDerivAt (fun u => Real.sqrt (outerCassini t u)) _ x
  convert hh using 1
  unfold cassiniSlopeFactor cassiniGraph
  change x*((2/innerCassini t x-1)/Real.sqrt (outerCassini t x)) = _
  have hq : innerCassini t x ≠ 0 := (innerCassini_pos t x).ne'
  have hy : Real.sqrt (outerCassini t x) ≠ 0 := (Real.sqrt_pos.2 h).ne'
  field_simp [hq,hy] <;> ring

theorem cassini_first_derivative_zero {t : ℝ} (ht : 0 < t) :
    HasDerivAt (cassiniGraph t) 0 0 := by
  have h : 0 < outerCassini t 0 := by rw [outerCassini_zero]; positivity
  simpa only [zero_mul] using cassini_hasDerivAt h

theorem cassiniSlopeFactor_zero {t : ℝ} (ht : 0 < t) :
    cassiniSlopeFactor t 0=cassiniCurvature t := by
  unfold cassiniSlopeFactor cassiniCurvature
  rw [innerCassini_zero,cassiniGraph_zero ht]
  field_simp [ht.ne',show 1+t^2 ≠ 0 by positivity] <;> ring

theorem cassiniSlopeFactor_hasDerivAt_zero {t : ℝ} (ht : 0 < t) :
    HasDerivAt (cassiniSlopeFactor t) 0 0 := by
  have hi : HasDerivAt (innerCassini t) 0 0 := by
    simpa using innerCassini_hasDerivAt t 0
  have hnum := ((hasDerivAt_const (0:ℝ) (2:ℝ)).div hi (innerCassini_pos t 0).ne').sub_const 1
  have hne : cassiniGraph t 0 ≠ 0 := by rw [cassiniGraph_zero ht]; exact ht.ne'
  have h := hnum.div (cassini_first_derivative_zero ht) hne
  convert h using 1 <;> simp [cassiniSlopeFactor]

theorem cassini_second_derivative {t : ℝ} (ht : 0 < t) :
    HasDerivAt (deriv (cassiniGraph t)) (cassiniCurvature t) 0 := by
  have hp := (hasDerivAt_id (0:ℝ)).mul (cassiniSlopeFactor_hasDerivAt_zero ht)
  have hp' : HasDerivAt (fun x : ℝ => x*cassiniSlopeFactor t x) (cassiniCurvature t) 0 := by
    simpa [cassiniSlopeFactor_zero ht] using hp
  apply hp'.congr_of_eventuallyEq
  filter_upwards [Metric.ball_mem_nhds (0:ℝ) ht] with x hx
  have hx' : |x| < t := by simpa [Metric.mem_ball,Real.dist_eq] using hx
  have hsq : x^2<t^2 := by
    have hp := mul_pos (show 0 < t-|x| by linarith) (show 0 < t+|x| by positivity)
    nlinarith [sq_abs x]
  exact (cassini_hasDerivAt (outerCassini_pos hsq)).deriv

def circleSlopeFactor (r x : ℝ) : ℝ := 1/Real.sqrt (r^2-x^2)

theorem circle_hasDerivAt {r x : ℝ} (h : 0 < r^2-x^2) :
    HasDerivAt (lowerCircleGraph r) (x*circleSlopeFactor r x) x := by
  have hp : HasDerivAt (fun u : ℝ => r^2-u^2) (-2*x) x := by
    convert (hasDerivAt_pow 2 x).const_sub (r^2) using 1 <;> ring
  have hh := (hp.sqrt h.ne').const_sub 1
  unfold lowerCircleGraph
  convert hh using 1
  unfold circleSlopeFactor
  field_simp [(Real.sqrt_pos.2 h).ne'] <;> ring

theorem circle_first_derivative_zero {r : ℝ} (hr : 0 < r) :
    HasDerivAt (lowerCircleGraph r) 0 0 := by
  have h : 0 < r^2-(0:ℝ)^2 := by simp; positivity
  simpa only [zero_mul] using circle_hasDerivAt h

theorem circle_second_derivative {r : ℝ} (hr : 0 < r) :
    HasDerivAt (deriv (lowerCircleGraph r)) (1/r) 0 := by
  have h : HasDerivAt (fun x : ℝ => r^2-x^2) 0 0 := by
    convert (hasDerivAt_pow 2 (0:ℝ)).const_sub (r^2) using 1 <;> ring
  have hpos : 0 < r^2-(0:ℝ)^2 := by simp; positivity
  have hh := (hasDerivAt_const (0:ℝ) (1:ℝ)).div (h.sqrt hpos.ne') (Real.sqrt_pos.2 hpos).ne'
  have hf : HasDerivAt (circleSlopeFactor r) 0 0 := by
    convert hh using 1 <;> simp [circleSlopeFactor]
  have hp := (hasDerivAt_id (0:ℝ)).mul hf
  have hp' : HasDerivAt (fun x : ℝ => x*circleSlopeFactor r x) (1/r) 0 := by
    simpa [circleSlopeFactor,Real.sqrt_sq hr.le] using hp
  apply hp'.congr_of_eventuallyEq
  filter_upwards [Metric.ball_mem_nhds (0:ℝ) hr] with x hx
  have hx' : |x| < r := by simpa [Metric.mem_ball,Real.dist_eq] using hx
  have hp := mul_pos (show 0 < r-|x| by linarith) (show 0 < r+|x| by positivity)
  have hsq : 0 < r^2-x^2 := by nlinarith [sq_abs x]
  exact (circle_hasDerivAt hsq).deriv

/-- Signed curvature of the oriented regular graph x ↦ (x,f x). -/
def signedGraphCurvature (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv (deriv f) x / (Real.sqrt (1+(deriv f x)^2))^3

theorem cassini_geometric_curvature {t : ℝ} (ht : 0 < t) :
    signedGraphCurvature (cassiniGraph t) 0=cassiniCurvature t := by
  unfold signedGraphCurvature
  rw [(cassini_first_derivative_zero ht).deriv,(cassini_second_derivative ht).deriv]
  simp

theorem circle_geometric_curvature {r : ℝ} (hr : 0 < r) :
    signedGraphCurvature (lowerCircleGraph r) 0=1/r := by
  unfold signedGraphCurvature
  rw [(circle_first_derivative_zero hr).deriv,(circle_second_derivative hr).deriv]
  simp

theorem geometric_curvature_contact {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    signedGraphCurvature (cassiniGraph (1-r)) 0 =
      signedGraphCurvature (lowerCircleGraph r) 0 ↔ r=threshold := by
  rw [cassini_geometric_curvature (sub_pos.mpr hr1),circle_geometric_curvature hr]
  exact cassini_circle_curvature_contact hr hr1

end Manuscript15.DiskFamily20261127
#print axioms Manuscript15.DiskFamily20261127.innerCassini_pos
#print axioms Manuscript15.DiskFamily20261127.innerCassini_zero
#print axioms Manuscript15.DiskFamily20261127.outerCassini_zero
#print axioms Manuscript15.DiskFamily20261127.cassiniGraph_zero
#print axioms Manuscript15.DiskFamily20261127.outerCassini_pos
#print axioms Manuscript15.DiskFamily20261127.innerCassini_hasDerivAt
#print axioms Manuscript15.DiskFamily20261127.outerCassini_hasDerivAt
#print axioms Manuscript15.DiskFamily20261127.cassini_hasDerivAt
#print axioms Manuscript15.DiskFamily20261127.cassini_first_derivative_zero
#print axioms Manuscript15.DiskFamily20261127.cassiniSlopeFactor_zero
#print axioms Manuscript15.DiskFamily20261127.cassiniSlopeFactor_hasDerivAt_zero
#print axioms Manuscript15.DiskFamily20261127.cassini_second_derivative
#print axioms Manuscript15.DiskFamily20261127.circle_hasDerivAt
#print axioms Manuscript15.DiskFamily20261127.circle_first_derivative_zero
#print axioms Manuscript15.DiskFamily20261127.circle_second_derivative
#print axioms Manuscript15.DiskFamily20261127.cassini_geometric_curvature
#print axioms Manuscript15.DiskFamily20261127.circle_geometric_curvature
#print axioms Manuscript15.DiskFamily20261127.geometric_curvature_contact
