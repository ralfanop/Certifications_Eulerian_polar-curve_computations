import Manuscript15.HopfSubmersionDifferential20261124
import Mathlib

/-!
# M15: local spherical chart of the actual Hopf map and Laplace coefficients

Independent local coordinate bridge toward M15
prop:hopf-basic-laplace, eq:hopf-basic-laplacian.

For q(η,α,β) = (cosη e^(iα), sinη e^(iβ)),
the actual normalized Hopf map is
  π_H(q) = 1/2 (sin(2η)cos(α-β), sin(2η)sin(α-β), cos(2η)).
The source round S³ metric in these coordinates is classically
  dη² + cos²η dα² + sin²η dβ²,
whereas the base radius-1/2 S² metric is
  (dθ² + sin²θ dφ²)/4, θ=2η, φ=α-β.

The Lean theorems prove the actual Hopf chart, its unit-sphere
constraint, and the EXACT identity between the scalar Laplacian's
LOCAL COEFFICIENTS for arbitrary base 2-jet values. The chart
metric, the C² chain rule, smoothness at the poles and the intrinsic
Laplace--Beltrami identification remain independent obligations.

The formulas are derived here from standard trigonometry, not
quoted as a source theorem or asserted axiomatically.
-/

namespace Manuscript15.HopfLocalLaplacian20261124

open Manuscript15.HopfDifferential20261124

/-- Standard Hopf angular chart on the actual real unit S³. -/
noncomputable def hopfChart (η α β : ℝ) : HopfQ :=
  ((Real.cos η * Real.cos α, Real.cos η * Real.sin α),
    (Real.sin η * Real.cos β, Real.sin η * Real.sin β))

/-- Every chart point lies on the true unit sphere in ℂ². -/
theorem hopfChart_unit (η α β : ℝ) :
    normSq4 (hopfChart η α β) = 1 := by
  calc
    normSq4 (hopfChart η α β) =
      Real.cos η ^ 2 * (Real.cos α ^ 2 + Real.sin α ^ 2) +
      Real.sin η ^ 2 * (Real.cos β ^ 2 + Real.sin β ^ 2) := by
        dsimp [normSq4, hopfChart]
        ring
    _ = Real.cos η ^ 2 + Real.sin η ^ 2 := by
      rw [Real.cos_sq_add_sin_sq α, Real.cos_sq_add_sin_sq β]
      ring
    _ = 1 := Real.cos_sq_add_sin_sq η

/-- Actual quadratic Hopf X coordinate in the angular chart. -/
theorem hopfChart_X (η α β : ℝ) :
    hopfX (hopfChart η α β) =
      Real.sin (2 * η) * Real.cos (α - β) := by
  rw [Real.sin_two_mul, Real.cos_sub]
  dsimp [hopfX, hopfChart]
  ring

/-- Actual quadratic Hopf Y coordinate in the angular chart. -/
theorem hopfChart_Y (η α β : ℝ) :
    hopfY (hopfChart η α β) =
      Real.sin (2 * η) * Real.sin (α - β) := by
  rw [Real.sin_two_mul, Real.sin_sub]
  dsimp [hopfY, hopfChart]
  ring

/-- Actual quadratic Hopf Z coordinate in the angular chart. -/
theorem hopfChart_Z (η α β : ℝ) :
    hopfZ (hopfChart η α β) = Real.cos (2 * η) := by
  calc
    hopfZ (hopfChart η α β) =
      Real.cos η ^ 2 * (Real.cos α ^ 2 + Real.sin α ^ 2) -
      Real.sin η ^ 2 * (Real.cos β ^ 2 + Real.sin β ^ 2) := by
        dsimp [hopfZ, hopfChart]
        ring
    _ = Real.cos η ^ 2 - Real.sin η ^ 2 := by
      rw [Real.cos_sq_add_sin_sq α, Real.cos_sq_add_sin_sq β]
      ring
    _ = Real.cos (2 * η) := (Real.cos_two_mul' η).symm

/-- True curvature-four spherical map in Hopf coordinates.
This is an identity of the actually defined map h/2, not
a separately postulated parametrisation. -/
theorem hopfChart_base (η α β : ℝ) :
    hopfBase (hopfChart η α β) =
      ((Real.sin (2 * η) * Real.cos (α - β) / 2,
        Real.sin (2 * η) * Real.sin (α - β) / 2),
        Real.cos (2 * η) / 2) := by
  change ((hopfX (hopfChart η α β) / 2,
    hopfY (hopfChart η α β) / 2),
    hopfZ (hopfChart η α β) / 2) = _
  rw [hopfChart_X, hopfChart_Y, hopfChart_Z]

/-- Exact first-order divergence coefficient in Hopf angles,
corresponding to the θ=2η change of angular variable.
The hypothesis merely excludes singular chart coordinates. -/
theorem hopf_cotangent_coefficient (η : ℝ)
    (hs : Real.sin η ≠ 0) (hc : Real.cos η ≠ 0) :
    2 * (Real.cos η / Real.sin η - Real.sin η / Real.cos η) =
      4 * (Real.cos (2 * η) / Real.sin (2 * η)) := by
  rw [Real.cos_two_mul', Real.sin_two_mul]
  field_simp [hs, hc]
  ring

/-- Exact angular second-derivative coefficient for the radius-1/2
Fubini--Study base metric. -/
theorem hopf_cosecant_coefficient (η : ℝ)
    (hs : Real.sin η ≠ 0) (hc : Real.cos η ≠ 0) :
    1 / Real.cos η ^ 2 + 1 / Real.sin η ^ 2 =
      4 / Real.sin (2 * η) ^ 2 := by
  calc
    1 / Real.cos η ^ 2 + 1 / Real.sin η ^ 2 =
        (Real.sin η ^ 2 + Real.cos η ^ 2) /
          (Real.sin η ^ 2 * Real.cos η ^ 2) := by
            field_simp [hs, hc]
            ring
    _ = 1 / (Real.sin η ^ 2 * Real.cos η ^ 2) := by
      rw [Real.sin_sq_add_cos_sq η]
    _ = 4 / Real.sin (2 * η) ^ 2 := by
      rw [Real.sin_two_mul]
      field_simp [hs, hc]
      ring

/-- Local scalar Laplacian coefficient expression in the round
S³ Hopf chart when applied to a Hopf-basic scalar f(2η,α-β).
A,B,C are respectively the θθ, θ and φφ base 2-jet values.
The sign used is div grad; apply the same negative sign to both
sides to obtain the nonnegative convention of the manuscript. -/
noncomputable def hopfS3LocalTrace (η A B C : ℝ) : ℝ :=
    4 * A +
      2 * (Real.cos η / Real.sin η - Real.sin η / Real.cos η) * B +
      (1 / Real.cos η ^ 2 + 1 / Real.sin η ^ 2) * C

/-- Local scalar Laplacian expression on the radius-1/2 base
sphere at θ, for the same three 2-jet coefficients. -/
noncomputable def baseSphereLocalTrace (θ A B C : ℝ) : ℝ :=
    4 * (A + (Real.cos θ / Real.sin θ) * B +
      (1 / Real.sin θ ^ 2) * C)

/-- Complete equality of the LOCAL scalar Laplace coefficients
for arbitrary C² angular 2-jet values A,B,C, away from poles.
No condition about eigenfunctions, Fourier modes or polynomial
degree is needed. This is an explicit analytic chart bridge,
not yet the full intrinsic differential-operator theorem. -/
theorem hopf_local_laplacian_coefficient_identity (η A B C : ℝ)
    (hs : Real.sin η ≠ 0) (hc : Real.cos η ≠ 0) :
    hopfS3LocalTrace η A B C =
      baseSphereLocalTrace (2 * η) A B C := by
  have hcot := hopf_cotangent_coefficient η hs hc
  have hcsc := hopf_cosecant_coefficient η hs hc
  calc
    hopfS3LocalTrace η A B C =
        4 * A +
          (2 * (Real.cos η / Real.sin η - Real.sin η / Real.cos η)) * B +
          (1 / Real.cos η ^ 2 + 1 / Real.sin η ^ 2) * C := by
            dsimp [hopfS3LocalTrace]
            ring
    _ = 4 * A +
          (4 * (Real.cos (2 * η) / Real.sin (2 * η))) * B +
          (4 / Real.sin (2 * η) ^ 2) * C := by rw [hcot, hcsc]
    _ = baseSphereLocalTrace (2 * η) A B C := by
          dsimp [baseSphereLocalTrace]
          ring

#print axioms Manuscript15.HopfLocalLaplacian20261124.hopfChart_unit
#print axioms Manuscript15.HopfLocalLaplacian20261124.hopfChart_X
#print axioms Manuscript15.HopfLocalLaplacian20261124.hopfChart_Y
#print axioms Manuscript15.HopfLocalLaplacian20261124.hopfChart_Z
#print axioms Manuscript15.HopfLocalLaplacian20261124.hopfChart_base
#print axioms Manuscript15.HopfLocalLaplacian20261124.hopf_cotangent_coefficient
#print axioms Manuscript15.HopfLocalLaplacian20261124.hopf_cosecant_coefficient
#print axioms Manuscript15.HopfLocalLaplacian20261124.hopf_local_laplacian_coefficient_identity

end Manuscript15.HopfLocalLaplacian20261124
