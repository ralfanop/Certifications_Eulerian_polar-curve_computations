import Mathlib

/-!
# Manuscript 16 — rotating Hopf observer, Costa–Natário (23 Nov 2026)

Source: `Manuscript_16_20261123_COSTA_NATARIO_HOPF_COMPLETE`,
`16.tex`, `prop:gem-hopf-rotation` and
`cor:gem-hopf-magnetic-spectrum`, especially
`eq:gem-rotating-ultrastationary`,
`eq:gem-rotating-tidal`, and
`eq:gem-rotating-dispersion`.

The metric and tidal identities below are equalities of their evaluations
on EVERY PAIR of frame tangent vectors, not just diagonal scalar
coefficients. The geometric differential of the rotating-coordinate
diffeomorphism, Levi–Civita naturality, Hodge star and unbounded operator
domains are separate proof obligations. Earlier M16 modules are unchanged.
-/
namespace Manuscript16.CostaNatarioHopf20261123

/-- `Q_b = 1-b²` from the rotating observer metric. -/
def Q (b : ℝ) : ℝ := 1 - b ^ 2

theorem Q_positive (b : ℝ) (hb : |b| < 1) : 0 < Q b := by
  have hh : -1 < b ∧ b < 1 := abs_lt.mp hb
  unfold Q
  nlinarith [sq_nonneg b]

/-- Einstein-cylinder metric evaluated on two tangent frame vectors
with components `(dτ,σ₀,σ₁,σ₂)`. -/
def rotatingEinsteinFrame (b : ℝ) (u v : Fin 4 → ℝ) : ℝ :=
  -(1 - b ^ 2) * u 0 * v 0 +
  b * (u 0 * v 1 + u 1 * v 0) +
  u 1 * v 1 + u 2 * v 2 + u 3 * v 3

/-- `-(ds-A_b)²+γ_b` evaluated as a symmetric covariant
two-tensor in the same frame; `s²=Q_b`. -/
def rotatingUltrastationaryFrame (b s : ℝ) (u v : Fin 4 → ℝ) : ℝ :=
  -(s * u 0 - b / s * u 1) *
      (s * v 0 - b / s * v 1) +
    (u 1 * v 1) / s ^ 2 + u 2 * v 2 + u 3 * v 3

/-- Exact equality of the two **bilinear tensor evaluations** for
all tangent-vector pairs. This is the rotating Hopf coframe identity;
global metric pullback still needs differentiable frame formalisation. -/
theorem rotating_metric_tensor_identity (b s : ℝ)
    (hs : s ≠ 0) (hQ : s ^ 2 = 1 - b ^ 2) :
    rotatingUltrastationaryFrame b s = rotatingEinsteinFrame b := by
  funext u v
  calc
    rotatingUltrastationaryFrame b s u v =
      -(s ^ 2) * u 0 * v 0 +
        b * (u 0 * v 1 + u 1 * v 0) +
        ((1 - b ^ 2) / s ^ 2) * u 1 * v 1 +
        u 2 * v 2 + u 3 * v 3 := by
          unfold rotatingUltrastationaryFrame
          field_simp [hs]
          ring
    _ = rotatingEinsteinFrame b u v := by
      unfold rotatingEinsteinFrame
      rw [← hQ]
      have hc : s ^ 2 / s ^ 2 = (1 : ℝ) := by
        field_simp [hs]
      rw [hc]
      ring

/-- The Costa–Natário tidal tensor `(‖H‖² γ-H⊗H)/4`
in the Hopf-adapted orthonormal coframe `(η₀,σ₁,σ₂)`,
with `‖H‖²=4b²/s²` and `H=(2b/s)η₀`. -/
def costaTidalFrame (b s : ℝ) (u v : Fin 3 → ℝ) : ℝ :=
  ((4 * b ^ 2 / s ^ 2) *
      (u 0 * v 0 + u 1 * v 1 + u 2 * v 2) -
    ((2 * b / s) * u 0) * ((2 * b / s) * v 0)) / 4

def diagonalTidalFrame (b s : ℝ) (u v : Fin 3 → ℝ) : ℝ :=
  (b ^ 2 / s ^ 2) * (u 1 * v 1 + u 2 * v 2)

/-- Tensor equality from the full Costa–Natário tidal formula,
not merely equality of their eigenvalue lists. -/
theorem tidal_tensor_identity (b s : ℝ) (hs : s ≠ 0) :
    costaTidalFrame b s = diagonalTidalFrame b s := by
  funext u v
  unfold costaTidalFrame diagonalTidalFrame
  field_simp [hs]
  ring

/-- The Hopf-tangent direction has zero tidal eigenvalue. -/
theorem tidal_longitudinal_zero (b s : ℝ) :
    diagonalTidalFrame b s (fun i => if i = 0 then 1 else 0)
      (fun i => if i = 0 then 1 else 0) = 0 := by
  simp [diagonalTidalFrame]

/-- The horizontal direction has eigenvalue `b²/s²`. -/
theorem tidal_transverse_eigenvalue (b s : ℝ) :
    diagonalTidalFrame b s (fun i => if i = 1 then 1 else 0)
      (fun i => if i = 1 then 1 else 0) = b ^ 2 / s ^ 2 := by
  simp [diagonalTidalFrame]

/-- The rotating scalar Klein–Gordon relation, expressed as the
complete equality of the magnetic and shifted-frequency dispersion
polynomials. The harmonic eigenfunction relation is an independent
geometric spectral hypothesis in the manuscript. -/
theorem magnetic_dispersion_identity (b s ω k ell mass : ℝ)
    (hQ : s ^ 2 = 1 - b ^ 2) :
    ω ^ 2 - (ell * (ell + 2) - k ^ 2 +
      (s * k - b * ω) ^ 2) - mass ^ 2 =
      (s * ω + b * k) ^ 2 - ell * (ell + 2) - mass ^ 2 := by
  have hh : 1 - s ^ 2 - b ^ 2 = 0 := by
    linarith [hQ]
  calc
    ω ^ 2 - (ell * (ell + 2) - k ^ 2 +
        (s * k - b * ω) ^ 2) - mass ^ 2 =
      (s * ω + b * k) ^ 2 - ell * (ell + 2) - mass ^ 2 +
        (1 - s ^ 2 - b ^ 2) * (ω ^ 2 + k ^ 2) := by ring
    _ = (s * ω + b * k) ^ 2 - ell * (ell + 2) - mass ^ 2 := by
      rw [hh]
      ring

#print axioms Manuscript16.CostaNatarioHopf20261123.Q_positive
#print axioms Manuscript16.CostaNatarioHopf20261123.rotating_metric_tensor_identity
#print axioms Manuscript16.CostaNatarioHopf20261123.tidal_tensor_identity
#print axioms Manuscript16.CostaNatarioHopf20261123.tidal_longitudinal_zero
#print axioms Manuscript16.CostaNatarioHopf20261123.tidal_transverse_eigenvalue
#print axioms Manuscript16.CostaNatarioHopf20261123.magnetic_dispersion_identity

end Manuscript16.CostaNatarioHopf20261123
