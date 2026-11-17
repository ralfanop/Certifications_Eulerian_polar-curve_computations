import Mathlib

/-! M14 seven-loop ideal nearest-neighbour circuit, independent of the
already established adjacency spectrum. No claim about lossy resonators
or experimental coupling coefficients. -/
noncomputable section
namespace Manuscript14.SevenLoop

/-- The impedance equation after multiplication by ωC and cancellation of i. -/
def reactanceMode (L C M ω λ : ℝ) : ℝ :=
  (ω^2*L*C-1)+ω^2*M*C*λ

theorem dispersion (L C M ω λ : ℝ) (hL : 0 < L) (hC : 0 < C)
    (hω : 0 < ω) :
    reactanceMode L C M ω λ = 0 ↔
      1/(L*C*ω^2) = 1 + (M/L)*λ := by
  unfold reactanceMode
  constructor <;> intro h
  · apply (div_eq_iff (by positivity : L*C*ω^2 ≠ 0)).2
    calc
      (1:ℝ) = ω^2*L*C+ω^2*M*C*λ := by linarith
      _ = (1+M/L*λ)*(L*C*ω^2) := by field_simp [hL.ne'] <;> ring
  · have hh := (div_eq_iff (by positivity : L*C*ω^2 ≠ 0)).1 h
    have he : (1+M/L*λ)*(L*C*ω^2) = ω^2*L*C+ω^2*M*C*λ := by
      field_simp [hL.ne'] <;> ring
    rw [he] at hh
    linarith

/-- The physical modal inductance is positive for every eigenvalue
with |λ| ≤ μ when |M| μ < L. -/
theorem modal_inductance_positive (L M λ μ : ℝ) (hμ : 0 ≤ μ)
    (hλ : |λ| ≤ μ) (hc : |M|*μ < L) : 0 < L+M*λ := by
  have h : |M*λ| ≤ |M|*μ := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hλ (abs_nonneg M)
  have hl := (abs_le.mp h).1
  linarith

theorem natural_frequency (L C M λ : ℝ) (hC : 0 < C) (h : 0 < L+M*λ) :
    reactanceMode L C M (1/Real.sqrt (C*(L+M*λ))) λ = 0 := by
  have hp : 0 < C*(L+M*λ) := mul_pos hC h
  have hs : Real.sqrt (C*(L+M*λ)) ≠ 0 := (Real.sqrt_pos.2 hp).ne'
  unfold reactanceMode
  have he : (1/Real.sqrt (C*(L+M*λ)))^2 * (C*(L+M*λ)) = 1 := by
    rw [div_pow, one_pow, Real.sq_sqrt hp.le]
    field_simp [hp.ne']
  nlinarith [he]

/-- Sinusoidal adjacency relation turned into the dimensionless
natural-frequency ratio, with κ=2M/L. -/
theorem sinusoidal_dispersion (L C M ω θ : ℝ) (hL : 0 < L)
    (hC : 0 < C) (hω : 0 < ω) :
    reactanceMode L C M ω (2*Real.cos θ) = 0 ↔
      1/(L*C*ω^2) = 1+(2*M/L)*Real.cos θ := by
  rw [dispersion L C M ω (2*Real.cos θ) hL hC hω]
  have he : 1+M/L*(2*Real.cos θ) = 1+(2*M/L)*Real.cos θ := by ring
  rw [he]

/-- Kirchhoff equation at an actual site of the open nearest-neighbour
line, when the adjacency eigenvector recurrence is satisfied. -/
theorem site_equation (L C M ω λ : ℝ) (u : ℕ → ℝ) (n : ℕ)
    (heig : u n + u (n+2) = λ*u (n+1))
    (hmode : reactanceMode L C M ω λ = 0) :
    (ω^2*L*C-1)*u (n+1) + ω^2*M*C*(u n+u (n+2)) = 0 := by
  rw [heig]
  calc
    _ = reactanceMode L C M ω λ * u (n+1) := by unfold reactanceMode; ring
    _ = 0 := by rw [hmode, zero_mul]

/-- Exact sinusoidal recurrence, used at the seven consecutive sites. -/
theorem sine_recurrence (θ t : ℝ) :
    Real.sin (t-θ)+Real.sin (t+θ) =
      (2*Real.cos θ)*Real.sin t := by
  rw [Real.sin_sub, Real.sin_add]
  ring

theorem sinusoidal_site (L C M ω θ t : ℝ)
    (hmode : reactanceMode L C M ω (2*Real.cos θ) = 0) :
    (ω^2*L*C-1)*Real.sin t +
      ω^2*M*C*(Real.sin (t-θ)+Real.sin (t+θ)) = 0 := by
  rw [sine_recurrence]
  calc
    _ = reactanceMode L C M ω (2*Real.cos θ) * Real.sin t := by
      unfold reactanceMode
      ring
    _ = 0 := by rw [hmode, zero_mul]

#print axioms sine_recurrence
#print axioms sinusoidal_site
#print axioms dispersion
#print axioms modal_inductance_positive
#print axioms natural_frequency
#print axioms sinusoidal_dispersion
#print axioms site_equation
end Manuscript14.SevenLoop
