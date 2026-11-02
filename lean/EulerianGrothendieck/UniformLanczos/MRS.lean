/-
Uniform Lanczos note, Lemma 3, condition (v): the Mhaskar–Rakhmanov–Saff equations for the
even field `Q_{N,M}` reduce exactly to the finite-`M` endpoint equation of Lemma 2.

The MRS equations of Levin–Lubinsky (1.13)–(1.14) are taken in the arcsine (`y = cos θ`) form
  `(1/π) ∫₀^π cos θ · Q'(cos θ) dθ = 1`,   `(1/π) ∫₀^π Q'(cos θ) dθ = 0`;
the substitution `y = cos θ` in the improper integrals `∫_{-1}^{1} … dy/√(1-y²)` is not
formalised.  With `Q'(y) = (a M/(2N)) P(a y)`, `P = φ_M'` odd and continuous:
* `cos_odd_eq_two_sin` : `∫₀^π cos θ P(a cos θ) dθ = 2 ∫₀^{π/2} sin θ P(a sin θ) dθ`;
* `mrs_first_iff`      : first MRS equation  ⇔  `Hint (y ↦ y P y) a = N/M`
                         (exactly the note's equation for `a_{N,M}`; every factor checked);
* `mrs_second`         : the second MRS equation holds automatically (parity).
Also `beta_scaling`: if the monic norms satisfy `h^X_n = c^{2n} h^y_n` (monic polynomials of
`X = c y`) and `A_{N-1} = γ_{N-1}/γ_N` with `γ_n = (h^y_n)^{-1/2}` (orthonormal leading
coefficients), then `β^X_N = h^X_N/h^X_{N-1} = c² A_{N-1}²`; with `c = M a_{N,M}` this is
`β_N^{[M]}/M² = a_{N,M}² A_{N,N-1}²`.
-/
import UniformLanczos.Endpoint

open Set Real intervalIntegral

namespace UniformLanczos

theorem cos_odd_eq_two_sin {P : ℝ → ℝ} (hP : Continuous P) (hodd : ∀ y, P (-y) = -P y) (a : ℝ) :
    ∫ θ in (0 : ℝ)..π, cos θ * P (a * cos θ) =
      2 * ∫ θ in (0 : ℝ)..(π / 2), sin θ * P (a * sin θ) := by
  have hcont : Continuous fun θ => cos θ * P (a * cos θ) :=
    continuous_cos.mul (hP.comp (continuous_const.mul continuous_cos))
  have hsplit := integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hcont.intervalIntegrable 0 (π / 2)) (hcont.intervalIntegrable (π / 2) π)
  -- first half: θ ↦ π/2 - θ
  have h1 : ∫ θ in (0 : ℝ)..(π / 2), cos θ * P (a * cos θ) =
      ∫ θ in (0 : ℝ)..(π / 2), sin θ * P (a * sin θ) := by
    have := intervalIntegral.integral_comp_sub_left
      (fun θ => sin θ * P (a * sin θ)) (a := 0) (b := π / 2) (π / 2)
    simp only [sin_pi_div_two_sub, sub_self, sub_zero] at this
    exact this
  -- second half: θ ↦ θ + π/2
  have h2 : ∫ θ in (π / 2)..π, cos θ * P (a * cos θ) =
      ∫ θ in (0 : ℝ)..(π / 2), sin θ * P (a * sin θ) := by
    have := intervalIntegral.integral_comp_add_right
      (fun θ => cos θ * P (a * cos θ)) (a := 0) (b := π / 2) (π / 2)
    rw [show (0 : ℝ) + π / 2 = π / 2 by ring, show π / 2 + π / 2 = π by ring] at this
    rw [← this]
    apply integral_congr
    intro θ _
    simp only [cos_add_pi_div_two]
    rw [show a * -sin θ = -(a * sin θ) by ring, hodd]
    ring
  rw [← hsplit, h1, h2]; ring

theorem mrs_first_iff {P : ℝ → ℝ} (hP : Continuous P) (hodd : ∀ y, P (-y) = -P y)
    {a M N : ℝ} (hM : 0 < M) (hN : 0 < N) :
    (1 / π) * ∫ θ in (0 : ℝ)..π, cos θ * (a * M / (2 * N) * P (a * cos θ)) = 1 ↔
      Hint (fun y => y * P y) a = N / M := by
  have hpi : 0 < π := pi_pos
  have e1 : ∫ θ in (0 : ℝ)..π, cos θ * (a * M / (2 * N) * P (a * cos θ)) =
      a * M / (2 * N) * (2 * ∫ θ in (0 : ℝ)..(π / 2), sin θ * P (a * sin θ)) := by
    rw [← cos_odd_eq_two_sin hP hodd a, ← intervalIntegral.integral_const_mul]
    apply integral_congr; intro θ _; ring
  have e2 : Hint (fun y => y * P y) a = a / π * ∫ θ in (0 : ℝ)..(π / 2), sin θ * P (a * sin θ) := by
    unfold Hint
    rw [show (fun θ => a * sin θ * P (a * sin θ)) = fun θ => a * (sin θ * P (a * sin θ)) by
      funext θ; ring, intervalIntegral.integral_const_mul]
    ring
  rw [e1, e2]
  set J := ∫ θ in (0 : ℝ)..(π / 2), sin θ * P (a * sin θ)
  constructor
  · intro h
    field_simp at h ⊢
    linarith
  · intro h
    field_simp at h ⊢
    linarith

theorem mrs_second {Qp : ℝ → ℝ} (hodd : ∀ y, Qp (-y) = -Qp y) :
    ∫ θ in (0 : ℝ)..π, Qp (cos θ) = 0 := by
  have h := intervalIntegral.integral_comp_sub_left (fun θ => Qp (cos θ)) (a := 0) (b := π) π
  simp only [cos_pi_sub, hodd, sub_self, sub_zero, intervalIntegral.integral_neg] at h
  linarith

theorem beta_scaling {c hXN hXN1 hyN hyN1 : ℝ} {N : ℕ} (hc : c ≠ 0)
    (hy : 0 < hyN) (hy1 : 0 < hyN1)
    (hX : hXN = c ^ (2 * N) * hyN) (hX1 : hXN1 = c ^ (2 * (N - 1)) * hyN1) (hN : 1 ≤ N) :
    hXN / hXN1 = c ^ 2 * ((1 / Real.sqrt hyN1) / (1 / Real.sqrt hyN)) ^ 2 := by
  have hs : Real.sqrt hyN ^ 2 = hyN := Real.sq_sqrt hy.le
  have hs1 : Real.sqrt hyN1 ^ 2 = hyN1 := Real.sq_sqrt hy1.le
  have hpow : c ^ (2 * N) = c ^ 2 * c ^ (2 * (N - 1)) := by
    rw [← pow_add]; congr 1; omega
  have hsq : 0 < Real.sqrt hyN := Real.sqrt_pos.mpr hy
  have hsq1 : 0 < Real.sqrt hyN1 := Real.sqrt_pos.mpr hy1
  rw [hX, hX1, hpow, div_div_div_cancel_left' _ _ (one_ne_zero), div_pow, hs, hs1]
  have : c ^ (2 * (N - 1)) ≠ 0 := pow_ne_zero _ hc
  field_simp

end UniformLanczos
