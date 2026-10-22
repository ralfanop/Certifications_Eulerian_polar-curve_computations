/-
Uniform Lanczos note, Lemma 1 (differentiable saddlepoint estimate): the algebraic core.

Notation of the note: `Λ` is the cumulant generating function of Uniform[-1/2,1/2],
`s = s(x)` the tilt with `Λ'(s(x)) = x`, `v(x) = Λ''(s(x))`, `I` the Legendre transform.
Here `L1 = Λ'`, `L2 = Λ''`, `L3 = Λ'''` are arbitrary functions with the stated derivative
relations, so the results apply verbatim to the concrete `Λ(s) = log(sinh(s/2)/(s/2))`.

Proved here (no `sorry`):
* `tilt_first`  : `s'(x) · Λ''(s(x)) = 1`            (the coefficient `s' v - 1` of `iu` in `∂ₓΨ` vanishes);
* `tilt_second` : `s''(x) Λ''(s(x)) + s'(x)² Λ'''(s(x)) = 0`
                                                    (the coefficient of `iu` in `∂ₓ²Ψ` vanishes);
* `legendre_deriv` : `I'(x) = s(x)` for `I(x) = s(x) x - Λ(s(x))`;
* `legendre_second` : `I''(x) = s'(x) = 1 / v(x)`.
The Taylor expansion of `Ψ(x,u) = Λ(s(x)+iu) - Λ(s(x)) - iux` in `u` whose linear coefficients
these identities are, and the Fourier/Laplace analysis of the note, are not formalised here.
-/
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv

open Filter Topology

namespace UniformLanczos

/-- First-order cancellation: differentiating `Λ'(s(x)) = x` gives `s'(x) Λ''(s(x)) = 1`. -/
theorem tilt_first {L1 L2 s : ℝ → ℝ} {s1 x : ℝ}
    (hL1 : HasDerivAt L1 (L2 (s x)) (s x)) (hs : HasDerivAt s s1 x)
    (hinv : ∀ᶠ y in 𝓝 x, L1 (s y) = y) :
    s1 * L2 (s x) = 1 := by
  have h1 : HasDerivAt (fun y => L1 (s y)) (L2 (s x) * s1) x := hL1.comp x hs
  have h2 : HasDerivAt (fun y => L1 (s y)) 1 x :=
    (hasDerivAt_id x).congr_of_eventuallyEq hinv
  have := h1.unique h2
  linarith [mul_comm (L2 (s x)) s1]

/-- Second-order cancellation: differentiating `s'(y) Λ''(s(y)) = 1` gives
`s''(x) Λ''(s(x)) + s'(x)^2 Λ'''(s(x)) = 0`. -/
theorem tilt_second {L2 L3 s s1 : ℝ → ℝ} {s2 x : ℝ}
    (hL2 : HasDerivAt L2 (L3 (s x)) (s x)) (hs : HasDerivAt s (s1 x) x)
    (hs1 : HasDerivAt s1 s2 x) (hid : ∀ᶠ y in 𝓝 x, s1 y * L2 (s y) = 1) :
    s2 * L2 (s x) + s1 x ^ 2 * L3 (s x) = 0 := by
  have h1 : HasDerivAt (fun y => s1 y * L2 (s y))
      (s2 * L2 (s x) + s1 x * (L3 (s x) * s1 x)) x := hs1.mul (hL2.comp x hs)
  have h2 : HasDerivAt (fun y => s1 y * L2 (s y)) 0 x :=
    (hasDerivAt_const x (1 : ℝ)).congr_of_eventuallyEq hid
  have := h1.unique h2
  linarith [this]

/-- Both cancellations on an open set where `Λ' ∘ s = id`, with `s, s'` differentiable. -/
theorem tilt_cancellations {U : Set ℝ} (hU : IsOpen U) {L1 L2 L3 s s1 s2 : ℝ → ℝ}
    (hL1 : ∀ σ, HasDerivAt L1 (L2 σ) σ) (hL2 : ∀ σ, HasDerivAt L2 (L3 σ) σ)
    (hs : ∀ x ∈ U, HasDerivAt s (s1 x) x) (hs1 : ∀ x ∈ U, HasDerivAt s1 (s2 x) x)
    (hinv : ∀ x ∈ U, L1 (s x) = x) :
    ∀ x ∈ U, s1 x * L2 (s x) = 1 ∧ s2 x * L2 (s x) + s1 x ^ 2 * L3 (s x) = 0 := by
  have first : ∀ x ∈ U, s1 x * L2 (s x) = 1 := fun x hx =>
    tilt_first (hL1 (s x)) (hs x hx)
      (Filter.mem_of_superset (hU.mem_nhds hx) fun y hy => hinv y hy)
  intro x hx
  refine ⟨first x hx, ?_⟩
  exact tilt_second (hL2 (s x)) (hs x hx) (hs1 x hx)
    (Filter.mem_of_superset (hU.mem_nhds hx) fun y hy => first y hy)

/-- Legendre duality: for `I(y) = s(y) y - Λ(s(y))` with `Λ'(s(x)) = x`, `I'(x) = s(x)`. -/
theorem legendre_deriv {Λ L1 s : ℝ → ℝ} {s1 x : ℝ}
    (hΛ : HasDerivAt Λ (L1 (s x)) (s x)) (hs : HasDerivAt s s1 x) (hinv : L1 (s x) = x) :
    HasDerivAt (fun y => s y * y - Λ (s y)) (s x) x := by
  have h := (hs.mul (hasDerivAt_id x)).sub (hΛ.comp x hs)
  convert h using 1
  · funext y; simp [Pi.mul_apply, Pi.sub_apply, Function.comp]
  · rw [hinv]; simp; ring

/-- `I'' = s' = 1/v` with `v = Λ''(s)`: from `I' = s` and the first cancellation. -/
theorem legendre_second {L1 L2 s : ℝ → ℝ} {s1 x : ℝ}
    (hL1 : HasDerivAt L1 (L2 (s x)) (s x)) (hs : HasDerivAt s s1 x)
    (hinv : ∀ᶠ y in 𝓝 x, L1 (s y) = y) (hv : L2 (s x) ≠ 0) :
    s1 = 1 / L2 (s x) := by
  have := tilt_first hL1 hs hinv
  field_simp
  linarith [this]

end UniformLanczos
