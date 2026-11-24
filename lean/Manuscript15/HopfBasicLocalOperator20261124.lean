import Manuscript15.HopfLocalLaplacian20261124
import Mathlib

/-!
# M15 actual local operator intertwining on arbitrary C² scalar sections

Source: the new 15.tex, Proposition prop:hopf-basic-laplace.
The previously certified actual Hopf angular chart and metric
lead to equality of local Laplacian coefficients. Here the
complete one-dimensional C² chain rule is applied to ACTUAL
first and second derivatives of arbitrary scalar fields f(θ,φ).
This proves the local operator identity in every regular angular
chart, not just a symbolic substitution for arbitrary jets.

The intrinsic global quotient CP¹/S³, extension across the
singular chart poles, and Fefferman Lorentzian d'Alembertian
are NOT certified by this module.
-/

namespace Manuscript15.HopfBasicLocalOperator20261124

open Manuscript15.HopfLocalLaplacian20261124

/-- True first scalar derivative of g(2x). -/
theorem deriv_double_argument (g : ℝ → ℝ) (hg : Differentiable ℝ g) (x : ℝ) :
    deriv (fun t : ℝ => g (2 * t)) x = 2 * deriv g (2 * x) := by
  have hlin : HasDerivAt (fun t : ℝ => 2 * t) 2 x := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id x).const_mul (2 : ℝ))
  have h := (hg (2 * x)).hasDerivAt.comp x hlin
  simpa only [Function.comp_def, mul_comm] using h.deriv

/-- True second scalar derivative of g(2x). -/
theorem second_deriv_double_argument (g : ℝ → ℝ)
    (hg : Differentiable ℝ g) (hg2 : Differentiable ℝ (deriv g))
    (x : ℝ) :
    deriv (fun t : ℝ => deriv (fun s : ℝ => g (2 * s)) t) x =
      4 * deriv (deriv g) (2 * x) := by
  have hfun :
      (fun t : ℝ => deriv (fun s : ℝ => g (2 * s)) t) =
        (fun t : ℝ => 2 * deriv g (2 * t)) := by
    funext t
    exact deriv_double_argument g hg t
  rw [hfun]
  have hlin : HasDerivAt (fun t : ℝ => 2 * t) 2 x := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id x).const_mul (2 : ℝ))
  have hout := (hg2 (2 * x)).hasDerivAt.comp x hlin
  have h := hout.const_mul (2 : ℝ)
  have hder : deriv (fun t : ℝ => 2 * deriv g (2 * t)) x =
      2 * (deriv (deriv g) (2 * x) * 2) := by
    simpa only [Function.comp_def] using h.deriv
  rw [hder]
  ring

/-- First chain rule for a translated scalar argument. -/
theorem deriv_sub_const_argument (g : ℝ → ℝ)
    (hg : Differentiable ℝ g) (c x : ℝ) :
    deriv (fun t : ℝ => g (t - c)) x = deriv g (x - c) := by
  have hlin : HasDerivAt (fun t : ℝ => t - c) 1 x :=
    (hasDerivAt_id x).sub_const c
  have h := (hg (x - c)).hasDerivAt.comp x hlin
  simpa only [Function.comp_def, mul_one] using h.deriv

/-- Second chain rule for a translated scalar argument. -/
theorem second_deriv_sub_const_argument (g : ℝ → ℝ)
    (hg : Differentiable ℝ g) (hg2 : Differentiable ℝ (deriv g))
    (c x : ℝ) :
    deriv (fun t : ℝ => deriv (fun s : ℝ => g (s - c)) t) x =
      deriv (deriv g) (x - c) := by
  have hfun :
      (fun t : ℝ => deriv (fun s : ℝ => g (s - c)) t) =
        (fun t : ℝ => deriv g (t - c)) := by
    funext t
    exact deriv_sub_const_argument g hg c t
  rw [hfun]
  exact deriv_sub_const_argument (deriv g) hg2 c x

/-- First chain rule for a reversed translated scalar argument. -/
theorem deriv_const_sub_argument (g : ℝ → ℝ)
    (hg : Differentiable ℝ g) (c x : ℝ) :
    deriv (fun t : ℝ => g (c - t)) x = -deriv g (c - x) := by
  have hlin : HasDerivAt (fun t : ℝ => c - t) (-1) x :=
    (hasDerivAt_id x).const_sub c
  have h := (hg (c - x)).hasDerivAt.comp x hlin
  simpa only [Function.comp_def, mul_neg, mul_one] using h.deriv

/-- Second chain rule: the two reversed derivatives cancel signs. -/
theorem second_deriv_const_sub_argument (g : ℝ → ℝ)
    (hg : Differentiable ℝ g) (hg2 : Differentiable ℝ (deriv g))
    (c x : ℝ) :
    deriv (fun t : ℝ => deriv (fun s : ℝ => g (c - s)) t) x =
      deriv (deriv g) (c - x) := by
  have hfun :
      (fun t : ℝ => deriv (fun s : ℝ => g (c - s)) t) =
        (fun t : ℝ => -deriv g (c - t)) := by
    funext t
    exact deriv_const_sub_argument g hg c t
  rw [hfun]
  have hlin : HasDerivAt (fun t : ℝ => c - t) (-1) x :=
    (hasDerivAt_id x).const_sub c
  have hout := (hg2 (c - x)).hasDerivAt.comp x hlin
  have h := hout.neg
  have hfunNeg :
      (fun t : ℝ => -deriv g (c - t)) =
      -(fun t : ℝ => deriv g (c - t)) := by
    funext t
    rfl
  rw [hfunNeg]
  simpa only [Function.comp_def, mul_neg, mul_one, neg_neg] using h.deriv

/-- Actual Hopf-basic scalar pullback in the real angular chart. -/
def localBasicField (f : ℝ → ℝ → ℝ) (η α β : ℝ) : ℝ :=
  f (2 * η) (α - β)

noncomputable def localEtaDeriv (f : ℝ → ℝ → ℝ) (η α β : ℝ) : ℝ :=
  deriv (fun t : ℝ => localBasicField f t α β) η

noncomputable def localEtaSecond (f : ℝ → ℝ → ℝ) (η α β : ℝ) : ℝ :=
  deriv (fun t : ℝ => localEtaDeriv f t α β) η

noncomputable def localAlphaDeriv (f : ℝ → ℝ → ℝ) (η α β : ℝ) : ℝ :=
  deriv (fun t : ℝ => localBasicField f η t β) α

noncomputable def localAlphaSecond (f : ℝ → ℝ → ℝ) (η α β : ℝ) : ℝ :=
  deriv (fun t : ℝ => localAlphaDeriv f η t β) α

noncomputable def localBetaDeriv (f : ℝ → ℝ → ℝ) (η α β : ℝ) : ℝ :=
  deriv (fun t : ℝ => localBasicField f η α t) β

noncomputable def localBetaSecond (f : ℝ → ℝ → ℝ) (η α β : ℝ) : ℝ :=
  deriv (fun t : ℝ => localBetaDeriv f η α t) β

noncomputable def baseThetaDeriv (f : ℝ → ℝ → ℝ) (θ φ : ℝ) : ℝ :=
  deriv (fun t : ℝ => f t φ) θ

noncomputable def baseThetaSecond (f : ℝ → ℝ → ℝ) (θ φ : ℝ) : ℝ :=
  deriv (fun t : ℝ => baseThetaDeriv f t φ) θ

noncomputable def basePhiDeriv (f : ℝ → ℝ → ℝ) (θ φ : ℝ) : ℝ :=
  deriv (fun t : ℝ => f θ t) φ

noncomputable def basePhiSecond (f : ℝ → ℝ → ℝ) (θ φ : ℝ) : ℝ :=
  deriv (fun t : ℝ => basePhiDeriv f θ t) φ

/-- Local divergence-of-gradient on the round S³ chart,
evaluated at TRUE scalar derivatives of the Hopf-basic field. -/
noncomputable def localS3LaplaceBasic (f : ℝ → ℝ → ℝ)
    (η α β : ℝ) : ℝ :=
  localEtaSecond f η α β +
    (Real.cos η / Real.sin η - Real.sin η / Real.cos η) *
      localEtaDeriv f η α β +
    (1 / Real.cos η ^ 2) * localAlphaSecond f η α β +
    (1 / Real.sin η ^ 2) * localBetaSecond f η α β

/-- True local radius-1/2 Fubini--Study Laplacian in θ,φ. -/
noncomputable def localFSLaplace (f : ℝ → ℝ → ℝ) (θ φ : ℝ) : ℝ :=
  4 * (baseThetaSecond f θ φ +
    (Real.cos θ / Real.sin θ) * baseThetaDeriv f θ φ +
    (1 / Real.sin θ ^ 2) * basePhiSecond f θ φ)

/-- ACTUAL LOCAL Hopf–Laplace operator intertwining for arbitrary
twice differentiable θ/φ scalar sections, away from poles.
Unlike a symbolic 2-jet identity, the operators on both sides
are defined using the genuine real first and second derivatives
of f and of its explicit Hopf-basic pullback. -/
theorem actual_local_hopf_laplacian_intertwining
    (f : ℝ → ℝ → ℝ) (η α β : ℝ)
    (hs : Real.sin η ≠ 0) (hc : Real.cos η ≠ 0)
    (hθ : Differentiable ℝ (fun θ => f θ (α - β)))
    (hθ2 : Differentiable ℝ
      (deriv (fun θ : ℝ => f θ (α - β))))
    (hφ : Differentiable ℝ (fun φ => f (2 * η) φ))
    (hφ2 : Differentiable ℝ
      (deriv (fun φ : ℝ => f (2 * η) φ))) :
    localS3LaplaceBasic f η α β =
      localFSLaplace f (2 * η) (α - β) := by
  let A := baseThetaSecond f (2 * η) (α - β)
  let B := baseThetaDeriv f (2 * η) (α - β)
  let C := basePhiSecond f (2 * η) (α - β)
  have hη : localEtaDeriv f η α β = 2 * B := by
    change deriv (fun t : ℝ => f (2 * t) (α - β)) η =
      2 * deriv (fun t : ℝ => f t (α - β)) (2 * η)
    exact deriv_double_argument _ hθ η
  have hη2 : localEtaSecond f η α β = 4 * A := by
    change deriv (fun t : ℝ =>
      deriv (fun s : ℝ => f (2 * s) (α - β)) t) η =
      4 * deriv (fun t : ℝ =>
        deriv (fun s : ℝ => f s (α - β)) t) (2 * η)
    exact second_deriv_double_argument _ hθ hθ2 η
  have hα2 : localAlphaSecond f η α β = C := by
    change deriv (fun t : ℝ =>
      deriv (fun s : ℝ => f (2 * η) (s - β)) t) α =
      deriv (fun t : ℝ =>
        deriv (fun s : ℝ => f (2 * η) s) t) (α - β)
    exact second_deriv_sub_const_argument _ hφ hφ2 β α
  have hβ2 : localBetaSecond f η α β = C := by
    change deriv (fun t : ℝ =>
      deriv (fun s : ℝ => f (2 * η) (α - s)) t) β =
      deriv (fun t : ℝ =>
        deriv (fun s : ℝ => f (2 * η) s) t) (α - β)
    exact second_deriv_const_sub_argument _ hφ hφ2 α β
  have hcoeff : hopfS3LocalTrace η A B C =
      baseSphereLocalTrace (2 * η) A B C :=
    hopf_local_laplacian_coefficient_identity η A B C hs hc
  calc
    localS3LaplaceBasic f η α β =
        4 * A +
          (Real.cos η / Real.sin η - Real.sin η / Real.cos η) * (2 * B) +
          (1 / Real.cos η ^ 2) * C +
          (1 / Real.sin η ^ 2) * C := by
      unfold localS3LaplaceBasic
      rw [hη2, hη, hα2, hβ2]
    _ = hopfS3LocalTrace η A B C := by
      dsimp [hopfS3LocalTrace]
      ring
    _ = baseSphereLocalTrace (2 * η) A B C := hcoeff
    _ = localFSLaplace f (2 * η) (α - β) := by
      dsimp [baseSphereLocalTrace, localFSLaplace, A, B, C]

#print axioms Manuscript15.HopfBasicLocalOperator20261124.deriv_double_argument
#print axioms Manuscript15.HopfBasicLocalOperator20261124.second_deriv_double_argument
#print axioms Manuscript15.HopfBasicLocalOperator20261124.deriv_sub_const_argument
#print axioms Manuscript15.HopfBasicLocalOperator20261124.second_deriv_sub_const_argument
#print axioms Manuscript15.HopfBasicLocalOperator20261124.deriv_const_sub_argument
#print axioms Manuscript15.HopfBasicLocalOperator20261124.second_deriv_const_sub_argument
#print axioms Manuscript15.HopfBasicLocalOperator20261124.actual_local_hopf_laplacian_intertwining

end Manuscript15.HopfBasicLocalOperator20261124
