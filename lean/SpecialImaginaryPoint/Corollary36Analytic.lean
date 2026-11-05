import SpecialImaginaryPoint.Corollary36

/-!
# Manuscript 14.1, Corollary 3.6 — analytic completion

This module connects the *actual entire function*
  F(t) = ∑ n, 4^n / (2n+1)! * t^n
to the complex entire regularization
  r_E(z) = sin(z/2)/(z/2),  r_E(0)=1,
and proves the genuine second-order complex-derivative equation
  z² r_E''(z) + 2z r_E'(z) + z²/4 r_E(z) = 0
for every z ∈ ℂ. The formal operator identities remain in Corollary36.lean.
-/

namespace EulerianSpecialPoint

set_option maxHeartbeats 1000000

/-- Analytic pullback of the true double-Borel entire series. -/
noncomputable def eulerianEvenAnalytic (z : ℂ) : ℂ :=
  eulerianEntireSeries (-z ^ 2 / 16)

/-- The regularized complex sine quotient, with removable singularity filled in. -/
noncomputable def eulerianSinc (z : ℂ) : ℂ :=
  if z = 0 then 1 else Complex.sin (z / 2) / (z / 2)

/-- Cancellation of Borel's 4^n with the substitution's (-1/4)^n. -/
private theorem evenEulerian_pow_identity (z : ℂ) (n : ℕ) :
    (4 : ℂ) ^ n * (-z ^ 2 / 16) ^ n =
      (-1 : ℂ) ^ n * (z / 2) ^ (2 * n) := by
  calc
    (4 : ℂ) ^ n * (-z ^ 2 / 16) ^ n =
        ((4 : ℂ) * (-z ^ 2 / 16)) ^ n := by rw [mul_pow]
    _ = ((-1 : ℂ) * (z / 2) ^ 2) ^ n := by congr 1; ring
    _ = (-1 : ℂ) ^ n * (z / 2) ^ (2 * n) := by
      rw [mul_pow, pow_mul]

/-- Identification of every Taylor coefficient with the complex sine series. -/
private theorem evenEulerian_term_cancel (z : ℂ) (n : ℕ) :
    (z / 2) * (eulerianEntireCoeff n * (-z ^ 2 / 16) ^ n) =
    (-1 : ℂ) ^ n * (z / 2) ^ (2 * n + 1) /
      ((2 * n + 1).factorial : ℂ) := by
  calc
    (z / 2) * (eulerianEntireCoeff n * (-z ^ 2 / 16) ^ n) =
        ((z / 2) * ((4 : ℂ) ^ n * (-z ^ 2 / 16) ^ n)) /
          ((2 * n + 1).factorial : ℂ) := by
            unfold eulerianEntireCoeff
            ring
    _ = ((z / 2) * ((-1 : ℂ) ^ n * (z / 2) ^ (2 * n))) /
          ((2 * n + 1).factorial : ℂ) := by
            rw [evenEulerian_pow_identity]
    _ = (-1 : ℂ) ^ n * (z / 2) ^ (2 * n + 1) /
          ((2 * n + 1).factorial : ℂ) := by
            rw [pow_add]
            simp only [pow_one]
            ring

/-- The actual convergent double-Borel series, after pullback, satisfies
(z/2) F(-z²/16) = sin(z/2), including at zero. -/
theorem eulerianEvenAnalytic_mul_eq_sin (z : ℂ) :
    (z / 2) * eulerianEvenAnalytic z = Complex.sin (z / 2) := by
  have hf := (eulerianEntireSeries_hasSum (-z ^ 2 / 16)).mul_left (z / 2)
  have hs := Complex.hasSum_sin (z / 2)
  have hc :
      HasSum (fun n : ℕ =>
        (-1 : ℂ) ^ n * (z / 2) ^ (2 * n + 1) /
          ((2 * n + 1).factorial : ℂ))
        ((z / 2) * eulerianEvenAnalytic z) := by
    apply hf.congr_fun
    intro n
    exact (evenEulerian_term_cancel z n).symm
  exact hc.unique hs

/-- Exact function identity on all ℂ, including the removable value r_E(0)=1. -/
theorem eulerianEvenAnalytic_eq_sinc (z : ℂ) :
    eulerianEvenAnalytic z = eulerianSinc z := by
  by_cases hz : z = 0
  · subst z
    simp [eulerianEvenAnalytic, eulerianSinc, eulerianEntireSeries_zero]
  · have hz2 : (z / 2 : ℂ) ≠ 0 := div_ne_zero hz (by norm_num)
    have hm := eulerianEvenAnalytic_mul_eq_sin z
    unfold eulerianSinc
    rw [if_neg hz]
    apply (eq_div_iff hz2).2
    simpa only [mul_comm] using hm

/-- The Borel pullback is a genuine globally analytic function of z. -/
theorem eulerianEvenAnalytic_analyticAt (z : ℂ) :
    AnalyticAt ℂ eulerianEvenAnalytic z := by
  have hi : AnalyticAt ℂ (fun w : ℂ => w) z := analyticAt_id
  have hs : AnalyticAt ℂ (fun w : ℂ => w ^ 2) z := by
    simpa only [id_eq] using hi.fun_pow 2
  have hn : AnalyticAt ℂ (fun w : ℂ => -(w ^ 2)) z := by
    simpa only [Pi.neg_apply] using hs.fun_neg
  have hp : AnalyticAt ℂ (fun w : ℂ => -w ^ 2 / 16) z := by
    simpa only [Pi.div_apply] using hn.div_const
  have hg : AnalyticAt ℂ eulerianEntireSeries (-z ^ 2 / 16) :=
    eulerianEntireSeries_analyticAt _
  have hc : AnalyticAt ℂ (fun w : ℂ => eulerianEntireSeries (-w ^ 2 / 16)) z :=
    AnalyticAt.fun_comp hg hp
  exact hc

private theorem sin_half_scaled_deriv (z : ℂ) :
    deriv (fun w : ℂ => 2 * Complex.sin (w / 2)) z =
      Complex.cos (z / 2) := by
  have hs : HasDerivAt (fun w : ℂ => Complex.sin (w / 2))
      (Complex.cos (z / 2) * (1 / 2)) z := by
    simpa only [id_eq] using ((hasDerivAt_id z).div_const 2).csin
  calc
    deriv (fun w : ℂ => 2 * Complex.sin (w / 2)) z =
      2 * (Complex.cos (z / 2) * (1 / 2)) := (hs.const_mul 2).deriv
    _ = Complex.cos (z / 2) := by ring

private theorem cos_half_deriv (z : ℂ) :
    deriv (fun w : ℂ => Complex.cos (w / 2)) z =
      -Complex.sin (z / 2) / 2 := by
  have hs : HasDerivAt (fun w : ℂ => Complex.cos (w / 2))
      (-Complex.sin (z / 2) * (1 / 2)) z := by
    simpa only [id_eq] using ((hasDerivAt_id z).div_const 2).ccos
  calc
    deriv (fun w : ℂ => Complex.cos (w / 2)) z =
      -Complex.sin (z / 2) * (1 / 2) := hs.deriv
    _ = -Complex.sin (z / 2) / 2 := by ring

/-- First derivative identity of actual analytic functions, valid at zero. -/
theorem eulerianEvenAnalytic_deriv_relation (z : ℂ) :
    eulerianEvenAnalytic z + z * deriv eulerianEvenAnalytic z =
      Complex.cos (z / 2) := by
  have hfun :
      (fun w : ℂ => w * eulerianEvenAnalytic w) =
      (fun w : ℂ => 2 * Complex.sin (w / 2)) := by
    funext w
    calc
      w * eulerianEvenAnalytic w =
          2 * ((w / 2) * eulerianEvenAnalytic w) := by ring
      _ = 2 * Complex.sin (w / 2) := by
          rw [eulerianEvenAnalytic_mul_eq_sin]
  have hder := (hasDerivAt_id z).mul
    (eulerianEvenAnalytic_analyticAt z).differentiableAt.hasDerivAt
  have hfunction : (id * eulerianEvenAnalytic) =
      (fun w : ℂ => w * eulerianEvenAnalytic w) := by
    funext w
    rfl
  rw [hfunction] at hder
  have heqprod :
      id * eulerianEvenAnalytic =
      (fun w : ℂ => w * eulerianEvenAnalytic w) := by
    funext w
    rfl
  calc
    eulerianEvenAnalytic z + z * deriv eulerianEvenAnalytic z =
      deriv (fun w : ℂ => w * eulerianEvenAnalytic w) z := by
        simpa [id_eq] using hder.deriv.symm
    _ = deriv (fun w : ℂ => 2 * Complex.sin (w / 2)) z := by rw [hfun]
    _ = Complex.cos (z / 2) := sin_half_scaled_deriv z

/-- Second derivative identity obtained from the first one, with no division
by z; hence it also applies at the removable singularity. -/
theorem eulerianEvenAnalytic_second_deriv_relation (z : ℂ) :
    2 * deriv eulerianEvenAnalytic z +
      z * deriv (deriv eulerianEvenAnalytic) z =
      -Complex.sin (z / 2) / 2 := by
  have hfun :
      (fun w : ℂ =>
        eulerianEvenAnalytic w + w * deriv eulerianEvenAnalytic w) =
      (fun w : ℂ => Complex.cos (w / 2)) := by
    funext w
    exact eulerianEvenAnalytic_deriv_relation w
  have hd := (eulerianEvenAnalytic_analyticAt z).differentiableAt.hasDerivAt
  have hdd := ((eulerianEvenAnalytic_analyticAt z).deriv).differentiableAt.hasDerivAt
  have hder := hd.add ((hasDerivAt_id z).mul hdd)
  have hfunction : (eulerianEvenAnalytic + id * deriv eulerianEvenAnalytic) =
      (fun w : ℂ => eulerianEvenAnalytic w + w * deriv eulerianEvenAnalytic w) := by
    funext w
    rfl
  rw [hfunction] at hder
  have heqsum :
      eulerianEvenAnalytic + id * deriv eulerianEvenAnalytic =
      (fun w : ℂ =>
        eulerianEvenAnalytic w + w * deriv eulerianEvenAnalytic w) := by
    funext w
    rfl
  calc
    2 * deriv eulerianEvenAnalytic z +
      z * deriv (deriv eulerianEvenAnalytic) z =
      deriv (fun w : ℂ =>
        eulerianEvenAnalytic w + w * deriv eulerianEvenAnalytic w) z := by
          calc
            _ = deriv eulerianEvenAnalytic z +
                  (1 * deriv eulerianEvenAnalytic z +
                    (id z) * deriv (deriv eulerianEvenAnalytic) z) := by
                      simp only [id_eq]
                      ring
            _ = deriv (eulerianEvenAnalytic + id * deriv eulerianEvenAnalytic) z :=
                  hder.deriv.symm
            _ = deriv (fun w : ℂ =>
                  eulerianEvenAnalytic w + w * deriv eulerianEvenAnalytic w) z := by
                    rw [heqsum]
    _ = deriv (fun w : ℂ => Complex.cos (w / 2)) z := by rw [hfun]
    _ = -Complex.sin (z / 2) / 2 := cos_half_deriv z

/-- The analytic Corollary 3.6 ODE for genuine first/second complex
derivatives, globally (including z=0). This is stronger than the
earlier coefficient-level equation. -/
theorem eulerianEvenAnalytic_differential_eq (z : ℂ) :
    z ^ 2 * deriv (deriv eulerianEvenAnalytic) z +
      2 * z * deriv eulerianEvenAnalytic z +
      z ^ 2 / 4 * eulerianEvenAnalytic z = 0 := by
  have h1 := eulerianEvenAnalytic_mul_eq_sin z
  have h2 := eulerianEvenAnalytic_second_deriv_relation z
  calc
    z ^ 2 * deriv (deriv eulerianEvenAnalytic) z +
      2 * z * deriv eulerianEvenAnalytic z +
      z ^ 2 / 4 * eulerianEvenAnalytic z =
        z * (2 * deriv eulerianEvenAnalytic z +
          z * deriv (deriv eulerianEvenAnalytic) z) +
        (z / 2) * ((z / 2) * eulerianEvenAnalytic z) := by ring
    _ = z * (-Complex.sin (z / 2) / 2) +
          (z / 2) * Complex.sin (z / 2) := by rw [h2, h1]
    _ = 0 := by ring

#print axioms EulerianSpecialPoint.eulerianEvenAnalytic_mul_eq_sin
#print axioms EulerianSpecialPoint.eulerianEvenAnalytic_eq_sinc
#print axioms EulerianSpecialPoint.eulerianEvenAnalytic_analyticAt
#print axioms EulerianSpecialPoint.eulerianEvenAnalytic_deriv_relation
#print axioms EulerianSpecialPoint.eulerianEvenAnalytic_second_deriv_relation
#print axioms EulerianSpecialPoint.eulerianEvenAnalytic_differential_eq

end EulerianSpecialPoint
