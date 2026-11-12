import Manuscript15.PantographAntecedent
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Manuscript 15 — rigorous dyadic unique continuation for nonlinear pantograph solutions

Consider any TWO globally differentiable real solutions of the exact
nonlinear pantograph differential equation

     y'(t) = 1 - 2 y(t/2)^2.

The key structural fact is the half-argument t/2: if two solutions
agree on the CLOSED interval [-R,R], their prescribed derivatives
agree throughout the OPEN doubled interval (-2R,2R). By the
classical mean-value/constant-derivative theorem and continuity,
the solutions then coincide on the CLOSED doubled interval [-2R,2R].

Iterating the doubling step and using the Archimedean fact that
2^n R tends to infinity yields the global unique-continuation
theorem: any two globally differentiable solutions agreeing on
ONE symmetric neighborhood of zero agree on the entire real line.

This is a true conditional GLOBAL theorem for nonlinear pantograph
solutions, beyond the previously certified pointwise algebraic
pantograph substitution. It does NOT itself prove that the equation
forces two distinct solutions with only the same single initial
value y(0)=0 to agree near zero; local Cauchy uniqueness remains
a separate and essential obligation.
-/

noncomputable section
namespace Manuscript15

open Set Filter Topology

/-- The nonlinear pantograph differential equation in its genuine
real HasDerivAt form, for every point on the whole real line. -/
def SolvesEulerianPantograph (f : ℝ → ℝ) : Prop :=
  ∀ t : ℝ,
    HasDerivAt f (1 - 2 * (f (t / 2)) ^ 2) t

/-- Local agreement of two global pantograph solutions extends
rigorously from the symmetric closed interval [-R,R] to [-2R,2R].
The proof uses the exact derivative equality on an open interval,
the real mean-value theorem, and continuity at the endpoints. -/
theorem pantograph_eqOn_double_of_eqOn
    (f g : ℝ → ℝ)
    (hf : SolvesEulerianPantograph f)
    (hg : SolvesEulerianPantograph g)
    (R : ℝ) (hR : 0 < R)
    (hlocal : EqOn f g (Icc (-R) R)) :
    EqOn f g (Icc (-(2 * R)) (2 * R)) := by
  have hfDiff : Differentiable ℝ f :=
    fun t => (hf t).differentiableAt
  have hgDiff : Differentiable ℝ g :=
    fun t => (hg t).differentiableAt
  let s : Set ℝ := Ioo (-(2 * R)) (2 * R)
  have hsOpen : IsOpen s := isOpen_Ioo
  have hsConn : IsPreconnected s := isPreconnected_Ioo
  have hderiv : EqOn (deriv f) (deriv g) s := by
    intro t ht
    have ht2 : t / 2 ∈ Icc (-R) R := by
      have htl : -(2 * R) < t := ht.1
      have htr : t < 2 * R := ht.2
      constructor <;> linarith
    calc
      deriv f t = 1 - 2 * (f (t / 2)) ^ 2 := (hf t).deriv
      _ = 1 - 2 * (g (t / 2)) ^ 2 := by
        rw [hlocal ht2]
      _ = deriv g t := (hg t).deriv.symm
  have h0 : (0 : ℝ) ∈ s := by
    change -(2 * R) < (0 : ℝ) ∧ (0 : ℝ) < 2 * R
    constructor <;> linarith
  have h0eq : f 0 = g 0 := by
    apply hlocal
    constructor <;> linarith
  have hopen : EqOn f g s :=
    hsOpen.eqOn_of_deriv_eq hsConn
      hfDiff.differentiableOn hgDiff.differentiableOn
      hderiv h0 h0eq
  have hclosure : EqOn f g (closure s) :=
    hopen.closure hfDiff.continuous hgDiff.continuous
  have hNe : -(2 * R) ≠ 2 * R := by
    intro h
    linarith
  change EqOn f g (Icc (-(2 * R)) (2 * R))
  simpa only [s, closure_Ioo hNe] using hclosure

/-- GLOBAL pantograph unique continuation from equality on ANY one
positive-radius symmetric interval. The expanding dyadic intervals
eventually contain every real argument t, so local equality
propagates to all ℝ. -/
theorem pantograph_eq_of_eqOn_near_zero
    (f g : ℝ → ℝ)
    (hf : SolvesEulerianPantograph f)
    (hg : SolvesEulerianPantograph g)
    (R : ℝ) (hR : 0 < R)
    (hlocal : EqOn f g (Icc (-R) R)) :
    f = g := by
  have hIter (n : ℕ) :
      EqOn f g
        (Icc (-((2 : ℝ) ^ n * R)) ((2 : ℝ) ^ n * R)) := by
    induction n with
    | zero =>
        simpa only [pow_zero, one_mul] using hlocal
    | succ n ih =>
        have hRn : 0 < (2 : ℝ) ^ n * R :=
          mul_pos (pow_pos (by norm_num) n) hR
        have hdoubled :=
          pantograph_eqOn_double_of_eqOn f g hf hg
            ((2 : ℝ) ^ n * R) hRn ih
        simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using
          hdoubled
  have hTop :
      Tendsto (fun n : ℕ => (2 : ℝ) ^ n * R) atTop atTop :=
    Tendsto.atTop_mul_const hR
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  funext t
  obtain ⟨n, hn⟩ :=
    (hTop.eventually_gt_atTop |t|).exists
  have habs : -((2 : ℝ) ^ n * R) < t ∧
      t < (2 : ℝ) ^ n * R := abs_lt.mp hn
  exact hIter n ⟨habs.1.le, habs.2.le⟩

/-- The certified sine solution is the unique global differentiable
pantograph solution matching sin on SOME symmetric neighborhood
of zero. This does not yet claim equality based on a single initial
value alone. -/
theorem pantograph_eq_sine_of_local_agreement
    (f : ℝ → ℝ)
    (hf : SolvesEulerianPantograph f)
    (R : ℝ) (hR : 0 < R)
    (hlocal : EqOn f Real.sin (Icc (-R) R)) :
    f = Real.sin := by
  apply pantograph_eq_of_eqOn_near_zero f Real.sin hf
    (fun t => sine_pantograph_hasDerivAt t) R hR hlocal

#print axioms Manuscript15.pantograph_eqOn_double_of_eqOn
#print axioms Manuscript15.pantograph_eq_of_eqOn_near_zero
#print axioms Manuscript15.pantograph_eq_sine_of_local_agreement

end Manuscript15
