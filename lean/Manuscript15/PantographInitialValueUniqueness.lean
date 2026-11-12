import Manuscript15.PantographDyadicUniqueContinuation
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Order.Compact

/-!
# Manuscript 15 — true global Cauchy uniqueness for the nonlinear pantograph equation

Consider the exact nonlinear pantograph differential equation
    y'(t) = 1 - 2 y(t/2)^2
for a globally differentiable real function y.

We now prove the missing SINGLE-INITIAL-VALUE uniqueness theorem,
without assuming analyticity, a Taylor series, or prior agreement
of the two solutions on a neighborhood. If f and g both satisfy
the pantograph equation for all real t and f(0)=g(0), then f=g
throughout the real line.

The local Cauchy-uniqueness argument is analytic and constructive:
1. On [-1,1], the continuous f+g is bounded by a finite constant K.
2. Choose R>0 sufficiently small that 2KR ≤ 1/2.
3. The continuous difference f-g achieves its maximal absolute
   value M on the compact symmetric interval [-R,R].
4. At each t in [-R,R], the nonlinear factorization
       (f-g)'(t) = -2(f(t/2)+g(t/2))(f(t/2)-g(t/2))
   yields |(f-g)'(t)| ≤ 2KM.
5. The mean-value bound, applied between 0 and a maximizing point,
   forces M ≤ 2KRM ≤ M/2, so M=0.
6. The previous fully formalized dyadic unique-continuation theorem
   propagates equality from [-R,R] to all ℝ.

This gives genuine global differentiable Cauchy uniqueness from one
initial value, not a conditional formal series theorem. It does not
by itself assert the existence of a solution, but the independent
certified sine solution supplies existence for initial value 0.
-/

noncomputable section
namespace Manuscript15

open Set Filter Topology

/-- A full mathematical Cauchy uniqueness theorem for the nonlinear
Eulerian pantograph equation: equality of a SINGLE initial value at
zero forces equality of any two globally differentiable solutions
throughout the entire real line. No analyticity hypothesis. -/
theorem pantograph_eq_of_initial_value
    (f g : ℝ → ℝ)
    (hf : SolvesEulerianPantograph f)
    (hg : SolvesEulerianPantograph g)
    (hfg0 : f 0 = g 0) :
    f = g := by
  have hfDiff : Differentiable ℝ f :=
    fun t => (hf t).differentiableAt
  have hgDiff : Differentiable ℝ g :=
    fun t => (hg t).differentiableAt
  have hcont : Continuous (fun x : ℝ => f x + g x) :=
    hfDiff.continuous.add hgDiff.continuous
  obtain ⟨C, hC⟩ :=
    IsCompact.exists_bound_of_continuousOn
      (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1))
      (show ContinuousOn (fun x : ℝ => f x + g x) (Icc (-1 : ℝ) 1) from
        hcont.continuousOn)
  let K : ℝ := max C 1
  have hK : 0 < K := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
    (le_max_right C 1)
  have hKone : 1 ≤ K := le_max_right C 1
  have hKbound : ∀ x ∈ Icc (-1 : ℝ) 1, ‖f x + g x‖ ≤ K := by
    intro x hx
    exact (hC x hx).trans (le_max_left C 1)
  let R : ℝ := 1 / (4 * K)
  have hR : 0 < R := by
    dsimp [R]
    positivity
  have hRle : R ≤ 1 := by
    dsimp [R]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * K)]
    nlinarith
  let s : Set ℝ := Icc (-R) R
  have hzeroMem : (0 : ℝ) ∈ s := by
    change -R ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ R
    constructor <;> linarith
  have hdiff : Continuous (fun x : ℝ => ‖f x - g x‖) :=
    (hfDiff.continuous.sub hgDiff.continuous).norm
  obtain ⟨xmax, hxmax, hmax⟩ :=
    (isCompact_Icc : IsCompact s).exists_isMaxOn
      ⟨0, hzeroMem⟩ hdiff.continuousOn
  let M : ℝ := ‖f xmax - g xmax‖
  have hMpos : 0 ≤ M := norm_nonneg _
  have hM : ∀ x ∈ s, ‖f x - g x‖ ≤ M := by
    intro x hx
    exact hmax hx
  have hhalf (x : ℝ) (hx : x ∈ s) : x / 2 ∈ s := by
    change -R ≤ x / 2 ∧ x / 2 ≤ R
    have hlo : -R ≤ x := hx.1
    have hhi : x ≤ R := hx.2
    constructor <;> linarith
  have hhalfUnit (x : ℝ) (hx : x ∈ s) :
      x / 2 ∈ Icc (-1 : ℝ) 1 := by
    have h := hhalf x hx
    constructor <;> linarith
  have hDeriv (x : ℝ) (hx : x ∈ s) :
      ‖deriv (fun y : ℝ => f y - g y) x‖ ≤
        (2 * K) * M := by
    have hformula :
        deriv (fun y : ℝ => f y - g y) x =
          -2 * ((f (x / 2) + g (x / 2)) *
              (f (x / 2) - g (x / 2))) := by
      rw [deriv_sub (hf x).differentiableAt
        (hg x).differentiableAt, (hf x).deriv, (hg x).deriv]
      ring
    have hsum := hKbound (x / 2) (hhalfUnit x hx)
    have hgap := hM (x / 2) (hhalf x hx)
    calc
      ‖deriv (fun y : ℝ => f y - g y) x‖ =
          2 * (‖f (x / 2) + g (x / 2)‖ *
            ‖f (x / 2) - g (x / 2)‖) := by
              rw [hformula, norm_mul, norm_mul]
              norm_num
      _ ≤ 2 * (K * M) := by
        gcongr <;> assumption
      _ = (2 * K) * M := by ring
  have hMean :
      ‖(f xmax - g xmax) - (f 0 - g 0)‖ ≤
        ((2 * K) * M) * ‖xmax - 0‖ :=
    Convex.norm_image_sub_le_of_norm_deriv_le
      (f := fun y : ℝ => f y - g y) (s := s)
      (C := (2 * K) * M)
      (fun y _ => (hf y).differentiableAt.sub (hg y).differentiableAt)
      hDeriv (convex_Icc _ _) hzeroMem hxmax
  have hX : ‖xmax‖ ≤ R := by
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [hxmax.1], hxmax.2⟩
  have hMbound : M ≤ ((2 * K) * M) * R := by
    calc
      M = ‖(f xmax - g xmax) - (f 0 - g 0)‖ := by
        simp [M, hfg0]
      _ ≤ ((2 * K) * M) * ‖xmax - 0‖ := hMean
      _ ≤ ((2 * K) * M) * R :=
        mul_le_mul_of_nonneg_left
          (by simpa only [sub_zero] using hX)
          (mul_nonneg (mul_nonneg (by norm_num) hK.le) hMpos)
  have hCoeff : (2 * K) * R = 1 / 2 := by
    dsimp [R]
    field_simp [ne_of_gt hK]
    ring
  have hMzero : M = 0 := by
    have hle : M ≤ M / 2 := by
      calc
        M ≤ ((2 * K) * M) * R := hMbound
        _ = ((2 * K) * R) * M := by ring
        _ = M / 2 := by rw [hCoeff]; ring
    linarith
  have hlocal : EqOn f g s := by
    intro x hx
    have hbound := hM x hx
    rw [hMzero] at hbound
    have heq : f x - g x = 0 :=
      norm_eq_zero.mp (le_antisymm hbound (norm_nonneg _))
    exact sub_eq_zero.mp heq
  exact pantograph_eq_of_eqOn_near_zero f g hf hg R hR hlocal

/-- Sine is the unique globally differentiable real solution of
the exact nonlinear Eulerian pantograph equation with the SINGLE
Cauchy initial value y(0)=0. -/
theorem pantograph_unique_sine_of_initial_zero
    (f : ℝ → ℝ)
    (hf : SolvesEulerianPantograph f)
    (hzero : f 0 = 0) :
    f = Real.sin := by
  apply pantograph_eq_of_initial_value f Real.sin hf
    (fun t => sine_pantograph_hasDerivAt t)
  simpa using hzero

#print axioms Manuscript15.pantograph_eq_of_initial_value
#print axioms Manuscript15.pantograph_unique_sine_of_initial_zero

end Manuscript15
