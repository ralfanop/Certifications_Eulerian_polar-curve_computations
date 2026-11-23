import UniformLanczos.Lemma513Legendre
import Mathlib

/-!
# M12 Lemma 5.13, second inequality (158): combining the two reflected tails

This original *assembly* applies the already certified one-sided weighted
endpoint bound (159), `Lemma513Legendre.second_tail_half`, to both ends of
the symmetric cardinal B-spline support.

For the left end, the integration variable is reflected: the functions
are `p_k(-x)`, `p_{k-1}(-x)` and `g_M(-x)` on a positive interval.
The derivative of the reflected weight is `-g'_M(-x)`. Each derivative
identity, monotonicity condition, the classical endpoint-Christoffel
polynomial estimate and the first unweighted exponentially small tail
are explicit inputs, not new axioms.

The output is the two-sided factor 2 (k+1)^2 exp(-cM), matching the
second bound in (158) once the actual weight and first tail are supplied.
No classical Christoffel or change-of-variable theorem is reproved.
-/

namespace UniformLanczos.Lemma513ReflectedTails

open intervalIntegral Set MeasureTheory

/-- Second inequality of (158), in positive coordinates for both reflected
half-lines. The hypotheses are precisely the published endpoint polynomial
estimate, weight derivatives and previously proved first-tail inputs for
the original and reflected functions. -/
theorem two_reflected_tails
    (pk pk1 g g' : ℝ → ℝ) {s r b M c : ℝ} (k : ℕ)
    (hsr : s < r) (hrb : r ≤ b)
    (hM : 0 < M) (hscale : 1 ≤ M * (r - s))
    (hpk : Continuous pk) (hpk1 : Continuous pk1)
    (hgPlus : ∀ x ∈ Icc s b, HasDerivAt g (g' x) x)
    (hgMinus : ∀ x ∈ Icc s b,
       HasDerivAt (fun y : ℝ => g (-y)) (-(g' (-x))) x)
    (hgiPlus : IntervalIntegrable g' volume r b)
    (hgiMinus : IntervalIntegrable (fun x : ℝ => -(g' (-x))) volume r b)
    (hmonoPlus : AntitoneOn g (Icc s b))
    (hmonoMinus : AntitoneOn (fun x : ℝ => g (-x)) (Icc s b))
    (hgbPlus : 0 ≤ g b) (hgbMinus : 0 ≤ g (-b))
    (hnegPlus : ∀ x ∈ Icc r b, g' x ≤ 0)
    (hnegMinus : ∀ x ∈ Icc r b, -(g' (-x)) ≤ 0)
    (hLegPlus : ∀ x ∈ Icc r b,
       pk x ^ 2 ≤ ((k:ℝ)+1)^2/(x-s) * ∫ y in s..x, pk y ^ 2)
    (hLegPlus1 : ∀ x ∈ Icc r b,
       pk1 x ^ 2 ≤ ((k:ℝ)+1)^2/(x-s) * ∫ y in s..x, pk1 y ^ 2)
    (hLegMinus : ∀ x ∈ Icc r b,
       pk (-x) ^ 2 ≤ ((k:ℝ)+1)^2/(x-s) * ∫ y in s..x, pk (-y) ^ 2)
    (hLegMinus1 : ∀ x ∈ Icc r b,
       pk1 (-x) ^ 2 ≤ ((k:ℝ)+1)^2/(x-s) * ∫ y in s..x, pk1 (-y) ^ 2)
    (hTailPlus : ∫ y in s..b, pk y ^ 2 * g y ≤ Real.exp (-c*M))
    (hTailPlus1 : ∫ y in s..b, pk1 y ^ 2 * g y ≤ Real.exp (-c*M))
    (hTailMinus : ∫ y in s..b, pk (-y) ^ 2 * g (-y) ≤ Real.exp (-c*M))
    (hTailMinus1 : ∫ y in s..b, pk1 (-y) ^ 2 * g (-y) ≤ Real.exp (-c*M)) :
    (∫ x in r..b, |pk x * pk1 x| * (-g' x / M)) +
      (∫ x in r..b, |pk (-x) * pk1 (-x)| * (-(-(g' (-x))) / M))
      ≤ 2 * ((k:ℝ)+1)^2 * Real.exp (-c*M) := by
  have hcontinuousMinus : Continuous (fun x : ℝ => pk (-x)) :=
    hpk.comp continuous_neg
  have hcontinuousMinus1 : Continuous (fun x : ℝ => pk1 (-x)) :=
    hpk1.comp continuous_neg
  have hPlus := UniformLanczos.Lemma513Legendre.second_tail_half
    (K := ((k:ℝ)+1)^2) (T := Real.exp (-c*M)) (M := M)
    pk pk1 g g' hsr hrb (sq_nonneg _) hM
    hpk hpk1 hgPlus hgiPlus hmonoPlus hgbPlus hnegPlus
    hLegPlus hLegPlus1 hTailPlus hTailPlus1
  have hMinus := UniformLanczos.Lemma513Legendre.second_tail_half
    (K := ((k:ℝ)+1)^2) (T := Real.exp (-c*M)) (M := M)
    (fun x : ℝ => pk (-x)) (fun x : ℝ => pk1 (-x))
    (fun x : ℝ => g (-x)) (fun x : ℝ => -(g' (-x)))
    hsr hrb (sq_nonneg _) hM hcontinuousMinus hcontinuousMinus1
    hgMinus hgiMinus hmonoMinus hgbMinus hnegMinus
    hLegMinus hLegMinus1 hTailMinus hTailMinus1
  have hScale := UniformLanczos.Lemma513Legendre.second_tail_exp
    (k := k) (c := c) (M := M) (r := r) (s := s) hscale
  calc
    (∫ x in r..b, |pk x * pk1 x| * (-g' x / M)) +
      (∫ x in r..b, |pk (-x) * pk1 (-x)| * (-(-(g' (-x))) / M))
        ≤ ((k:ℝ)+1)^2 * Real.exp (-c*M) / (M * (r-s)) +
          ((k:ℝ)+1)^2 * Real.exp (-c*M) / (M * (r-s)) :=
            add_le_add hPlus hMinus
    _ ≤ ((k:ℝ)+1)^2 * Real.exp (-c*M) +
          ((k:ℝ)+1)^2 * Real.exp (-c*M) :=
            add_le_add hScale hScale
    _ = 2 * ((k:ℝ)+1)^2 * Real.exp (-c*M) := by ring

end UniformLanczos.Lemma513ReflectedTails

#print axioms UniformLanczos.Lemma513ReflectedTails.two_reflected_tails
