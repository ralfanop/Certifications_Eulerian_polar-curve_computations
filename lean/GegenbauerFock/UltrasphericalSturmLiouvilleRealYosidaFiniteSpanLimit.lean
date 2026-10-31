import GegenbauerFock.UltrasphericalSturmLiouvilleRealYosidaExponentialModeLimit
import Mathlib.Topology.Algebra.ConstMulAction

/-!
# V007 — strong semigroup convergence on finite Gegenbauer spectral sums

This strengthens exact normalized-eigenmode convergence to arbitrary
FINITE linear combinations of the actual normalized Gegenbauer basis.
For every fixed real s, and each fixed finite sum f, the genuine
weighted L² bounded Yosida semigroup converges strongly along positive
integer shifts to the corresponding finite spectral heat expansion.

The separate extension to arbitrary L² requires a bounded-limit
density argument; it is not assumed here.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory Filter
open scoped Topology

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- Actual finite sum of normalized real Gegenbauer eigenmodes. -/
noncomputable def sturmRealGegenbauerFiniteVector
    (lam : ℝ) (hlam : 0 < lam)
    (F : Finset ℕ) (a : ℕ → ℝ) : SturmH lam :=
  ∑ n ∈ F, (a n) • sturmMonicEigenCandidate_realL2_normalized lam hlam n

/-- Finite Gegenbauer expansion with the exact limiting heat weights. -/
noncomputable def sturmRealGegenbauerFiniteHeatVector
    (lam : ℝ) (hlam : 0 < lam)
    (F : Finset ℕ) (a : ℕ → ℝ) (s : ℝ) : SturmH lam :=
  ∑ n ∈ F,
    (a n) • ((Real.exp (-s * ((n : ℝ) * ((n : ℝ) + 2 * lam)))) •
      sturmMonicEigenCandidate_realL2_normalized lam hlam n)

/-- Strong bounded-Yosida-to-heat convergence for every finite
Gegenbauer linear combination, without any unbounded semigroup. -/
theorem sturmRealYosidaExponential_finiteGegenbauer_tendsto
    (lam : ℝ) (hlam : 0 < lam)
    (F : Finset ℕ) (a : ℕ → ℝ) (s : ℝ) :
    Tendsto
      (fun k : ℕ =>
        sturmRealYosidaExponential lam ((k : ℝ) + 1) hlam
          (by positivity : 0 < (k : ℝ) + 1) s
          (sturmRealGegenbauerFiniteVector lam hlam F a))
      atTop
      (𝓝 (sturmRealGegenbauerFiniteHeatVector lam hlam F a s)) := by
  let v : ℕ → SturmH lam :=
    sturmMonicEigenCandidate_realL2_normalized lam hlam
  let w : ℕ → ℝ :=
    fun n => Real.exp (-s * ((n : ℝ) * ((n : ℝ) + 2 * lam)))
  have hmode (n : ℕ) :
      Tendsto
        (fun k : ℕ =>
          (a n) •
            (sturmRealYosidaExponential lam ((k : ℝ) + 1) hlam
              (by positivity : 0 < (k : ℝ) + 1) s (v n)))
        atTop (𝓝 ((a n) • ((w n) • v n))) := by
    exact
      (sturmRealYosidaExponential_Gegenbauer_mode_tendsto lam hlam n s).const_smul (a n)
  have hfinite :
      Tendsto
        (fun k : ℕ =>
          ∑ n ∈ F,
            (a n) •
              (sturmRealYosidaExponential lam ((k : ℝ) + 1) hlam
                (by positivity : 0 < (k : ℝ) + 1) s (v n)))
        atTop
        (𝓝 (∑ n ∈ F, (a n) • ((w n) • v n))) := by
    induction F using Finset.induction_on with
    | empty =>
        simp
    | @insert n F hn ih =>
        simp only [Finset.sum_insert hn]
        exact (hmode n).add ih
  convert hfinite using 1
  · ext k
    change
      (sturmRealYosidaExponential lam ((k : ℝ) + 1) hlam
          (by positivity : 0 < (k : ℝ) + 1) s)
        (∑ n ∈ F, (a n) • v n) = _
    simp only [map_sum, map_smul]
  · rfl

#print axioms GegenbauerFock.Ultraspherical.sturmRealYosidaExponential_finiteGegenbauer_tendsto

end GegenbauerFock.Ultraspherical
