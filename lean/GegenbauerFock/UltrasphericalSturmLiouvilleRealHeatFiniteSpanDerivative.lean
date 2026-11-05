import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatModeDerivative
import GegenbauerFock.UltrasphericalSturmLiouvilleRealYosidaFiniteSpanLimit
import Mathlib.Topology.Algebra.ConstMulAction

/-!
# V007 — right derivative of the genuine heat semigroup on the finite spectral core

The strong heat semigroup has the correct infinitesimal generator action
not merely on each eigenmode, but on every finite real linear combination
of normalized Gegenbauer modes in the actual weighted L2 space.

Extension to the entire closed graph domain by dominated convergence
is an independent, explicitly outstanding theorem.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory Filter
open scoped Topology

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- The exact finite spectral expression of the closed Sturm generator. -/
noncomputable def sturmRealGegenbauerFiniteGeneratorVector
    (lam : ℝ) (hlam : 0 < lam)
    (F : Finset ℕ) (a : ℕ → ℝ) : SturmH lam :=
  ∑ n ∈ F, (a n) • ((-((n : ℝ) * ((n : ℝ) + 2 * lam))) •
    sturmMonicEigenCandidate_realL2_normalized lam hlam n)

/-- On every finite combination of genuine Gegenbauer modes, the right
difference quotient of the actual heat semigroup tends in weighted L2
to the precise finite Sturm spectral generator action. -/
theorem sturmRealHeatLimit_finiteGegenbauer_right_slope
    (lam : ℝ) (hlam : 0 < lam)
    (F : Finset ℕ) (a : ℕ → ℝ) :
    Tendsto
      (fun s : ℝ =>
        s⁻¹ • (sturmRealHeatLimitNonnegativeExtended lam hlam s
          (sturmRealGegenbauerFiniteVector lam hlam F a) -
          sturmRealGegenbauerFiniteVector lam hlam F a))
      (𝓝[>] (0 : ℝ))
      (𝓝 (sturmRealGegenbauerFiniteGeneratorVector lam hlam F a)) := by
  let v : ℕ → SturmH lam :=
    sturmMonicEigenCandidate_realL2_normalized lam hlam
  let T : ℝ → SturmH lam →L[ℝ] SturmH lam :=
    sturmRealHeatLimitNonnegativeExtended lam hlam
  have hmode (n : ℕ) :
      Tendsto
        (fun s : ℝ => (a n) •
          (s⁻¹ • (T s (v n) - v n)))
        (𝓝[>] (0 : ℝ))
        (𝓝 ((a n) • ((-((n : ℝ) * ((n : ℝ) + 2 * lam))) • v n))) :=
    (sturmRealHeatLimit_mode_right_slope lam hlam n).const_smul (a n)
  have hfinite :
      Tendsto
        (fun s : ℝ => ∑ n ∈ F, (a n) • (s⁻¹ • (T s (v n) - v n)))
        (𝓝[>] (0 : ℝ))
        (𝓝 (∑ n ∈ F,
          (a n) • ((-((n : ℝ) * ((n : ℝ) + 2 * lam))) • v n))) := by
    induction F using Finset.induction_on with
    | empty => simp
    | @insert n F hn ih =>
        simp only [Finset.sum_insert hn]
        exact (hmode n).add ih
  have hrewrite (s : ℝ) :
      T s (∑ n ∈ F, (a n) • v n) -
        (∑ n ∈ F, (a n) • v n) =
          ∑ n ∈ F, (a n) • (T s (v n) - v n) := by
    rw [map_sum]
    simp only [map_smul, smul_sub, Finset.sum_sub_distrib]
  have hfun :
      (fun s : ℝ =>
        s⁻¹ • (T s (sturmRealGegenbauerFiniteVector lam hlam F a) -
          sturmRealGegenbauerFiniteVector lam hlam F a)) =
      (fun s : ℝ => ∑ n ∈ F, (a n) • (s⁻¹ • (T s (v n) - v n))) := by
    funext s
    dsimp [sturmRealGegenbauerFiniteVector, v]
    rw [hrewrite s, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [smul_comm]
  rw [hfun]
  exact hfinite

#print axioms GegenbauerFock.Ultraspherical.sturmRealHeatLimit_finiteGegenbauer_right_slope

end GegenbauerFock.Ultraspherical
