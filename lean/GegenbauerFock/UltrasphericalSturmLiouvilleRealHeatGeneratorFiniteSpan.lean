import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatGeneratorModes
import GegenbauerFock.UltrasphericalSturmLiouvilleRealYosidaFiniteSpanLimit

/-!
# V007 — heat infinitesimal generator on finite Gegenbauer spectral sums

For the full-L² contractive C₀ heat semigroup, the right time-zero
derivative is computed on every finite span of the explicitly
normalized Gegenbauer Hilbert basis:

  lim_{h→0+} h⁻¹ • (H_h f - f)
    = ∑_{n∈F} a_n • (-n(n+2λ)) • u_n,

where f = ∑_{n∈F} a_n • u_n.
This identifies the generator on a dense invariant polynomial core,
without assuming the full generator's domain equals the closed Sturm
operator's domain; that equality is a separate obligation.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory Filter
open scoped Topology

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- Exact finite spectral derivative of the genuine limiting heat semigroup. -/
noncomputable def sturmRealGegenbauerFiniteGeneratorVector
    (lam : ℝ) (hlam : 0 < lam) (F : Finset ℕ)
    (a : ℕ → ℝ) : SturmH lam :=
  ∑ n ∈ F,
    (a n) • ((-((n : ℝ) * ((n : ℝ) + 2 * lam))) •
      sturmMonicEigenCandidate_realL2_normalized lam hlam n)

/-- The full-L² semigroup's infinitesimal generator acts on every
finite linear combination of actual normalized Gegenbauer modes. -/
theorem sturmRealHeatLimit_generator_on_finite_Gegenbauer
    (lam : ℝ) (hlam : 0 < lam) (F : Finset ℕ) (a : ℕ → ℝ) :
    Tendsto
      (fun h : ℝ => h⁻¹ •
        (sturmRealHeatLimitNonnegativeExtended lam hlam h
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
        (fun h : ℝ => (a n) •
          (h⁻¹ • (T h (v n) - v n)))
        (𝓝[>] (0 : ℝ))
        (𝓝 ((a n) • ((-((n : ℝ) * ((n : ℝ) + 2 * lam))) • v n))) :=
    (sturmRealHeatLimit_generator_on_normalized_Gegenbauer
      lam hlam n).const_smul (a n)
  have hfinite :
      Tendsto
        (fun h : ℝ =>
          ∑ n ∈ F, (a n) • (h⁻¹ • (T h (v n) - v n)))
        (𝓝[>] (0 : ℝ))
        (𝓝 (∑ n ∈ F,
          (a n) • ((-((n : ℝ) * ((n : ℝ) + 2 * lam))) • v n))) := by
    induction F using Finset.induction_on with
    | empty => simp
    | @insert n F hn ih =>
        simp only [Finset.sum_insert hn]
        exact (hmode n).add ih
  have hfun :
      (fun h : ℝ => h⁻¹ •
        (T h (sturmRealGegenbauerFiniteVector lam hlam F a) -
          sturmRealGegenbauerFiniteVector lam hlam F a)) =
      (fun h : ℝ =>
        ∑ n ∈ F, (a n) • (h⁻¹ • (T h (v n) - v n))) := by
    funext h
    change h⁻¹ •
      (T h (∑ n ∈ F, (a n) • v n) -
        ∑ n ∈ F, (a n) • v n) = _
    rw [map_sum]
    simp only [map_smul, ← Finset.sum_sub_distrib, ← smul_sum, smul_sub]
    apply Finset.sum_congr rfl
    intro n hn
    exact smul_comm (h⁻¹) (a n) (T h (v n) - v n)
  rw [hfun]
  exact hfinite

#print axioms GegenbauerFock.Ultraspherical.sturmRealHeatLimit_generator_on_finite_Gegenbauer

end GegenbauerFock.Ultraspherical
