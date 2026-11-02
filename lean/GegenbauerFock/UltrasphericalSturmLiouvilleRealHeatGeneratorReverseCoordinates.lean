import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatLimitHilbertCoordinates
import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatScalarSlope
import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatLimitModeContinuity
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# V007 — necessary spectral-coordinate condition for the heat generator domain

Suppose the right time-zero difference quotient of the *actual* strongly
continuous weighted-real-L² heat semigroup converges in L² to g. Then each
Gegenbauer Fourier coordinate of g equals the closed Sturm spectral
multiplier of the corresponding coordinate of f.

Unlike a statement only about polynomial eigenmodes, this theorem is
quantified over arbitrary f and g in the full weighted L² and makes
no a priori closed-operator-domain assumption. Together with Parseval
and the certified exact closed Sturm spectral domain, it provides the
reverse domain inclusion required to identify the generator.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory Filter
open scoped Topology

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- Any actual strong right derivative of the heat orbit has exactly
the canonical Gegenbauer Sturm Fourier coordinates at every degree. -/
theorem sturmRealHeatLimit_right_derivative_repr
    (lam : ℝ) (hlam : 0 < lam) (f g : SturmH lam)
    (hderiv : Tendsto
      (fun s : ℝ =>
        s⁻¹ • (sturmRealHeatLimitNonnegativeExtended lam hlam s f - f))
      (𝓝[>] (0 : ℝ)) (𝓝 g))
    (n : ℕ) :
    (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr g n =
      (-((n : ℝ) * ((n : ℝ) + 2 * lam))) *
        (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr f n := by
  let b := sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam
  let omega : ℝ := (n : ℝ) * ((n : ℝ) + 2 * lam)
  let c : ℝ := (b.repr f) n
  have hlimit :
      Tendsto
        (fun s : ℝ =>
          (b.repr (s⁻¹ •
            (sturmRealHeatLimitNonnegativeExtended lam hlam s f - f))) n)
        (𝓝[>] (0 : ℝ)) (𝓝 ((b.repr g) n)) := by
    have h := ((innerSL ℝ (b n)).continuous.tendsto g).comp hderiv
    have h' :
        Tendsto
          (fun t : ℝ => inner ℝ (b n)
            (t⁻¹ •
              (sturmRealHeatLimitNonnegativeExtended lam hlam t f - f)))
          (𝓝[>] (0 : ℝ)) (𝓝 (inner ℝ (b n) g)) := by
      simpa only [Function.comp_def, innerSL_apply_apply] using h
    simpa only [← HilbertBasis.repr_apply_apply] using h'
  have hspectral (s : ℝ) (hs : 0 < s) :
      (b.repr (sturmRealHeatLimitNonnegativeExtended lam hlam s f)) n =
        Real.exp (-s * omega) * c := by
    have h := sturmRealHeatLimitCLM_hilbert_repr_diagonal lam hlam
      (max (0 : ℝ) s) (le_max_left (0 : ℝ) s) f n
    change (b.repr (sturmRealHeatLimitCLM lam hlam
      (max (0 : ℝ) s) (le_max_left (0 : ℝ) s) f)) n =
        Real.exp (-s * omega) * c
    simpa only [max_eq_right hs.le] using h
  have hpoint (s : ℝ) (hs : 0 < s) :
      (b.repr (s⁻¹ •
        (sturmRealHeatLimitNonnegativeExtended lam hlam s f - f))) n =
        (s⁻¹ • (Real.exp (s * (-omega)) - 1)) * c := by
    calc
      (b.repr (s⁻¹ •
        (sturmRealHeatLimitNonnegativeExtended lam hlam s f - f))) n =
          inner ℝ (b n) (s⁻¹ •
            (sturmRealHeatLimitNonnegativeExtended lam hlam s f - f)) :=
        HilbertBasis.repr_apply_apply b _ n
      _ = s⁻¹ * (inner ℝ (b n)
          (sturmRealHeatLimitNonnegativeExtended lam hlam s f) -
          inner ℝ (b n) f) := by
        rw [inner_smul_right, inner_sub_right]
        rfl
      _ = s⁻¹ * (Real.exp (-s * omega) * c - c) := by
        rw [← HilbertBasis.repr_apply_apply b
          (sturmRealHeatLimitNonnegativeExtended lam hlam s f) n,
          ← HilbertBasis.repr_apply_apply b f n, hspectral s hs]
      _ = (s⁻¹ • (Real.exp (s * (-omega)) - 1)) * c := by
        have he : Real.exp (-s * omega) =
            Real.exp (s * (-omega)) := by
          congr 1
          ring
        rw [he]
        simp only [smul_eq_mul]
        ring
  have hevent :
      (fun s : ℝ =>
        (b.repr (s⁻¹ •
          (sturmRealHeatLimitNonnegativeExtended lam hlam s f - f))) n)
      =ᶠ[𝓝[>] (0 : ℝ)]
      (fun s : ℝ => (s⁻¹ • (Real.exp (s * (-omega)) - 1)) * c) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact hpoint s hs
  have hscalar :
      Tendsto (fun s : ℝ =>
        (s⁻¹ • (Real.exp (s * (-omega)) - 1)) * c)
        (𝓝[>] (0 : ℝ)) (𝓝 ((-omega) * c)) :=
    (sturmRealHeat_scalar_slope_zero_right omega).mul_const c
  have hother := hlimit.congr' hevent
  have heq := tendsto_nhds_unique hother hscalar
  change (b.repr g) n = -omega * c
  exact heq

#print axioms GegenbauerFock.Ultraspherical.sturmRealHeatLimit_right_derivative_repr

end GegenbauerFock.Ultraspherical
