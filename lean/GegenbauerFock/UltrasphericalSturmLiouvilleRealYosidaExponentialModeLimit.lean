import GegenbauerFock.UltrasphericalSturmLiouvilleRealYosidaExponentialGegenbauerModes
import GegenbauerFock.UltrasphericalSturmLiouvilleRealYosidaSpectralScalarLimit
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# V007 — strong Yosida semigroup convergence on every Gegenbauer eigenmode

This is a single-eigenmode strong limit as the positive Yosida parameter
approaches infinity along the integer shifts t = N + 1. It combines
certified scalar multiplier convergence with certified exact exponential
eigenvector action in the actual weighted real L² Hilbert space.
It does not assert strong convergence for arbitrary L² inputs.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory Filter
open scoped Topology

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- For every fixed Gegenbauer mode and every fixed real time, the
bounded Yosida exponential orbit converges to the spectral heat
multiplier along positive integer shifts. -/
theorem sturmRealYosidaExponential_Gegenbauer_mode_tendsto
    (lam : ℝ) (hlam : 0 < lam) (n : ℕ) (s : ℝ) :
    Tendsto
      (fun k : ℕ =>
        sturmRealYosidaExponential lam ((k : ℝ) + 1) hlam
          (by positivity : 0 < (k : ℝ) + 1) s
          (sturmMonicEigenCandidate_realL2_normalized lam hlam n))
      atTop
      (𝓝 ((Real.exp (-s * ((n : ℝ) * ((n : ℝ) + 2 * lam)))) •
        sturmMonicEigenCandidate_realL2_normalized lam hlam n)) := by
  let omega : ℝ := (n : ℝ) * ((n : ℝ) + 2 * lam)
  let u : SturmH lam :=
    sturmMonicEigenCandidate_realL2_normalized lam hlam n
  have htop : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop := by
    exact tendsto_atTop_add_const_right atTop 1
      tendsto_natCast_atTop_atTop
  have hscalar :
      Tendsto (fun k : ℕ =>
        Real.exp ((-s * omega) *
          (((k : ℝ) + 1) / (((k : ℝ) + 1) + omega))))
        atTop (𝓝 (Real.exp (-s * omega))) := by
    exact (sturmRealYosida_eigenmode_exponential_tendsto
      lam hlam n s).comp htop
  have hpoint (k : ℕ) :
      sturmRealYosidaExponential lam ((k : ℝ) + 1) hlam
          (by positivity : 0 < (k : ℝ) + 1) s u =
        (Real.exp ((-s * omega) *
          (((k : ℝ) + 1) / (((k : ℝ) + 1) + omega)))) • u := by
    rw [sturmRealYosidaExponential_normalized_Gegenbauer_eigen]
    congr 1
    dsimp [omega]
    ring
  change Tendsto
    (fun k : ℕ =>
      sturmRealYosidaExponential lam ((k : ℝ) + 1) hlam
        (by positivity : 0 < (k : ℝ) + 1) s u)
    atTop (𝓝 ((Real.exp (-s * omega)) • u))
  have hfun :
      (fun k : ℕ =>
        sturmRealYosidaExponential lam ((k : ℝ) + 1) hlam
          (by positivity : 0 < (k : ℝ) + 1) s u) =
      (fun k : ℕ =>
        (Real.exp ((-s * omega) *
          (((k : ℝ) + 1) / (((k : ℝ) + 1) + omega)))) • u) :=
    funext hpoint
  rw [hfun]
  exact hscalar.smul_const u

#print axioms GegenbauerFock.Ultraspherical.sturmRealYosidaExponential_Gegenbauer_mode_tendsto

end GegenbauerFock.Ultraspherical
