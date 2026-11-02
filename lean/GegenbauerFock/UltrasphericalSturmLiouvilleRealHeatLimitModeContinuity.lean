import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatLimitEigenmodes
import Mathlib.Topology.Algebra.Order.Field

/-!
# V007 — time-zero strong continuity of actual heat-limit Gegenbauer eigenmodes

The operator H_s is constructed on every real weighted L² vector by
the strongly convergent, uniformly contractive Yosida exponentials.
For every normalized Gegenbauer eigenmode v_n the exact eigenvalue
is exp(-s*n*(n+2*lambda)).

To define a family on all real times without choosing positivity
witnesses pointwise, we extend by H_(max(0,s)). The family is contractive
for every real argument and agrees with H_s when s>=0.

The exact mode formula proves strong continuity of every eigenmode
at time zero, hence prepares a density argument for all L².
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory Filter
open scoped Topology

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- A total real-time extension of the genuine nonnegative-time
heat-limit operators; the extension is constant for s ≤ 0. -/
noncomputable def sturmRealHeatLimitNonnegativeExtended
    (lam : ℝ) (hlam : 0 < lam) (s : ℝ) :
    SturmH lam →L[ℝ] SturmH lam :=
  sturmRealHeatLimitCLM lam hlam (max (0 : ℝ) s)
    (le_max_left (0 : ℝ) s)

/-- Contractivity of the total nonnegative-time heat extension. -/
theorem sturmRealHeatLimitNonnegativeExtended_opNorm_le
    (lam : ℝ) (hlam : 0 < lam) (s : ℝ) :
    ‖sturmRealHeatLimitNonnegativeExtended lam hlam s‖ ≤ 1 := by
  exact sturmRealHeatLimitCLM_opNorm_le lam hlam
    (max (0 : ℝ) s) (le_max_left (0 : ℝ) s)

/-- Exact action of the nonnegative-time heat extension on
every normalized Gegenbauer eigenmode. -/
theorem sturmRealHeatLimitNonnegativeExtended_mode
    (lam : ℝ) (hlam : 0 < lam) (s : ℝ) (n : ℕ) :
    sturmRealHeatLimitNonnegativeExtended lam hlam s
      (sturmMonicEigenCandidate_realL2_normalized lam hlam n) =
      Real.exp (-(max (0 : ℝ) s) *
        ((n : ℝ) * ((n : ℝ) + 2 * lam))) •
        sturmMonicEigenCandidate_realL2_normalized lam hlam n :=
  sturmRealHeatLimitCLM_normalized_Gegenbauer_eigen lam hlam
    (max (0 : ℝ) s) (le_max_left (0 : ℝ) s) n

/-- Real-time strong continuity at zero for EACH actual L²
normalized Gegenbauer eigenmode of the limiting heat operator. -/
theorem sturmRealHeatLimitNonnegativeExtended_mode_tendsto_zero
    (lam : ℝ) (hlam : 0 < lam) (n : ℕ) :
    Tendsto
      (fun s : ℝ =>
        sturmRealHeatLimitNonnegativeExtended lam hlam s
          (sturmMonicEigenCandidate_realL2_normalized lam hlam n))
      (𝓝[≥] (0 : ℝ))
      (𝓝 (sturmMonicEigenCandidate_realL2_normalized lam hlam n)) := by
  let omega : ℝ := (n : ℝ) * ((n : ℝ) + 2 * lam)
  let v : SturmH lam :=
    sturmMonicEigenCandidate_realL2_normalized lam hlam n
  have harg : Continuous
      (fun s : ℝ => -(max (0 : ℝ) s) * omega) := by
    fun_prop
  have hscalar :
      Tendsto
        (fun s : ℝ => Real.exp (-(max (0 : ℝ) s) * omega))
        (𝓝[≥] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
    have h := (Real.continuous_exp.comp harg).tendsto (0 : ℝ)
    have hh := h.mono_left (nhdsWithin_le_nhds (s := Set.Ici (0 : ℝ)))
    simpa only [max_self, neg_zero, zero_mul, Real.exp_zero] using hh
  have hvec : Tendsto
      (fun s : ℝ => Real.exp (-(max (0 : ℝ) s) * omega) • v)
      (𝓝[≥] (0 : ℝ)) (𝓝 v) := by
    simpa only [one_smul] using hscalar.smul_const v
  have heq :
      (fun s : ℝ => sturmRealHeatLimitNonnegativeExtended lam hlam s v) =
      (fun s : ℝ => Real.exp (-(max (0 : ℝ) s) * omega) • v) := by
    funext s
    exact sturmRealHeatLimitNonnegativeExtended_mode lam hlam s n
  rw [heq]
  exact hvec

#print axioms GegenbauerFock.Ultraspherical.sturmRealHeatLimitNonnegativeExtended_opNorm_le
#print axioms GegenbauerFock.Ultraspherical.sturmRealHeatLimitNonnegativeExtended_mode
#print axioms GegenbauerFock.Ultraspherical.sturmRealHeatLimitNonnegativeExtended_mode_tendsto_zero

end GegenbauerFock.Ultraspherical
