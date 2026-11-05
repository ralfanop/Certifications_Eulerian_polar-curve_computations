import GegenbauerFock.UltrasphericalSturmLiouvilleActualComplexHeatSemigroupLaw
import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatLimitFullC0

/-!
# V007 — strong right C0 continuity of actual COMPLEX Gegenbauer heat

The concrete bounded complex-linear operator H^C_s on the GENUINE
complex-valued Gegenbauer weighted L² is the complex extension of
the kernel-certified actual real Sturm heat semigroup.

The preceding module proves exact H^C_0=1 and
H^C_(s+t)=H^C_s H^C_t for nonnegative times.

Here the already certified strong right continuity of H^R_s on
every REAL weighted-L² vector is transported to both actual
real/imaginary projections of a complex weighted-L² vector. By the
bounded real inclusion J and the exact decomposition
f=J(Re f)+I J(Im f), this yields strong C₀ continuity at zero on
EVERY complex weighted-L² vector, not merely on the real subspace
or on a dense family of polynomials.

Nothing is assumed about the distinct Gegenbauer--Fock Gram.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory Filter
open scoped Topology

private abbrev HR (lam : ℝ) := Lp ℝ 2 (measure lam)
private abbrev HC (lam : ℝ) := Lp ℂ 2 (measure lam)

/-- Total real-time extension of the actual complex weighted-L²
heat operator; at negative times it is held at the identity value
s=0, while for s>=0 it agrees with the original complex H_s. -/
noncomputable def sturmActualComplexHeatNonnegativeExtended
    (lam : ℝ) (hlam : 0 < lam) (s : ℝ) :
    HC lam →L[ℂ] HC lam :=
  sturmActualComplexHeatCLM lam hlam (max (0 : ℝ) s)
    (le_max_left (0 : ℝ) s)

/-- Every complex vector has a strongly continuous right heat orbit
at zero for the genuine COMPLEX-linear semigroup. The proof is on
the full actual L²(nu_lambda;C), not an auxiliary ℓ² model. -/
theorem sturmActualComplexHeatNonnegativeExtended_allL2_tendsto_zero
    (lam : ℝ) (hlam : 0 < lam) (f : HC lam) :
    Tendsto
      (fun s : ℝ => sturmActualComplexHeatNonnegativeExtended lam hlam s f)
      (𝓝[≥] (0 : ℝ)) (𝓝 f) := by
  have hRe :
      Tendsto
        (fun s : ℝ =>
          realToComplexLp lam
            (sturmRealHeatLimitNonnegativeExtended lam hlam s
              (complexLpRe lam f)))
        (𝓝[≥] (0 : ℝ))
        (𝓝 (realToComplexLp lam (complexLpRe lam f))) :=
    ((realToComplexLp lam).continuous.tendsto
      (complexLpRe lam f)).comp
        (sturmRealHeatLimitNonnegativeExtended_allL2_tendsto_zero
          lam hlam (complexLpRe lam f))
  have hIm :
      Tendsto
        (fun s : ℝ =>
          realToComplexLp lam
            (sturmRealHeatLimitNonnegativeExtended lam hlam s
              (complexLpIm lam f)))
        (𝓝[≥] (0 : ℝ))
        (𝓝 (realToComplexLp lam (complexLpIm lam f))) :=
    ((realToComplexLp lam).continuous.tendsto
      (complexLpIm lam f)).comp
        (sturmRealHeatLimitNonnegativeExtended_allL2_tendsto_zero
          lam hlam (complexLpIm lam f))
  have hSum := hRe.add (hIm.const_smul Complex.I)
  have hFormula (s : ℝ) :
      sturmActualComplexHeatNonnegativeExtended lam hlam s f =
        realToComplexLp lam
          (sturmRealHeatLimitNonnegativeExtended lam hlam s
            (complexLpRe lam f)) +
        Complex.I • realToComplexLp lam
          (sturmRealHeatLimitNonnegativeExtended lam hlam s
            (complexLpIm lam f)) := by
    simpa only [sturmActualComplexHeatNonnegativeExtended,
      sturmRealHeatLimitNonnegativeExtended] using
      (sturmActualComplexHeatCLM_apply_re_im lam hlam
        (max (0 : ℝ) s) (le_max_left (0 : ℝ) s) f)
  have hGoal :
      Tendsto
        (fun s : ℝ =>
          realToComplexLp lam
            (sturmRealHeatLimitNonnegativeExtended lam hlam s
              (complexLpRe lam f)) +
          Complex.I • realToComplexLp lam
            (sturmRealHeatLimitNonnegativeExtended lam hlam s
              (complexLpIm lam f)))
        (𝓝[≥] (0 : ℝ)) (𝓝 f) := by
    simpa only [complexLp_eq_realToComplex_re_add_I_im lam f] using hSum
  convert hGoal using 1
  funext s
  exact hFormula s

/-- The true complex Sturm heat forms a strongly continuous
complex-linear semigroup on full weighted-L²: exact identity,
additive semigroup law, and right C₀ continuity at zero.
This is a conjunction of three independently constructed proofs. -/
theorem sturmActualComplexHeat_fullC0_joint_certificate
    (lam : ℝ) (hlam : 0 < lam) :
    sturmActualComplexHeatCLM lam hlam 0 le_rfl =
        (1 : HC lam →L[ℂ] HC lam) ∧
    (∀ s t : ℝ, ∀ hs : 0 ≤ s, ∀ ht : 0 ≤ t,
      sturmActualComplexHeatCLM lam hlam (s + t) (add_nonneg hs ht) =
        sturmActualComplexHeatCLM lam hlam s hs *
          sturmActualComplexHeatCLM lam hlam t ht) ∧
    (∀ f : HC lam,
      Tendsto
        (fun s : ℝ =>
          sturmActualComplexHeatNonnegativeExtended lam hlam s f)
        (𝓝[≥] (0 : ℝ)) (𝓝 f)) := by
  exact ⟨sturmActualComplexHeatCLM_zero lam hlam,
    fun s t hs ht => sturmActualComplexHeatCLM_add lam hlam s t hs ht,
    fun f => sturmActualComplexHeatNonnegativeExtended_allL2_tendsto_zero
      lam hlam f⟩

#print axioms GegenbauerFock.Ultraspherical.sturmActualComplexHeatNonnegativeExtended_allL2_tendsto_zero
#print axioms GegenbauerFock.Ultraspherical.sturmActualComplexHeat_fullC0_joint_certificate

end GegenbauerFock.Ultraspherical
