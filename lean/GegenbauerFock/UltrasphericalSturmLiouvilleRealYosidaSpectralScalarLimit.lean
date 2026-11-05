import GegenbauerFock.UltrasphericalSturmLiouvilleMonicRealL2Unitary
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Algebra.Order.Field

/-!
# V007 — spectral Yosida scalar limit for every Gegenbauer degree

For every eigenmode n and lambda>0, the actual Sturm eigenvalue is
 -omega_n, omega_n=n(n+2 lambda)>=0. Its Yosida generator eigenvalue
 at shift t>0 is -t omega_n/(t+omega_n).

This module certifies scalar convergence of the corresponding
exponential multipliers as t→+∞. It does NOT claim the full operator
semigroup converges strongly: that requires the genuine eigenmode
action and density-extension argument.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open Filter
open scoped Topology

/-- Every positive-shift scalar Yosida ratio tends to one. -/
theorem sturmRealYosida_scalar_ratio_tendsto_one
    (omega : ℝ) (homega : 0 ≤ omega) :
    Tendsto (fun t : ℝ => t / (t + omega)) atTop (𝓝 1) := by
  have htop : Tendsto (fun t : ℝ => t + omega) atTop atTop :=
    tendsto_atTop_add_const_right atTop omega tendsto_id
  have hsmall : Tendsto (fun t : ℝ => omega / (t + omega)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop htop
  have hsub : Tendsto (fun t : ℝ => 1 - omega / (t + omega))
      atTop (𝓝 1) := by
    simpa only [sub_zero] using (tendsto_const_nhds.sub hsmall :
      Tendsto (fun t : ℝ => (1 : ℝ) - omega / (t + omega))
        atTop (𝓝 (1 - 0)))
  have heq : (fun t : ℝ => 1 - omega / (t + omega)) =ᶠ[atTop]
      (fun t : ℝ => t / (t + omega)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have hd : t + omega ≠ 0 :=
      ne_of_gt (add_pos_of_pos_of_nonneg ht homega)
    field_simp
    ring
  exact hsub.congr' heq

/-- For every genuine Gegenbauer spectral degree, the scalar
Yosida semigroup multiplier tends to exp(-s*n(n+2lambda)). -/
theorem sturmRealYosida_eigenmode_exponential_tendsto
    (lam : ℝ) (hlam : 0 < lam) (n : ℕ) (s : ℝ) :
    Tendsto (fun t : ℝ =>
      Real.exp ((-s * ((n : ℝ) * ((n : ℝ) + 2 * lam))) *
        (t / (t + ((n : ℝ) * ((n : ℝ) + 2 * lam))))))
      atTop
      (𝓝 (Real.exp (-s * ((n : ℝ) * ((n : ℝ) + 2 * lam))))) := by
  let omega : ℝ := (n : ℝ) * ((n : ℝ) + 2 * lam)
  have homega : 0 ≤ omega := by
    dsimp [omega]
    positivity
  have hratio : Tendsto (fun t : ℝ => t / (t + omega)) atTop (𝓝 1) :=
    sturmRealYosida_scalar_ratio_tendsto_one omega homega
  have hmul :
      Tendsto (fun t : ℝ => (-s * omega) * (t / (t + omega)))
        atTop (𝓝 (-s * omega)) := by
    simpa only [mul_one] using
      (tendsto_const_nhds.mul hratio :
        Tendsto (fun t : ℝ => (-s * omega) * (t / (t + omega)))
          atTop (𝓝 ((-s * omega) * 1)))
  change Tendsto (fun t : ℝ => Real.exp ((-s * omega) * (t / (t + omega))))
    atTop (𝓝 (Real.exp (-s * omega)))
  exact Real.continuous_exp.continuousAt.tendsto.comp hmul

#print axioms GegenbauerFock.Ultraspherical.sturmRealYosida_scalar_ratio_tendsto_one
#print axioms GegenbauerFock.Ultraspherical.sturmRealYosida_eigenmode_exponential_tendsto

end GegenbauerFock.Ultraspherical
