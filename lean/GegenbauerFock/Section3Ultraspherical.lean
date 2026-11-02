import GegenbauerFock.Manuscript13Fourier
import GegenbauerFock.UltrasphericalGammaDensity
import GegenbauerFock.GegenbauerIntrinsicEntireBochnerEvaluation
import GegenbauerFock.EulerianStateShi

/-!
# Manuscript 13, Section 3 on the branch's ultraspherical measure

`Manuscript13.ν λ` is the measure with density `c_λ (1-u²)^{λ-1/2}` on `(-1,1)`,
`c_λ = Γ(λ+1)/(√π Γ(λ+1/2))`, for every `λ > -1/2`. For `λ > 0` it coincides with the branch's
Beta-pushforward `Ultraspherical.measure λ` (`measure_eq_nu`). Hence:

* **Proposition 3.3**: `Φ_λ(z) = ∫ e^{izu} dν_λ` is entire (`Phi_differentiable`, through the
  certified pointwise Bochner formula of `C_{λ,α} 𝟏`), has the series
  `∑ (-1)ⁿ (z²/4)ⁿ / (n! (λ+1)_n)` (`Phi_series`), `Φ_λ(0) = 1`, and for `t > 0` the Bessel form
  `Φ_λ(t) = Γ(λ+1)(2/t)^λ J_λ(t)`, `J_λ` given by its classical power series (`Phi_bessel'`).
* **Proposition 3.4**: `dν_{1/2} = ½ 1_{(-1,1)} du` and `r_E(z) = Φ_{1/2}(z/2)` (`proposition_3_4`).
* **Proposition 3.6**: the `λ = 1` density `(2/π)√(1-u²)` with moments `C_n/4ⁿ`, the arcsine
  density at `λ = 0` with moments `binom(2n,n)/4ⁿ`, and the limit `λ ↓ 0` of densities and
  even moments (`proposition_3_6`).
-/

noncomputable section

open MeasureTheory Complex Set Filter Topology
open GegenbauerFock.GeneralUltrasphericalFock

namespace GegenbauerFock.Section3

open GegenbauerFock.Manuscript13 (ν Φ dens cl)

/-- For `λ > 0`, the branch's measure is the Gamma-normalized density measure. -/
theorem measure_eq_nu (lam : ℝ) (hlam : 0 < lam) : Ultraspherical.measure lam = ν lam := by
  rw [Ultraspherical.measure_eq_withDensity_gamma lam hlam]
  unfold ν
  congr 1
  all_goals
    funext u
    unfold Ultraspherical.gammaDensity dens cl Ultraspherical.shape
    simp only [Set.mem_Ioo]

/-- `Φ_λ` written with the branch's measure. -/
theorem Phi_eq_integral (lam : ℝ) (hlam : 0 < lam) (z : ℂ) :
    Φ lam z = ∫ u, cexp (I * z * u) ∂(Ultraspherical.measure lam) := by
  rw [measure_eq_nu lam hlam]; rfl

/-- **Proposition 3.3**: `Φ_λ` is entire. -/
theorem Phi_differentiable (lam : ℝ) (hlam : 0 < lam) : Differentiable ℂ (Φ lam) := by
  letI : IsProbabilityMeasure (Ultraspherical.measure lam) := Ultraspherical.probability lam hlam
  let f : Lp ℂ 2 (Ultraspherical.measure lam) := Lp.const 2 _ (1 : ℂ)
  have hc : (f : ℝ → ℂ) =ᵐ[Ultraspherical.measure lam] fun _ => (1 : ℂ) := Lp.coeFn_const 2 _ 1
  have hrep : ∀ z : ℂ, Φ lam z = GaussianArea.entireRepresentative 1
      (C_intrinsicEntire lam 1 hlam one_pos f) (2 * z) := by
    intro z
    rw [C_intrinsicEntire_pointwiseBochner, Phi_eq_integral lam hlam]
    refine integral_congr_ae (hc.mono fun u hu => ?_)
    show cexp (I * z * u) = (f : ℝ → ℂ) u * cexp (I * (2 * z) * (u : ℂ) / 2)
    rw [hu, one_mul]; ring_nf
  have hd := GaussianArea.entireRepresentative_differentiable 1
    (C_intrinsicEntire lam 1 hlam one_pos f)
  have : Φ lam = fun z => GaussianArea.entireRepresentative 1
      (C_intrinsicEntire lam 1 hlam one_pos f) (2 * z) := funext hrep
  rw [this]
  exact hd.comp (differentiable_const _ |>.mul differentiable_id)

/-- **Proposition 3.3**, power series (eq:phi-series). -/
theorem Phi_series (lam : ℝ) (hlam : 0 < lam) (z : ℂ) :
    HasSum (fun n : ℕ => ((-1 : ℂ) ^ n /
        ((n.factorial : ℂ) * ((ascPochhammer ℝ n).eval (lam + 1) : ℝ))) * (z ^ 2 / 4) ^ n)
      (∫ u, cexp (I * z * u) ∂(Ultraspherical.measure lam)) := by
  rw [← Phi_eq_integral lam hlam]
  exact Manuscript13.Phi_hasSum (by linarith) z

/-- **Proposition 3.3**, (eq:bessel-bridge). -/
theorem Phi_bessel' (lam : ℝ) (hlam : 0 < lam) {t : ℝ} (ht : 0 < t) :
    ∫ u, cexp (I * (t : ℂ) * u) ∂(Ultraspherical.measure lam) =
      ((Real.Gamma (lam + 1) * (2 / t) ^ lam * Manuscript13.besselJ lam t : ℝ) : ℂ) := by
  rw [← Phi_eq_integral lam hlam]
  exact Manuscript13.Phi_bessel (by linarith) ht

/-- The two forms of the Eulerian profile agree: `2 sin(z/2)/z = ∫_{-1/2}^{1/2} e^{izt} dt`. -/
theorem rE_eq (z : ℂ) : EulerianState.rE z = Manuscript13.rE z := by
  rw [Manuscript13.rE_eq_Phi, Phi_eq_integral (1 / 2) (by norm_num),
    ← EulerianState.C_one_eq_rE 1 one_pos z, C_intrinsicEntire_pointwiseBochner]
  have hc : ((EulerianState.one : Lp ℂ 2 (Ultraspherical.measure (1 / 2))) : ℝ → ℂ) =ᵐ[_]
      fun _ => (1 : ℂ) := Lp.coeFn_const 2 _ (1 : ℂ)
  refine integral_congr_ae (hc.mono fun u hu => ?_)
  show (EulerianState.one : ℝ → ℂ) u * cexp (I * z * (u : ℂ) / 2) = cexp (I * (z / 2) * u)
  rw [hu, one_mul]; ring_nf

/-- **Proposition 3.4**. -/
theorem proposition_3_4 :
    (∀ u, Ultraspherical.gammaDensity (1 / 2) u =
        Set.indicator (Set.Ioo (-1 : ℝ) 1) (fun _ => (1 / 2 : ℝ)) u) ∧
      ∀ z : ℂ, EulerianState.rE z =
        ∫ u, cexp (I * (z / 2) * u) ∂(Ultraspherical.measure (1 / 2)) := by
  refine ⟨EulerianState.gammaDensity_half, fun z => ?_⟩
  rw [rE_eq, Manuscript13.rE_eq_Phi, Phi_eq_integral (1 / 2) (by norm_num)]

/-- **Proposition 3.6**. -/
theorem proposition_3_6 :
    (∀ u, dens 1 u = if u ∈ Ioo (-1 : ℝ) 1 then 2 / Real.pi * Real.sqrt (1 - u ^ 2) else 0) ∧
      (∀ n : ℕ, ∫ u, ((u ^ (2 * n) : ℝ) : ℂ) ∂(Ultraspherical.measure 1) =
        (((Nat.choose (2 * n) n : ℝ) / (n + 1)) / 4 ^ n : ℝ)) ∧
      (∀ u, dens 0 u = if u ∈ Ioo (-1 : ℝ) 1 then 1 / (Real.pi * Real.sqrt (1 - u ^ 2)) else 0) ∧
      (∀ n : ℕ, ∫ u, ((u ^ (2 * n) : ℝ) : ℂ) ∂(ν 0) = (((Nat.choose (2 * n) n : ℝ)) / 4 ^ n : ℝ)) ∧
      (∀ u ∈ Ioo (-1 : ℝ) 1, Tendsto (fun l : ℝ => dens l u) (𝓝 0) (𝓝 (dens 0 u))) ∧
      (∀ n : ℕ, Tendsto (fun l : ℝ => (ascPochhammer ℝ n).eval (1 / 2) /
        (ascPochhammer ℝ n).eval (l + 1)) (𝓝 0)
          (𝓝 ((ascPochhammer ℝ n).eval (1 / 2) / (ascPochhammer ℝ n).eval (0 + 1)))) := by
  refine ⟨Manuscript13.dens_one, fun n => ?_, Manuscript13.dens_zero, Manuscript13.moment_zero,
    fun u hu => Manuscript13.dens_tendsto hu, Manuscript13.moment_tendsto⟩
  rw [measure_eq_nu 1 one_pos]
  exact Manuscript13.moment_one n

#print axioms GegenbauerFock.Section3.measure_eq_nu
#print axioms GegenbauerFock.Section3.Phi_differentiable
#print axioms GegenbauerFock.Section3.Phi_series
#print axioms GegenbauerFock.Section3.Phi_bessel'
#print axioms GegenbauerFock.Section3.proposition_3_4
#print axioms GegenbauerFock.Section3.proposition_3_6

end GegenbauerFock.Section3
