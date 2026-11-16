import Manuscript15.Section27PrimalWasserstein

/-! M15 §8.4. Exact cell geometry, normalising sums, and scalar identities.
The spectral estimates and construction of the Gibbs pushforward are separate
obligations. No asserted spectral theorem is used as a hidden axiom. -/
open MeasureTheory
open scoped BigOperators
noncomputable section
namespace Manuscript15.MagneticGibbs
open Manuscript15.Section27.Primal

def oddLevel (k : ℤ) : ℝ := 2 * (k : ℝ) + 1

/-- The centre is nearest among the whole odd integer lattice, not merely
among finitely many sample points. -/
theorem odd_cell_nearest (E : ℝ) (k j : ℤ)
    (hlo : 2*(k:ℝ) ≤ E) (hhi : E ≤ 2*(k:ℝ)+2) :
    |E-oddLevel k| ≤ |E-oddLevel j| := by
  unfold oddLevel
  have hc : |E-(2*(k:ℝ)+1)| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  rcases lt_trichotomy j k with hj | hj | hj
  · have hn : j+1 ≤ k := by omega
    have hr : (j:ℝ)+1 ≤ (k:ℝ) := by exact_mod_cast hn
    rw [abs_of_nonneg (by linarith : 0 ≤ E-(2*(j:ℝ)+1))]
    linarith
  · subst j
    exact le_rfl
  · have hn : k+1 ≤ j := by omega
    have hr : (k:ℝ)+1 ≤ (j:ℝ) := by exact_mod_cast hn
    rw [abs_of_nonpos (by linarith : E-(2*(j:ℝ)+1) ≤ 0)]
    linarith

theorem cell_displacement_le_one (E : ℝ) (k : ℤ)
    (hlo : 2*(k:ℝ) ≤ E) (hhi : E ≤ 2*(k:ℝ)+2) :
    |E-oddLevel k| ≤ 1 := by
  unfold oddLevel
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem cell_displacement_endpoint (k : ℤ) :
    |2*(k:ℝ)-oddLevel k| = 1 := by
  unfold oddLevel
  rw [show 2*(k:ℝ)-(2*(k:ℝ)+1) = -1 by ring]
  norm_num

theorem cell_cost_nearest (E : ℝ) (k j : ℤ)
    (hlo : 2*(k:ℝ) ≤ E) (hhi : E ≤ 2*(k:ℝ)+2)
    (φ : ℝ → ℝ) (hφ : Monotone φ) :
    φ |E-oddLevel k| ≤ φ |E-oddLevel j| :=
  hφ (odd_cell_nearest E k j hlo hhi)

/-- Actual primal infimum for an arbitrary real cost with an attained
pointwise lower bound. The necessary a.e. comparisons and marginal
identities are explicit; their construction for the Gibbs law is open. -/
theorem primal_infimum_of_attainment
    (μ ν : Measure ℝ) (c : ℝ × ℝ → ℝ) (m : ℝ → ℝ)
    (γ₀ : Measure (ℝ × ℝ)) (hγ₀ : γ₀ ∈ couplings μ ν)
    (hm : Integrable m μ)
    (hc : ∀ γ ∈ couplings μ ν, Integrable c γ)
    (hbelow : ∀ γ ∈ couplings μ ν, ∀ᵐ p ∂γ, m p.1 ≤ c p)
    (heq : ∀ᵐ p ∂γ₀, c p = m p.1) :
    sInf ((fun γ : Measure (ℝ × ℝ) => ∫ p, c p ∂γ) '' couplings μ ν) =
      ∫ x, m x ∂μ := by
  let C : Measure (ℝ × ℝ) → ℝ := fun γ => ∫ p, c p ∂γ
  have hcomp (γ : Measure (ℝ × ℝ)) (hγ : γ ∈ couplings μ ν) :
      (∫ p : ℝ × ℝ, m p.1 ∂γ) = ∫ x, m x ∂μ := by
    change Measure.map Prod.fst γ = μ ∧ Measure.map Prod.snd γ = ν at hγ
    have hmeas : AEStronglyMeasurable m (Measure.map Prod.fst γ) := by
      rw [hγ.1]; exact hm.aestronglyMeasurable
    rw [← integral_map measurable_fst.aemeasurable hmeas, hγ.1]
  have hbound : ∀ γ ∈ couplings μ ν, (∫ x, m x ∂μ) ≤ C γ := by
    intro γ hγ
    have hfst : MeasurePreserving Prod.fst γ μ := ⟨measurable_fst, hγ.1⟩
    have hi : Integrable (fun p : ℝ × ℝ => m p.1) γ :=
      hfst.integrable_comp_of_integrable hm
    rw [← hcomp γ hγ]
    exact integral_mono_ae hi (hc γ hγ) (hbelow γ hγ)
  have hb : BddBelow (C '' couplings μ ν) := by
    refine ⟨∫ x, m x ∂μ, ?_⟩
    rintro _ ⟨γ, hγ, rfl⟩
    exact hbound γ hγ
  have hval : C γ₀ = ∫ x, m x ∂μ :=
    (integral_congr_ae heq).trans (hcomp γ₀ hγ₀)
  change sInf (C '' couplings μ ν) = _
  apply le_antisymm
  · rw [← hval]
    exact csInf_le hb (Set.mem_image_of_mem C hγ₀)
  · apply le_csInf ⟨C γ₀, Set.mem_image_of_mem C hγ₀⟩
    rintro _ ⟨γ, hγ, rfl⟩
    exact hbound γ hγ

/-- Exact mass of a cell as difference of exponential survival values. -/
theorem cell_mass (x : ℝ) (k : ℕ) :
    Real.exp (-2*x*(k:ℝ)) - Real.exp (-2*x*((k:ℝ)+1)) =
      (1-Real.exp (-2*x))*Real.exp (-2*x*(k:ℝ)) := by
  rw [show -2*x*((k:ℝ)+1) = -2*x + -2*x*(k:ℝ) by ring, Real.exp_add]
  ring

theorem normalized_geometric (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' k : ℕ, (1-r)*r^k) = 1 := by
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  have h : 1-r ≠ 0 := by linarith
  field_simp

theorem odd_partition_formula (x : ℝ) (hx : 0 < x) :
    (∑' k : ℕ, Real.exp (-x)*(Real.exp (-2*x))^k) =
      Real.exp (-x)/(1-Real.exp (-2*x)) := by
  have h0 : 0 ≤ Real.exp (-2*x) := (Real.exp_pos _).le
  have h1 : Real.exp (-2*x) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  rw [tsum_mul_left, tsum_geometric_of_lt_one h0 h1, div_eq_mul_inv]

/-- The normalized trace factor from the actual geometric sum above. -/
theorem normalized_partition (x : ℝ) (hx : 0 < x) :
    2*x*(Real.exp (-x)/(1-Real.exp (-2*x))) =
      x/Real.sinh x := by
  have h0 : Real.exp x ≠ 0 := (Real.exp_pos _).ne'
  have he : Real.exp (-2*x) = (Real.exp x)⁻¹^2 := by
    rw [show -2*x = -x + -x by ring, Real.exp_add, Real.exp_neg]
    ring
  rw [he, Real.exp_neg, Real.sinh_eq, Real.exp_neg]
  have hpos : 1 < Real.exp x := by simpa using Real.exp_lt_exp.mpr hx
  have hne : Real.exp x - (Real.exp x)⁻¹ ≠ 0 := by
    have hi : (Real.exp x)⁻¹ < 1 := by
      rw [inv_lt_one₀ (Real.exp_pos x)]
      exact hpos
    linarith
  have hd : 1-(Real.exp x)⁻¹^2 ≠ 0 := by
    have hp : 0 < (Real.exp x)⁻¹ := by positivity
    have hi : (Real.exp x)⁻¹ < 1 := by
      rw [inv_lt_one₀ (Real.exp_pos x)]
      exact hpos
    nlinarith
  field_simp
  <;> ring

theorem variance_difference (x s : ℝ) :
    1/x^2-1/s^2 = (1/x)^2-(1/s)^2 := by ring

theorem wasserstein2_langevin (x c : ℝ) (hx : x ≠ 0) :
    1-2*(c-1/x)/x = 1-2*c/x+2/x^2 := by field_simp <;> ring

theorem uniform_arcsine_relation (q : ℝ) :
    5/6-2*q^2 = (1:ℝ)/3-2*(q-1/2)-2*(q-1/2)^2 := by ring

theorem zeta_weighted_difference (l s : ℝ) :
    5/6*l-s = (5/6-s)+(5/6:ℝ)*(l-1) := by ring

theorem schwarzian_majorant : (1:ℚ)/4*(17/8)*(16/25)=17/50 := by norm_num
theorem dilatation_bound : ((1:ℚ)+17/100)/(1-17/100)=117/83 := by norm_num
theorem kahler_boundary : (1:ℚ)/(1+(3/2)^2)=4/13 ∧ (1:ℚ)/(1+(1/2)^2)=4/5 := by norm_num

end Manuscript15.MagneticGibbs
#print axioms Manuscript15.MagneticGibbs.odd_cell_nearest
#print axioms Manuscript15.MagneticGibbs.cell_displacement_le_one
#print axioms Manuscript15.MagneticGibbs.cell_displacement_endpoint
#print axioms Manuscript15.MagneticGibbs.cell_cost_nearest
#print axioms Manuscript15.MagneticGibbs.primal_infimum_of_attainment
#print axioms Manuscript15.MagneticGibbs.cell_mass
#print axioms Manuscript15.MagneticGibbs.normalized_geometric
#print axioms Manuscript15.MagneticGibbs.odd_partition_formula
#print axioms Manuscript15.MagneticGibbs.normalized_partition
#print axioms Manuscript15.MagneticGibbs.variance_difference
#print axioms Manuscript15.MagneticGibbs.wasserstein2_langevin
#print axioms Manuscript15.MagneticGibbs.uniform_arcsine_relation
#print axioms Manuscript15.MagneticGibbs.zeta_weighted_difference
#print axioms Manuscript15.MagneticGibbs.schwarzian_majorant
#print axioms Manuscript15.MagneticGibbs.dilatation_bound
#print axioms Manuscript15.MagneticGibbs.kahler_boundary
