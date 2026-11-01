import GegenbauerFock.UltrasphericalInteriorSupport
import GegenbauerFock.OutputAnalyticUniquenessReduction

/-!
# V007 — from almost-everywhere analytic vanishing to interior pointwise vanishing

The actual ultraspherical measure has positive mass on every nonempty
interior interval. Consequently, a continuous complex function that
vanishes almost everywhere for that measure vanishes at every point
of (-1,1). We also prove that the genuine transported Beta law is
concentrated on the *open* interval, rather than merely on [-1,1].

Application to the genuine Fock adjoint is deliberately conditional on
continuity of the reconstruction. Analyticity and pointwise identity
uniqueness are further, separate obligations. No injectivity of C† is
claimed in this file.
-/

noncomputable section

open MeasureTheory Set

namespace GegenbauerFock.Ultraspherical

/-- The actual symmetric Beta pushforward is almost surely in the open
interval (-1,1); its endpoints carry no mass. -/
theorem ae_mem_open_interval (lam : ℝ) :
    ∀ᵐ u ∂measure lam, u ∈ Set.Ioo (-1 : ℝ) 1 := by
  have hmeas : Measurable betaToInterval := by
    unfold betaToInterval
    fun_prop
  apply (ae_map_iff hmeas.aemeasurable measurableSet_Ioo).2
  filter_upwards [beta_ae_unit_interval lam] with x hx
  change (-1 : ℝ) < betaToInterval x ∧ betaToInterval x < 1
  unfold betaToInterval
  constructor <;> linarith [hx.1, hx.2]

/-- A continuous complex function vanishing νλ-a.e. vanishes at
*every* interior point. The proof uses actual positive measure on
interior intervals, not merely positivity of a candidate density. -/
theorem continuous_ae_zero_implies_interior_zero
    (lam : ℝ) (hlam : 0 < lam)
    {f : ℝ → ℂ} (hf : Continuous f)
    (hz : f =ᵐ[measure lam] (0 : ℝ → ℂ)) :
    ∀ u ∈ Set.Ioo (-1 : ℝ) 1, f u = 0 := by
  intro u hu
  by_contra hne
  let U : Set ℝ := Set.Ioo (-1 : ℝ) 1 ∩ {x : ℝ | f x ≠ 0}
  have hopen : IsOpen U := by
    dsimp [U]
    apply isOpen_Ioo.inter
    change IsOpen (f ⁻¹' ({(0 : ℂ)} : Set ℂ)ᶜ)
    exact isClosed_singleton.isOpen_compl.preimage hf
  obtain ⟨a, b, hab, hsub⟩ :=
    hopen.exists_Ioo_subset (show U.Nonempty from ⟨u, ⟨hu, hne⟩⟩)
  have hinside : Set.Ioo a b ⊆ Set.Ioo (-1 : ℝ) 1 :=
    hsub.trans Set.inter_subset_left
  have hbounds : (-1 : ℝ) ≤ a ∧ b ≤ 1 :=
    (Set.Ioo_subset_Ioo_iff hab).mp hinside
  have hnull : measure lam {x : ℝ | f x ≠ 0} = 0 := by
    exact ae_iff.mp hz
  have hintervalnull : measure lam (Set.Ioo a b) = 0 :=
    measure_mono_null (hsub.trans Set.inter_subset_right) hnull
  exact (ne_of_gt (measure_Ioo_pos lam a b hlam hbounds.1 hab hbounds.2))
    hintervalnull

/-- For a continuous complex function, νλ-a.e. vanishing is
*equivalent* to pointwise vanishing throughout (-1,1). -/
theorem continuous_ae_zero_iff_interior_zero
    (lam : ℝ) (hlam : 0 < lam)
    {f : ℝ → ℂ} (hf : Continuous f) :
    f =ᵐ[measure lam] (0 : ℝ → ℂ) ↔
      ∀ u ∈ Set.Ioo (-1 : ℝ) 1, f u = 0 := by
  constructor
  · exact continuous_ae_zero_implies_interior_zero lam hlam hf
  · intro h
    filter_upwards [ae_mem_open_interval lam] with u hu
    exact h u hu

#print axioms GegenbauerFock.Ultraspherical.ae_mem_open_interval
#print axioms GegenbauerFock.Ultraspherical.continuous_ae_zero_implies_interior_zero
#print axioms GegenbauerFock.Ultraspherical.continuous_ae_zero_iff_interior_zero

end GegenbauerFock.Ultraspherical

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- For a Fock reconstruction *known to be continuous*, the kernel
of the actual Hilbert adjoint is exactly its pointwise zero set on
the open ultraspherical interval. Continuity is an explicit premise. -/
theorem C_adjoint_eq_zero_iff_interior_zero_of_continuous
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (F : InfiniteAnalysis.FockCoefficients)
    (hcont : Continuous (FockAnalyticRestriction.evaluate alpha ha F)) :
    C_adjoint lam alpha hlam ha F = 0 ↔
      ∀ u ∈ Set.Ioo (-1 : ℝ) 1,
        FockAnalyticRestriction.evaluate alpha ha F u = 0 := by
  exact
    (C_adjoint_eq_zero_iff_analytic_restriction_ae_zero
      lam alpha hlam ha F).trans
      (Ultraspherical.continuous_ae_zero_iff_interior_zero lam hlam hcont)

/-- Precise final two-premise reduction for output dense range:
continuity of all Fock restrictions and their uniqueness on (-1,1)
suffice for injectivity of the genuine Hilbert adjoint. Neither
analytic premise is silently asserted. -/
theorem C_adjoint_injective_of_continuous_interior_unique
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (hcont : ∀ F : InfiniteAnalysis.FockCoefficients,
      Continuous (FockAnalyticRestriction.evaluate alpha ha F))
    (hunique : ∀ F : InfiniteAnalysis.FockCoefficients,
      (∀ u ∈ Set.Ioo (-1 : ℝ) 1,
        FockAnalyticRestriction.evaluate alpha ha F u = 0) → F = 0) :
    Function.Injective (C_adjoint lam alpha hlam ha) := by
  apply (C_adjoint_injective_iff_analytic_uniqueness_ae
    lam alpha hlam ha).mpr
  intro F hz
  apply hunique F
  exact (Ultraspherical.continuous_ae_zero_iff_interior_zero
    lam hlam (hcont F)).mp hz

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_adjoint_eq_zero_iff_interior_zero_of_continuous
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_adjoint_injective_of_continuous_interior_unique

end GegenbauerFock.GeneralUltrasphericalFock
