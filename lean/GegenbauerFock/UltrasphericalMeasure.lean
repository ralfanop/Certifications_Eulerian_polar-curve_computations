import Mathlib

/-!
# General Gegenbauer/ultraspherical probability measure

For λ > 0, define the symmetric ultraspherical probability measure by
pushing forward the Mathlib Beta(λ + 1/2, λ + 1/2) probability law
under x ↦ 2x - 1.

This definition is a concrete measure, not an abstract unspecified
probability measure. A change-of-variables proof equating its
Lebesgue density with the classical Gamma-normalized
(1-u²)^(λ-1/2) profile remains a separate obligation.
Likewise the general even moments and symmetry must be
proved separately.

Mathlib's betaMeasure and its probability theorem already include
the analytic Gamma/Beta normalization proof.
-/

open MeasureTheory ProbabilityTheory

namespace GegenbauerFock.Ultraspherical

/-- The equal Beta shape parameters associated with ultraspherical λ. -/
noncomputable def shape (lam : ℝ) : ℝ := lam + 1 / 2

/-- Affine change of variables transporting the beta law to [-1,1]. -/
def betaToInterval (x : ℝ) : ℝ := 2*x - 1

/-- Concrete general ultraspherical probability measure. -/
noncomputable def measure (lam : ℝ) : Measure ℝ :=
  (ProbabilityTheory.betaMeasure (shape lam) (shape lam)).map betaToInterval

theorem shape_pos (lam : ℝ) (hlam : 0 < lam) : 0 < shape lam := by
  unfold shape
  linarith

/-- Genuine normalization of the general-parameter measure. -/
theorem probability (lam : ℝ) (hlam : 0 < lam) :
    IsProbabilityMeasure (measure lam) := by
  letI : IsProbabilityMeasure
      (ProbabilityTheory.betaMeasure (shape lam) (shape lam)) :=
    ProbabilityTheory.isProbabilityMeasureBeta
      (shape_pos lam hlam) (shape_pos lam hlam)
  unfold measure
  infer_instance

theorem measure_univ (lam : ℝ) (hlam : 0 < lam) :
    measure lam Set.univ = 1 := by
  letI : IsProbabilityMeasure (measure lam) := probability lam hlam
  exact IsProbabilityMeasure.measure_univ

/-- The probability normalization is also available as an actual
Bochner integral of the constant real function. -/
theorem integral_one (lam : ℝ) (hlam : 0 < lam) :
    (∫ _u : ℝ, (1 : ℝ) ∂(measure lam)) = 1 := by
  letI : IsProbabilityMeasure (measure lam) := probability lam hlam
  simp

/-- The Mathlib symmetric Beta density is strictly positive
inside its support, for every positive ultraspherical λ. -/
theorem beta_density_pos (lam x : ℝ) (hlam : 0 < lam)
    (hx0 : 0 < x) (hx1 : x < 1) :
    0 < ProbabilityTheory.betaPDFReal (shape lam) (shape lam) x :=
  ProbabilityTheory.betaPDFReal_pos hx0 hx1
    (shape_pos lam hlam) (shape_pos lam hlam)

/-- Symmetry of the underlying Beta density about x = 1/2.
This is a pointwise density lemma, not yet invariance of the
pushforward measure under u ↦ -u. -/
theorem beta_density_reflection (lam x : ℝ)
    (hx0 : 0 < x) (hx1 : x < 1) :
    ProbabilityTheory.betaPDFReal (shape lam) (shape lam) (1-x) =
      ProbabilityTheory.betaPDFReal (shape lam) (shape lam) x := by
  have hx'0 : 0 < 1-x := by linarith
  have hx'1 : 1-x < 1 := by linarith
  have h : (1:ℝ) - (1-x) = x := by ring
  simp [ProbabilityTheory.betaPDFReal, hx0, hx1, hx'0, hx'1,
    h, mul_comm, mul_left_comm, mul_assoc]

/-- The symmetric Beta law has almost-everywhere support (0,1).
The statement is a measure-theoretic fact, not merely a pointwise
claim about its density. -/
theorem beta_ae_unit_interval (lam : ℝ) :
    ∀ᵐ x ∂(ProbabilityTheory.betaMeasure (shape lam) (shape lam)),
      x ∈ Set.Ioo (0:ℝ) 1 := by
  unfold ProbabilityTheory.betaMeasure
  have hpdf : AEMeasurable
      (ProbabilityTheory.betaPDF (shape lam) (shape lam)) volume :=
    (Measurable.ennreal_ofReal
      (ProbabilityTheory.measurable_betaPDFReal (shape lam) (shape lam))).aemeasurable
  apply (ae_withDensity_iff' hpdf).2
  filter_upwards [] with x
  intro hx
  constructor
  · by_contra hn
    exact hx (ProbabilityTheory.betaPDF_eq_zero_of_nonpos (le_of_not_gt hn))
  · by_contra hn
    exact hx (ProbabilityTheory.betaPDF_eq_zero_of_one_le (le_of_not_gt hn))

/-- Ultraspherical measure is supported in [-1,1] for all real λ
(for probability normalisation additionally require λ>0). -/
theorem ae_mem_unit_interval (lam : ℝ) :
    ∀ᵐ u ∂measure lam, u ∈ Set.Icc (-1:ℝ) 1 := by
  have hmeas : Measurable betaToInterval := by
    unfold betaToInterval
    fun_prop
  apply (ae_map_iff hmeas.aemeasurable measurableSet_Icc).2
  filter_upwards [beta_ae_unit_interval lam] with x hx
  change (-1:ℝ) ≤ betaToInterval x ∧ betaToInterval x ≤ 1
  unfold betaToInterval
  constructor <;> linarith [hx.1, hx.2]

/-- The *unclamped original Eulerian coherent section* really
belongs to L² of the concrete general ultraspherical probability law.
This theorem uses the proved [-1,1] support statement rather than
postulating an integrability hypothesis. -/
theorem originalCoherent_memLp (lam : ℝ) (hlam : 0 < lam) (z : ℂ) :
    MemLp (fun u : ℝ => Complex.exp (Complex.I*z*(u:ℂ)/2))
      2 (measure lam) := by
  letI : IsProbabilityMeasure (measure lam) := probability lam hlam
  have hcontinuous :
      Continuous (fun u : ℝ => Complex.exp (Complex.I*z*(u:ℂ)/2)) := by
    fun_prop
  apply MemLp.of_bound hcontinuous.aestronglyMeasurable
    (Real.exp (‖z‖/2))
  filter_upwards [ae_mem_unit_interval lam] with u hu
  have habs : |u| ≤ 1 := abs_le.mpr ⟨hu.1, hu.2⟩
  have hnorm : ‖(u:ℂ)‖ ≤ 1 := by simpa using habs
  have harg : ‖Complex.I*z*(u:ℂ)/2‖ ≤ ‖z‖/2 := by
    calc
      ‖Complex.I*z*(u:ℂ)/2‖ = ‖z‖ * ‖(u:ℂ)‖ / 2 := by
        simp [norm_mul, mul_comm, mul_left_comm, mul_assoc]
      _ ≤ ‖z‖ * 1 / 2 := by gcongr
      _ = ‖z‖/2 := by ring
  exact (Complex.norm_exp_le_exp_norm _).trans
    (Real.exp_le_exp.mpr harg)

/-- Each z gives a genuine L² equivalence class on the beta-pushforward measure. -/
noncomputable def originalCoherentLp (lam : ℝ) (hlam : 0 < lam) (z : ℂ) :
    Lp ℂ 2 (measure lam) :=
  (originalCoherent_memLp lam hlam z).toLp
    (fun u : ℝ => Complex.exp (Complex.I*z*(u:ℂ)/2))

/-- Actual bounded evaluation/coefficient functional on ultraspherical L².
This is a scalar-valued map, not yet the full Fock-valued operator. -/
noncomputable def fourierFunctional (lam : ℝ) (hlam : 0 < lam) (z : ℂ) :
    Lp ℂ 2 (measure lam) →L[ℂ] ℂ :=
  innerSL ℂ (originalCoherentLp lam hlam (-star z))

theorem fourierFunctional_norm (lam : ℝ) (hlam : 0 < lam) (z : ℂ) :
    ‖fourierFunctional lam hlam z‖ =
      ‖originalCoherentLp lam hlam (-star z)‖ := by
  exact innerSL_apply_norm ℂ (originalCoherentLp lam hlam (-star z))

theorem fourierFunctional_adjoint (lam : ℝ) (hlam : 0 < lam) (z : ℂ) :
    (fourierFunctional lam hlam z).adjoint =
      ContinuousLinearMap.toSpanSingleton ℂ
        (originalCoherentLp lam hlam (-star z)) := by
  exact ContinuousLinearMap.adjoint_innerSL_apply _

#print axioms GegenbauerFock.Ultraspherical.shape_pos
#print axioms GegenbauerFock.Ultraspherical.probability
#print axioms GegenbauerFock.Ultraspherical.measure_univ
#print axioms GegenbauerFock.Ultraspherical.integral_one
#print axioms GegenbauerFock.Ultraspherical.beta_density_pos
#print axioms GegenbauerFock.Ultraspherical.beta_density_reflection
#print axioms GegenbauerFock.Ultraspherical.beta_ae_unit_interval
#print axioms GegenbauerFock.Ultraspherical.ae_mem_unit_interval
#print axioms GegenbauerFock.Ultraspherical.originalCoherent_memLp
#print axioms GegenbauerFock.Ultraspherical.fourierFunctional_norm
#print axioms GegenbauerFock.Ultraspherical.fourierFunctional_adjoint

end GegenbauerFock.Ultraspherical
