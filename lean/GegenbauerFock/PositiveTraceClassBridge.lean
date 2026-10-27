import GegenbauerFock.GramNuclearTrace

/-!
# V007: abstract positive nuclear Hilbert-space trace presentation

The pinned Mathlib provides Hilbert adjoints, compactness, spectral
theory, and infinite operator-norm summability, but no independent
Schatten-ideal class API has been identified in the locked version.
We therefore give a *reusable* structural positive-nuclear
presentation predicate on any complete complex Hilbert space:
a convergent sequence of rank-one maps r_n†r_n, with
summable squared row norms. This is a genuine positive trace-class
witness, but does NOT silently claim equality to a separately
defined, universal S₁ ideal norm object.

The concrete C†C satisfies the witness unconditionally; its
positive nuclear mass coincides with every complete Hilbert-basis
diagonal trace and with the Gamma-normalized Kummer function.
-/

namespace GegenbauerFock.PositiveNuclearIdeal

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A positive nuclear operator is represented as a norm-summable
series of positive rank-one maps r_n†r_n, with finite total squared
row norm. This is independent of the ultraspherical model. -/
def HasPositiveNuclearRows (T : E →L[ℂ] E) : Prop :=
  ∃ rows : ℕ → (E →L[ℂ] ℂ),
    Summable (fun n => ‖rows n‖ ^ 2) ∧
      T = ∑' n, (rows n).adjoint.comp (rows n)

/-- Each positive rank-one Hilbert operator has exactly the squared
operator norm of its defining linear functional. -/
theorem positiveRankOne_norm_eq_row_sq (r : E →L[ℂ] ℂ) :
    ‖r.adjoint.comp r‖ = ‖r‖ ^ 2 := by
  rw [ContinuousLinearMap.norm_adjoint_comp_self]
  ring

/-- For any sequence of Hilbert-space rows with summable squared norms,
the positive rank-one operator series converges ABSOLUTELY in the
Banach-space operator norm; no assumed operator-series convergence. -/
theorem positiveRankOne_summable
    (rows : ℕ → (E →L[ℂ] ℂ))
    (hs : Summable (fun n : ℕ => ‖rows n‖ ^ 2)) :
    Summable (fun n : ℕ => (rows n).adjoint.comp (rows n)) := by
  apply Summable.of_norm
  simpa only [positiveRankOne_norm_eq_row_sq] using hs

#print axioms GegenbauerFock.PositiveNuclearIdeal.positiveRankOne_norm_eq_row_sq
#print axioms GegenbauerFock.PositiveNuclearIdeal.positiveRankOne_summable

#print axioms GegenbauerFock.PositiveNuclearIdeal.HasPositiveNuclearRows

end GegenbauerFock.PositiveNuclearIdeal

namespace GegenbauerFock.GeneralUltrasphericalFock

open MeasureTheory

/-- The actual positive Gram integral operator C†C has a general
positive-nuclear Hilbert-space witness made of its genuinely
summable Fourier-moment rows, not a formal spectral surrogate. -/
theorem gram_hasPositiveNuclearRows
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    PositiveNuclearIdeal.HasPositiveNuclearRows
      (gram lam alpha hlam ha) := by
  letI : IsProbabilityMeasure (Ultraspherical.measure lam) :=
    Ultraspherical.probability lam hlam
  unfold PositiveNuclearIdeal.HasPositiveNuclearRows
  refine ⟨(fun n : ℕ =>
    WeightedMoments.coefficient
      (Ultraspherical.measure lam) (ae_abs_le_one lam) alpha n),
    ?_, ?_⟩
  · exact WeightedMoments.coefficient_norm_sq_summable
      (Ultraspherical.measure lam) (ae_abs_le_one lam) alpha ha
  · rw [gram_eq_nuclear_tsum lam alpha hlam ha]
    rfl

/-- The total nuclear rank-one norm mass equals EVERY complete
Hilbert-basis trace of the positive Gram operator; this is the
basis-independent positive trace-class mass statement. -/
theorem gram_positiveNuclearMass_eq_basisTrace
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    {ι : Type*}
    (b : HilbertBasis ι ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) :
    (∑' n : ℕ, ‖gramNuclearTerm lam alpha hlam ha n‖) =
      ∑' i : ι,
        RCLike.re (inner ℂ (gram lam alpha hlam ha (b i)) (b i)) := by
  calc
    (∑' n : ℕ, ‖gramNuclearTerm lam alpha hlam ha n‖) =
      KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) :=
        gramNuclearMass_eq_kummerSeries lam alpha hlam ha
    _ = ∑' i : ι,
        RCLike.re (inner ℂ (gram lam alpha hlam ha (b i)) (b i)) :=
          (gram_sourceBasis_trace_eq_kummer lam alpha hlam ha b).symm

/-- The diagonal trace of the actual positive Gram operator equals
Gamma(λ+1) times Mathlib's *regularized* complex confluent
hypergeometric function on the relevant positive real argument. -/
theorem gram_basisTrace_eq_mathlibRegularizedKummer
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    {ι : Type*}
    (b : HilbertBasis ι ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) :
    ((∑' i : ι,
        RCLike.re (inner ℂ (gram lam alpha hlam ha (b i)) (b i))) : ℂ) =
      Complex.Gamma (((lam + 1 : ℝ) : ℂ)) *
        KummerCoefficients.mathlibRegularizedKummer lam
          (((1 / (4 * alpha) : ℝ) : ℂ)) := by
  rw [← Complex.ofReal_tsum]
  rw [gram_sourceBasis_trace_eq_kummer lam alpha hlam ha b]
  exact KummerCoefficients.kummerSeries_eq_gamma_mul_mathlibRegularized
    lam (1 / (4 * alpha)) hlam

/-- Exactly the same Gamma-normalized complex hypergeometric
formula for the Hilbert--Schmidt energy of the actual transform
measured on an arbitrary complete source basis. -/
theorem C_basisHSEnergy_eq_mathlibRegularizedKummer
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    {ι : Type*}
    (b : HilbertBasis ι ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) :
    ((∑' i : ι, ‖C lam alpha hlam ha (b i)‖ ^ 2) : ℂ) =
      Complex.Gamma (((lam + 1 : ℝ) : ℂ)) *
        KummerCoefficients.mathlibRegularizedKummer lam
          (((1 / (4 * alpha) : ℝ) : ℂ)) := by
  simp only [← Complex.ofReal_pow]
  rw [← Complex.ofReal_tsum]
  rw [C_sourceBasis_HSEnergy_eq_kummer lam alpha hlam ha b]
  exact KummerCoefficients.kummerSeries_eq_gamma_mul_mathlibRegularized
    lam (1 / (4 * alpha)) hlam

#print axioms GegenbauerFock.GeneralUltrasphericalFock.gram_hasPositiveNuclearRows
#print axioms GegenbauerFock.GeneralUltrasphericalFock.gram_positiveNuclearMass_eq_basisTrace
#print axioms GegenbauerFock.GeneralUltrasphericalFock.gram_basisTrace_eq_mathlibRegularizedKummer
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_basisHSEnergy_eq_mathlibRegularizedKummer

end GegenbauerFock.GeneralUltrasphericalFock
