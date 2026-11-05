import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatComplexCFCS1Bridge
import GegenbauerFock.RationalTraceAnalyticTail
import GegenbauerFock.PhyslibTraceClassCompat

/-!
# V007 — a rigorous trace obstruction to identifying the real heat and complex Fock Gram

The actual REAL Gegenbauer Sturm heat semigroup has projective nuclear
S1 norm sum_n exp(-s*n*(n+2*lambda)). The ACTUAL COMPLEX Fock Gram
C^* C has genuine Physlib CFC trace norm equal to the Kummer series.

An eigenbasis-preserving real-linear intertwiner from the real heat
operator to the complex Gram would force equality of these traces.
This gives a rigorous NO-GO theorem whenever the two certified
scalar trace values differ.

At the explicit Eulerian Legendre/Fock specialization
  lambda = 1/2, alpha = 1, heat time s = 1/10,
the Gram trace is < 11/10 by the separately kernel-checked rational
15-term Taylor enclosure, while the real heat trace is >= 9/5 using
only n=0,1 and the classical exp(x) >= 1+x bound. Consequently
no complete-basis-preserving real-linear intertwiner can exist here.

No assumption of a general spectral correspondence is made.
This is an obstruction to ONE specific stronger correspondence, not a
claim that every possible weaker relationship is excluded.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory InnerProductSpace

private abbrev HR (lam : ℝ) := Lp ℝ 2 (measure lam)
private abbrev HC (lam : ℝ) := Lp ℂ 2 (measure lam)

/-- Necessary trace-matching condition: a complete-basis-preserving
real-linear intertwining between the actual weighted-real-L2 Sturm
heat semigroup and actual complex Gegenbauer--Fock Gram cannot exist
if their exact intrinsic trace norms differ. -/
theorem no_heat_fockGram_basis_intertwiner_of_trace_gap
    (lam alpha s : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (hs : 0 < s)
    (hgap :
      (∑' n : ℕ, Real.exp (-s * ((n : ℝ) * ((n : ℝ) + 2 * lam)))) ≠
        KummerCoefficients.kummerSeries lam (1 / (4 * alpha))) :
    ¬ ∃ (bC : HilbertBasis ℕ ℂ (HC lam))
        (J : HR lam →ₗ[ℝ] HC lam),
        (∀ n : ℕ,
          J ((sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam) n) =
            bC n) ∧
        (∀ f : HR lam,
          GegenbauerFock.GeneralUltrasphericalFock.gram lam alpha hlam ha
              (J f) =
            J (sturmRealHeatLimitCLM lam hlam s (le_of_lt hs) f)) := by
  rintro ⟨bC, J, hJ, hcomm⟩
  let G := GegenbauerFock.GeneralUltrasphericalFock.gram lam alpha hlam ha
  have hGpos : 0 ≤ G :=
    GegenbauerFock.GeneralUltrasphericalFock.gram_nonneg lam alpha hlam ha
  obtain ⟨hGclass, hEq⟩ :=
    sturmRealHeat_realS1_eq_complexCFC_autoClass_of_intertwining
      lam s hlam hs G bC J hJ hcomm hGpos
  have hGnorm :
      ProbabilisticTheory.traceNorm G hGclass =
        KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) := by
    simpa only [G] using
      (GegenbauerFock.GeneralUltrasphericalFock.gram_traceNorm_eq_kummer
        lam alpha hlam ha)
  have hHnorm :
      realNuclearInfimum
          (sturmRealHeatLimitCLM lam hlam s (le_of_lt hs)) =
        ∑' n : ℕ,
          Real.exp (-s * ((n : ℝ) * ((n : ℝ) + 2 * lam))) :=
    sturmRealHeat_realNuclearInfimum_eq_spectralTrace_directDuality
      lam s hlam hs
  apply hgap
  calc
    (∑' n : ℕ, Real.exp (-s * ((n : ℝ) * ((n : ℝ) + 2 * lam)))) =
        realNuclearInfimum
          (sturmRealHeatLimitCLM lam hlam s (le_of_lt hs)) :=
      hHnorm.symm
    _ = ProbabilisticTheory.traceNorm G hGclass := hEq
    _ = KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) := hGnorm

/-- The independently certified 15-term rational Taylor interval
implies the genuine Eulerian complex Fock Gram trace is < 11/10. -/
theorem eulerian_half_one_fock_gram_trace_lt_eleven_tenths :
    KummerCoefficients.kummerSeries (1 / 2) (1 / 4) <
      (11 / 10 : ℝ) := by
  have hI := GegenbauerFock.RationalTrace.legendre_exp_integral_decimal_enclosure
  have hK :
      KummerCoefficients.kummerSeries (1 / 2) (1 / 4) =
        (∫ u : ℝ, Real.exp (u ^ 2 / 4)
          ∂(measure (1 / 2))) :=
    (GegenbauerFock.RationalTrace.kummer_half_quarter_eq_realTraceSeries).trans
      (GegenbauerFock.RationalTrace.legendre_exp_integral_eq_realTraceSeries).symm
  rw [hK]
  exact lt_trans hI.2 (by norm_num)

/-- At the explicit positive heat time 1/10 the genuine real Legendre
heat semigroup has nuclear trace at least 9/5. The two lowest modes
are enough, so no numerical approximation of exp is needed. -/
theorem legendre_heat_trace_one_tenth_ge_nine_fifths :
    (9 / 5 : ℝ) ≤
      ∑' n : ℕ,
        Real.exp (-(1 / 10 : ℝ) *
          ((n : ℝ) * ((n : ℝ) + 2 * (1 / 2 : ℝ)))) := by
  let beta : ℕ → ℝ := fun n =>
    Real.exp (-(1 / 10 : ℝ) *
      ((n : ℝ) * ((n : ℝ) + 2 * (1 / 2 : ℝ))))
  have hb : Summable beta :=
    sturmRealHeat_spectral_multiplier_summable
      (1 / 2) (1 / 10) (by norm_num) (by norm_num)
  have hpos (n : ℕ) : 0 ≤ beta n :=
    (Real.exp_pos _).le
  have h2 :
      (∑ n ∈ Finset.range 2, beta n) ≤ ∑' n : ℕ, beta n :=
    sum_le_hasSum (Finset.range 2) (fun n _ => hpos n) hb.hasSum
  have h0 : beta 0 = 1 := by
    norm_num [beta]
  have h1 : beta 1 = Real.exp (-(1 / 5 : ℝ)) := by
    norm_num [beta]
  have hpartial :
      (∑ n ∈ Finset.range 2, beta n) =
        1 + Real.exp (-(1 / 5 : ℝ)) := by
    simp [Finset.sum_range_succ, h0, h1]
  have hexp : (4 / 5 : ℝ) ≤ Real.exp (-(1 / 5 : ℝ)) := by
    have hh := Real.add_one_le_exp (-(1 / 5 : ℝ))
    linarith
  change (9 / 5 : ℝ) ≤ ∑' n : ℕ, beta n
  calc
    (9 / 5 : ℝ) ≤ 1 + Real.exp (-(1 / 5 : ℝ)) := by linarith
    _ = ∑ n ∈ Finset.range 2, beta n := hpartial.symm
    _ ≤ ∑' n : ℕ, beta n := h2

/-- Concrete NO-GO theorem: no complete-orthonormal-basis-preserving
real-linear intertwiner between the ACTUAL Legendre Sturm heat operator
at time s=1/10 and the ACTUAL Gegenbauer--Fock complex Gram
C_(1/2,1)^* C_(1/2,1). Their certified traces are strictly different:
heat >= 9/5 > 11/10 > Gram. -/
theorem no_legendre_heat_one_tenth_to_fock_gram_one_basis_intertwiner :
    ¬ ∃ (bC : HilbertBasis ℕ ℂ (HC (1 / 2)))
        (J : HR (1 / 2) →ₗ[ℝ] HC (1 / 2)),
        (∀ n : ℕ,
          J ((sturmMonicEigenCandidate_realL2_hilbertBasis
            (1 / 2) (by norm_num)) n) = bC n) ∧
        (∀ f : HR (1 / 2),
          GegenbauerFock.GeneralUltrasphericalFock.gram
              (1 / 2) 1 (by norm_num) (by norm_num) (J f) =
            J (sturmRealHeatLimitCLM
              (1 / 2) (by norm_num) (1 / 10) (by norm_num) f)) := by
  have hLow := legendre_heat_trace_one_tenth_ge_nine_fifths
  have hUp := eulerian_half_one_fock_gram_trace_lt_eleven_tenths
  have hgap :
      (∑' n : ℕ,
        Real.exp (-(1 / 10 : ℝ) *
          ((n : ℝ) * ((n : ℝ) + 2 * (1 / 2 : ℝ))))) ≠
        KummerCoefficients.kummerSeries (1 / 2) (1 / 4) :=
    ne_of_gt (lt_of_lt_of_le (lt_trans hUp (by norm_num)) hLow)
  exact no_heat_fockGram_basis_intertwiner_of_trace_gap
    (1 / 2) 1 (1 / 10) (by norm_num) (by norm_num) (by norm_num)
    (by simpa only [mul_one] using hgap)

#print axioms GegenbauerFock.Ultraspherical.no_heat_fockGram_basis_intertwiner_of_trace_gap
#print axioms GegenbauerFock.Ultraspherical.eulerian_half_one_fock_gram_trace_lt_eleven_tenths
#print axioms GegenbauerFock.Ultraspherical.legendre_heat_trace_one_tenth_ge_nine_fifths
#print axioms GegenbauerFock.Ultraspherical.no_legendre_heat_one_tenth_to_fock_gram_one_basis_intertwiner

end GegenbauerFock.Ultraspherical
