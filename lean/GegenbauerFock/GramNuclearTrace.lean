import GegenbauerFock.GramIntegralComplete
import GegenbauerFock.GramKernelSeries
import GegenbauerFock.RowEnergyExpIntegral
import GegenbauerFock.UltrasphericalKummerBridge

/-!
# V007: operator-norm summable nuclear Gram decomposition

A trace-class positive Gram operator can be presented as an absolutely
operator-norm-summable series of positive rank-one terms. The row
functionals are the genuine ultraspherical Fourier moments. This
module certifies absolute convergence of the rank-one operators,
not just convergence after applying to a fixed L² vector.

Note: identifying this constructive nuclear presentation with a
separately bundled Schatten S₁ API is a further formal bridge.
-/

open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Each rank-one positive Gram summand of the genuine operator. -/
noncomputable def gramNuclearTerm
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (n : ℕ) :
    Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
      Lp ℂ 2 (Ultraspherical.measure lam) := by
  letI : IsProbabilityMeasure (Ultraspherical.measure lam) :=
    Ultraspherical.probability lam hlam
  let r := WeightedMoments.coefficient
    (Ultraspherical.measure lam) (ae_abs_le_one lam) alpha n
  exact r.adjoint.comp r

/-- Operator-norm bound for each concrete positive rank-one term. -/
theorem gramNuclearTerm_norm_le
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (n : ℕ) :
    ‖gramNuclearTerm lam alpha hlam ha n‖ ≤
      WeightedMoments.squareWeight alpha n := by
  letI : IsProbabilityMeasure (Ultraspherical.measure lam) :=
    Ultraspherical.probability lam hlam
  let r := WeightedMoments.coefficient
    (Ultraspherical.measure lam) (ae_abs_le_one lam) alpha n
  change ‖r.adjoint.comp r‖ ≤ _
  calc
    ‖r.adjoint.comp r‖ = ‖r‖ ^ 2 := by
      rw [ContinuousLinearMap.norm_adjoint_comp_self]
      ring
    _ ≤ WeightedMoments.squareWeight alpha n :=
      WeightedMoments.coefficient_norm_sq_le
        (Ultraspherical.measure lam) (ae_abs_le_one lam) alpha ha n

/-- The *actual* infinite family of positive rank-one Gram pieces
is absolutely summable in the full Banach operator norm. -/
theorem gramNuclearTerm_summable
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    Summable (gramNuclearTerm lam alpha hlam ha) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le
    (fun n => norm_nonneg _)
    (gramNuclearTerm_norm_le lam alpha hlam ha)
    (WeightedMoments.squareWeight_summable alpha)

/-- Exact identity of the Gram map with the infinite positive
rank-one sum, now as an equality of *bounded operators*, not merely
as separate convergent vectors. -/
theorem gram_eq_nuclear_tsum
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    gram lam alpha hlam ha =
      ∑' n : ℕ, gramNuclearTerm lam alpha hlam ha n := by
  apply ContinuousLinearMap.ext
  intro f
  rw [gram_eq_tsum_rows lam alpha hlam ha f]
  have hs := gramNuclearTerm_summable lam alpha hlam ha
  have heval :
      (∑' n : ℕ, gramNuclearTerm lam alpha hlam ha n) f =
        ∑' n : ℕ, gramNuclearTerm lam alpha hlam ha n f := by
    exact (ContinuousLinearMap.apply ℂ
      (Lp ℂ 2 (Ultraspherical.measure lam)) f).map_tsum hs
  rw [heval]
  apply tsum_congr
  intro n
  rfl

#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramNuclearTerm_norm_le
#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramNuclearTerm_summable
#print axioms GegenbauerFock.GeneralUltrasphericalFock.gram_eq_nuclear_tsum

/-- Rank-one positivity makes the operator norm of the n-th Gram
summand equal to the exact squared norm of the n-th Fock moment row. -/
theorem gramNuclearTerm_norm_eq_row_sq
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (n : ℕ) :
    ‖gramNuclearTerm lam alpha hlam ha n‖ =
      ‖SummableRowsCompact.row (C lam alpha hlam ha) n‖ ^ 2 := by
  letI : IsProbabilityMeasure (Ultraspherical.measure lam) :=
    Ultraspherical.probability lam hlam
  let r := WeightedMoments.coefficient
    (Ultraspherical.measure lam) (ae_abs_le_one lam) alpha n
  change ‖r.adjoint.comp r‖ = _
  rw [C_row_eq lam alpha hlam ha n]
  change ‖r.adjoint.comp r‖ = ‖r‖ ^ 2
  rw [ContinuousLinearMap.norm_adjoint_comp_self]
  ring

/-- The mass of the positive nuclear rank-one presentation is
exactly the verified squared canonical Hilbert-Schmidt row energy. -/
theorem gramNuclearMass_eq_rowEnergy
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (∑' n : ℕ, ‖gramNuclearTerm lam alpha hlam ha n‖) =
      rowEnergy lam alpha hlam ha := by
  unfold rowEnergy
  apply tsum_congr
  intro n
  exact gramNuclearTerm_norm_eq_row_sq lam alpha hlam ha n

/-- Exact exponential integral for the nuclear Gram mass. This is
the scalar trace of the positive rank-one presentation, independent
trace-class ideal equivalence still being formalized. -/
theorem gramNuclearMass_eq_exp_integral
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (∑' n : ℕ, ‖gramNuclearTerm lam alpha hlam ha n‖) =
      ∫ u : ℝ, Real.exp (u ^ 2 / (4 * alpha))
        ∂(Ultraspherical.measure lam) := by
  rw [gramNuclearMass_eq_rowEnergy]
  exact rowEnergy_eq_exp_integral lam alpha hlam ha

#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramNuclearTerm_norm_eq_row_sq
#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramNuclearMass_eq_rowEnergy
#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramNuclearMass_eq_exp_integral


/-- Unconditional Kummer closed form for the absolute rank-one
nuclear mass of the concrete positive Gram operator C†C. The
summands are actual norm-one-rank Hilbert operators, not merely
formal coefficients. -/
theorem gramNuclearMass_eq_kummerSeries
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (∑' n : ℕ, ‖gramNuclearTerm lam alpha hlam ha n‖) =
      KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) := by
  rw [gramNuclearMass_eq_rowEnergy]
  exact rowEnergy_eq_kummerSeries lam alpha hlam ha

#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramNuclearMass_eq_kummerSeries

/-- The nuclear mass of the concrete positive Gram presentation has
the exact unregularized Mathlib-Pochhammer Kummer series, with
physical parameter t = 1/(4α). -/
theorem gramNuclearMass_eq_pochhammerSeries
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (∑' n : ℕ, ‖gramNuclearTerm lam alpha hlam ha n‖) =
      ∑' n : ℕ,
        ((ascPochhammer ℝ n).eval (1 / 2) /
          (ascPochhammer ℝ n).eval (lam + 1)) *
          ((1 / (4 * alpha)) ^ n / (Nat.factorial n : ℝ)) := by
  rw [gramNuclearMass_eq_rowEnergy]
  exact rowEnergy_eq_pochhammerSeries lam alpha hlam ha

#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramNuclearMass_eq_pochhammerSeries

/-- The actual positive Gram operator has a basis-independent
Hilbert trace in the following concrete sense: for every complete
complex Hilbert basis of ultraspherical L², the sum of its real
diagonal matrix elements is the same unregularized Kummer value.
This proves the basis-sum trace identity, without postulating a
separate Schatten S₁ norm object. -/
theorem gram_sourceBasis_trace_eq_kummer
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    {ι : Type*}
    (b : HilbertBasis ι ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) :
    (∑' i : ι,
        RCLike.re (inner ℂ (gram lam alpha hlam ha (b i)) (b i))) =
      KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) := by
  calc
    (∑' i : ι,
        RCLike.re (inner ℂ (gram lam alpha hlam ha (b i)) (b i))) =
        ∑' i : ι, ‖C lam alpha hlam ha (b i)‖ ^ 2 := by
          apply tsum_congr
          intro i
          exact (HilbertGram.gram_norm_sq
            (C lam alpha hlam ha) (b i)).symm
    _ = KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) :=
      C_sourceBasis_HSEnergy_eq_kummer lam alpha hlam ha b

#print axioms GegenbauerFock.GeneralUltrasphericalFock.gram_sourceBasis_trace_eq_kummer

/-- A single basis-independent equality relating the concrete Hilbert--Schmidt
source-basis energy, the positive Gram diagonal trace, the nuclear
rank-one norm mass, and the exactly normalized Kummer/Pochhammer
hypergeometric sum.  No Schatten-ideal norm API is assumed. -/
theorem C_HSEnergy_GramTrace_NuclearMass_eq_pochhammer
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    {ι : Type*}
    (b : HilbertBasis ι ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) :
    (∑' i : ι, ‖C lam alpha hlam ha (b i)‖ ^ 2) =
        (∑' i : ι,
          RCLike.re (inner ℂ (gram lam alpha hlam ha (b i)) (b i))) ∧
    (∑' i : ι, ‖C lam alpha hlam ha (b i)‖ ^ 2) =
        (∑' n : ℕ, ‖gramNuclearTerm lam alpha hlam ha n‖) ∧
    (∑' i : ι, ‖C lam alpha hlam ha (b i)‖ ^ 2) =
        ∑' n : ℕ,
          ((ascPochhammer ℝ n).eval (1 / 2) /
            (ascPochhammer ℝ n).eval (lam + 1)) *
            ((1 / (4 * alpha)) ^ n / (Nat.factorial n : ℝ)) := by
  have hHS := C_sourceBasis_HSEnergy_eq_kummer lam alpha hlam ha b
  have htr := gram_sourceBasis_trace_eq_kummer lam alpha hlam ha b
  have hmass := gramNuclearMass_eq_kummerSeries lam alpha hlam ha
  have hp := gramNuclearMass_eq_pochhammerSeries lam alpha hlam ha
  constructor
  · exact hHS.trans htr.symm
  constructor
  · exact hHS.trans hmass.symm
  · exact (hHS.trans hmass.symm).trans hp

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_HSEnergy_GramTrace_NuclearMass_eq_pochhammer

end GegenbauerFock.GeneralUltrasphericalFock


/-!
## Basis-defined Hilbert--Schmidt class and left operator ideal

Mathlib at the pinned version has the Hilbert-space, Riesz, Parseval and
summability APIs needed to construct a basis-formulated Schatten-S₂
membership predicate directly. This predicate demands genuine summability
for *every* complete source Hilbert basis; it is not merely a raw `tsum`.
Identification with a bundled Schatten ideal type/norm is a distinct task.
-/

namespace GegenbauerFock.HilbertSchmidtBasis

variable {E F G : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- Abstract basis-independent Hilbert--Schmidt summability criterion
for a bounded operator between complex Hilbert spaces. -/
def IsHS (T : E →L[ℂ] F) : Prop :=
  ∀ {ι : Type*} (b : HilbertBasis ι ℂ E),
    Summable (fun i : ι => ‖T (b i)‖ ^ 2)

/-- The usual square-root-of-energy expression for a specified complete
source basis, for an operator whose energy series is summable. -/
noncomputable def basisNorm (T : E →L[ℂ] F)
    {ι : Type*} (b : HilbertBasis ι ℂ E) : ℝ :=
  Real.sqrt (∑' i : ι, ‖T (b i)‖ ^ 2)

/-- General target-side ideal theorem: Hilbert--Schmidt operators remain
Hilbert--Schmidt after composition on the left by any bounded operator,
even if the output Hilbert space changes. -/
theorem isHS_comp_left (T : E →L[ℂ] F)
    (hT : IsHS T) (S : F →L[ℂ] G) :
    IsHS (S.comp T) := by
  intro ι b
  apply Summable.of_nonneg_of_le
  · intro i
    exact sq_nonneg _
  · intro i
    calc
      ‖(S.comp T) (b i)‖ ^ 2 = ‖S (T (b i))‖ ^ 2 := rfl
      _ ≤ (‖S‖ * ‖T (b i)‖) ^ 2 := by
        gcongr
        exact ContinuousLinearMap.le_opNorm S (T (b i))
      _ = ‖S‖ ^ 2 * ‖T (b i)‖ ^ 2 := by ring
  · exact (hT b).mul_left (‖S‖ ^ 2)

#print axioms GegenbauerFock.HilbertSchmidtBasis.isHS_comp_left

end GegenbauerFock.HilbertSchmidtBasis

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The concrete normalized Beta-pushforward ultraspherical--Fock
operator satisfies the genuinely summable abstract Hilbert--Schmidt
basis criterion for ALL source Hilbert bases. -/
theorem C_isHilbertSchmidt
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    HilbertSchmidtBasis.IsHS (C lam alpha hlam ha) := by
  intro ι b
  letI : IsProbabilityMeasure (Ultraspherical.measure lam) :=
    Ultraspherical.probability lam hlam
  change Summable (fun i : ι =>
    ‖ConcreteFock.operator (Ultraspherical.measure lam)
      (ae_abs_le_one lam) alpha ha (b i)‖ ^ 2)
  exact FockEnergy.concrete_sourceBasis_energy_summable
    (Ultraspherical.measure lam) (ae_abs_le_one lam) alpha ha b

/-- The bona fide basis-defined Hilbert--Schmidt norm of the actual
Gegenbauer--Fock operator is exactly sqrt of the verified Kummer value,
for any complete source Hilbert basis. -/
theorem C_basisHSNorm_eq_sqrt_kummer
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    {ι : Type*} (b : HilbertBasis ι ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) :
    HilbertSchmidtBasis.basisNorm (C lam alpha hlam ha) b =
      Real.sqrt (KummerCoefficients.kummerSeries lam (1 / (4 * alpha))) := by
  unfold HilbertSchmidtBasis.basisNorm
  rw [C_sourceBasis_HSEnergy_eq_kummer lam alpha hlam ha b]

/-- Explicit independence of arbitrary choices of complete Hilbert bases
for the sqrt-Kummer Hilbert--Schmidt energy norm. -/
theorem C_basisHSNorm_basis_independent
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    {ι κ : Type*}
    (b : HilbertBasis ι ℂ (Lp ℂ 2 (Ultraspherical.measure lam)))
    (c : HilbertBasis κ ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) :
    HilbertSchmidtBasis.basisNorm (C lam alpha hlam ha) b =
      HilbertSchmidtBasis.basisNorm (C lam alpha hlam ha) c := by
  rw [C_basisHSNorm_eq_sqrt_kummer lam alpha hlam ha b,
    C_basisHSNorm_eq_sqrt_kummer lam alpha hlam ha c]

/-- Every bounded postprocessing of the actual Gegenbauer--Fock
coefficient map remains Hilbert--Schmidt, a genuine left-ideal theorem. -/
theorem C_comp_left_isHilbertSchmidt
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (S : InfiniteAnalysis.FockCoefficients →L[ℂ]
      InfiniteAnalysis.FockCoefficients) :
    HilbertSchmidtBasis.IsHS (S.comp (C lam alpha hlam ha)) :=
  HilbertSchmidtBasis.isHS_comp_left
    (C lam alpha hlam ha) (C_isHilbertSchmidt lam alpha hlam ha) S

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_isHilbertSchmidt
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_basisHSNorm_eq_sqrt_kummer
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_basisHSNorm_basis_independent
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_comp_left_isHilbertSchmidt

end GegenbauerFock.GeneralUltrasphericalFock
