import GegenbauerFock.RealNuclearTwoOrthonormalAllCostsDual
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# V007 — arbitrary-index real singular nuclear duality

A compact selfadjoint Gram can have a finite or countable positive
support and a possibly large zero eigenspace. Thus a convenient
positive-support index is NOT necessarily all of ℕ.

We generalize the already certified sharp mixed finite-trace duality
from Finset.range N to arbitrary finite subsets of an arbitrary type ι.
Consequently, for any real nuclear T, the nonnegative amplitudes of
any orthonormal partial singular family indexed by ι are summable and
their total mass is bounded by the universal real projective infimum.

This is independent of completeness, a global unitary polar factor,
and equality of source and output defects.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]
variable {ι : Type*}

/-- A finite mixed Fourier transfer between two arbitrary-index
orthonormal families is contractive, even if both are incomplete. -/
theorem realGeneralIndexFiniteTransfer_norm_le
    (b c : ι → H) (hb : Orthonormal ℝ b)
    (hc : Orthonormal ℝ c) (s : Finset ι) (v : H) :
    ‖∑ i ∈ s, (inner ℝ (b i) v) • c i‖ ≤ ‖v‖ := by
  classical
  let q : H := ∑ i ∈ s, (inner ℝ (b i) v) • c i
  have hqnorm : ‖q‖ ^ 2 =
      ∑ i ∈ s, (inner ℝ (b i) v) ^ 2 := by
    have hh := hc.inner_sum
      (fun i => inner ℝ (b i) v)
      (fun i => inner ℝ (b i) v) s
    change inner ℝ q q =
      ∑ i ∈ s, (inner ℝ (b i) v) * (inner ℝ (b i) v) at hh
    rw [real_inner_self_eq_norm_sq] at hh
    simpa [pow_two] using hh
  have hbessel :
      ∑ i ∈ s, (inner ℝ (b i) v) ^ 2 ≤ ‖v‖ ^ 2 := by
    have h := hb.sum_inner_products_le (s := s) v
    convert h using 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [Real.norm_eq_abs, sq_abs]
  have hqpos : 0 ≤ ‖q‖ := norm_nonneg _
  have hvpos : 0 ≤ ‖v‖ := norm_nonneg _
  change ‖q‖ ≤ ‖v‖
  nlinarith

/-- Finite mixed trace of a real rank-one map, for any finite index
set and with no completeness assumption. -/
theorem realGeneralIndexFiniteTrace_rankOne_eq
    (b c : ι → H) (s : Finset ι) (u v : H) :
    (∑ i ∈ s,
      inner ℝ (c i) (rankOne ℝ u v (b i))) =
      inner ℝ
        (∑ i ∈ s, (inner ℝ (b i) v) • c i) u := by
  classical
  calc
    (∑ i ∈ s,
       inner ℝ (c i) (rankOne ℝ u v (b i))) =
      ∑ i ∈ s,
        inner ℝ ((inner ℝ (b i) v) • c i) u := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [InnerProductSpace.rankOne_apply,
        real_inner_smul_right, real_inner_smul_left]
      rw [real_inner_comm v (b i)]
    _ = inner ℝ
          (∑ i ∈ s, (inner ℝ (b i) v) • c i) u := by
      rw [sum_inner]

/-- Sharp constant-one finite mixed trace bound for ANY index type. -/
theorem realGeneralIndexFiniteTrace_rankOne_abs_le
    (b c : ι → H) (hb : Orthonormal ℝ b)
    (hc : Orthonormal ℝ c) (s : Finset ι) (u v : H) :
    |∑ i ∈ s,
      inner ℝ (c i) (rankOne ℝ u v (b i))| ≤
      ‖u‖ * ‖v‖ := by
  rw [realGeneralIndexFiniteTrace_rankOne_eq b c s u v]
  have hCS :
      |inner ℝ
        (∑ i ∈ s, (inner ℝ (b i) v) • c i) u| ≤
        ‖∑ i ∈ s, (inner ℝ (b i) v) • c i‖ * ‖u‖ := by
    simpa only [Real.norm_eq_abs] using
      norm_inner_le_norm (𝕜 := ℝ)
        (∑ i ∈ s, (inner ℝ (b i) v) • c i) u
  calc
    _ ≤ ‖∑ i ∈ s, (inner ℝ (b i) v) • c i‖ * ‖u‖ := hCS
    _ ≤ ‖v‖ * ‖u‖ := by
      gcongr
      exact realGeneralIndexFiniteTransfer_norm_le b c hb hc s v
    _ = ‖u‖ * ‖v‖ := mul_comm _ _

/-- The actual finite mixed trace as a continuous real-linear
functional on bounded endomorphisms. -/
noncomputable def realGeneralIndexFiniteTraceCLM
    (b c : ι → H) (s : Finset ι) :
    (H →L[ℝ] H) →L[ℝ] ℝ :=
  ∑ i ∈ s,
    (innerSL ℝ (c i)).comp
      (ContinuousLinearMap.apply ℝ H (b i))

theorem realGeneralIndexFiniteTraceCLM_apply
    (b c : ι → H) (s : Finset ι) (T : H →L[ℝ] H) :
    realGeneralIndexFiniteTraceCLM b c s T =
      ∑ i ∈ s, inner ℝ (c i) (T (b i)) := by
  simp only [realGeneralIndexFiniteTraceCLM,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply]
  rfl

/-- Every finite partial singular trace is bounded by the cost
of EACH nuclear rank-one presentation, for any index type. -/
theorem realGeneralIndexFiniteTrace_abs_le_nuclearCost
    (b c : ι → H) (hb : Orthonormal ℝ b)
    (hc : Orthonormal ℝ c) (s : Finset ι)
    (T : H →L[ℝ] H) {cost : ℝ}
    (hcost : cost ∈ RealNuclearCosts T) :
    |∑ i ∈ s, inner ℝ (c i) (T (b i))| ≤ cost := by
  classical
  rcases hcost with ⟨u, v, beta, hs, hT, rfl⟩
  let Phi : (H →L[ℝ] H) →L[ℝ] ℝ :=
    realGeneralIndexFiniteTraceCLM b c s
  let A : ℕ → (H →L[ℝ] H) :=
    fun k => beta k • rankOne ℝ (u k) (v k)
  have hA : Summable A := by
    apply Summable.of_norm
    convert hs using 1
    funext k
    rw [norm_smul, norm_rankOne]
    ring
  have hterm (k : ℕ) :
      ‖Phi (A k)‖ ≤ ‖beta k‖ * ‖u k‖ * ‖v k‖ := by
    have htrace :
        |Phi (rankOne ℝ (u k) (v k))| ≤ ‖u k‖ * ‖v k‖ := by
      rw [realGeneralIndexFiniteTraceCLM_apply]
      exact realGeneralIndexFiniteTrace_rankOne_abs_le
        b c hb hc s (u k) (v k)
    have hscal : Phi (A k) =
        beta k • Phi (rankOne ℝ (u k) (v k)) := by
      change Phi (beta k • rankOne ℝ (u k) (v k)) = _
      rw [map_smul]
    rw [hscal, norm_smul, Real.norm_eq_abs]
    calc
      ‖beta k‖ * |Phi (rankOne ℝ (u k) (v k))| ≤
          ‖beta k‖ * (‖u k‖ * ‖v k‖) :=
        mul_le_mul_of_nonneg_left htrace (norm_nonneg _)
      _ = ‖beta k‖ * ‖u k‖ * ‖v k‖ := by ring
  have hPhiNorm :
      Summable (fun k : ℕ => ‖Phi (A k)‖) := by
    apply Summable.of_nonneg_of_le
    · intro k
      exact norm_nonneg _
    · exact hterm
    · exact hs
  have hcommute : Phi T = ∑' k : ℕ, Phi (A k) := by
    rw [hT]
    exact Phi.map_tsum hA
  have hsumBound :
      (∑' k : ℕ, ‖Phi (A k)‖) ≤
        ∑' k : ℕ, ‖beta k‖ * ‖u k‖ * ‖v k‖ :=
    hPhiNorm.tsum_le_tsum hterm hs
  calc
    |∑ i ∈ s, inner ℝ (c i) (T (b i))| =
        ‖Phi T‖ := by
          rw [realGeneralIndexFiniteTraceCLM_apply]
          exact (Real.norm_eq_abs _).symm
    _ = ‖∑' k : ℕ, Phi (A k)‖ := by rw [hcommute]
    _ ≤ ∑' k : ℕ, ‖Phi (A k)‖ :=
      norm_tsum_le_tsum_norm hPhiNorm
    _ ≤ ∑' k : ℕ, ‖beta k‖ * ‖u k‖ * ‖v k‖ :=
      hsumBound

/-- Uniform finite mass bound on a partial singular family. -/
theorem realGeneralIndexSingularFamily_sum_le_cost
    (T : H →L[ℝ] H) (b c : ι → H)
    (hb : Orthonormal ℝ b) (hc : Orthonormal ℝ c)
    (sigma : ι → ℝ) (hpos : ∀ i, 0 ≤ sigma i)
    (hpair : ∀ i, T (b i) = sigma i • c i)
    (s : Finset ι) {cost : ℝ} (hcost : cost ∈ RealNuclearCosts T) :
    (∑ i ∈ s, sigma i) ≤ cost := by
  classical
  have hdiag (i : ι) :
      inner ℝ (c i) (T (b i)) = sigma i := by
    rw [hpair i, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hc.norm_eq_one i]
    ring
  have htrace :=
    realGeneralIndexFiniteTrace_abs_le_nuclearCost
      b c hb hc s T hcost
  have hsum :
      (∑ i ∈ s, inner ℝ (c i) (T (b i))) =
        (∑ i ∈ s, sigma i) :=
    Finset.sum_congr rfl (fun i _ => hdiag i)
  rw [hsum] at htrace
  have hp : 0 ≤ ∑ i ∈ s, sigma i :=
    Finset.sum_nonneg (fun i _ => hpos i)
  simpa only [abs_of_nonneg hp] using htrace

/-- Arbitrary-index singular amplitudes are summable for ANY real
nuclear operator, without a countable choice of active-mode indices. -/
theorem HasRealNuclearRankOneSeries.generalIndexSingular_summable
    {T : H →L[ℝ] H} (hT : HasRealNuclearRankOneSeries T)
    (b c : ι → H) (hb : Orthonormal ℝ b)
    (hc : Orthonormal ℝ c)
    (sigma : ι → ℝ) (hpos : ∀ i, 0 ≤ sigma i)
    (hpair : ∀ i, T (b i) = sigma i • c i) :
    Summable sigma := by
  classical
  rcases hT with ⟨u, v, beta, hs, hseries⟩
  have hcost :
      (∑' n : ℕ, ‖beta n‖ * ‖u n‖ * ‖v n‖) ∈
        RealNuclearCosts T :=
    ⟨u, v, beta, hs, hseries, rfl⟩
  apply summable_of_sum_le (fun i => hpos i)
  intro s
  exact realGeneralIndexSingularFamily_sum_le_cost
    T b c hb hc sigma hpos hpair s hcost

/-- The sum of arbitrary-index singular amplitudes is below the
universal projective infimum over all nuclear representations. -/
theorem HasRealNuclearRankOneSeries.generalIndexSingular_tsum_le_infimum
    {T : H →L[ℝ] H} (hT : HasRealNuclearRankOneSeries T)
    (b c : ι → H) (hb : Orthonormal ℝ b)
    (hc : Orthonormal ℝ c)
    (sigma : ι → ℝ) (hpos : ∀ i, 0 ≤ sigma i)
    (hpair : ∀ i, T (b i) = sigma i • c i) :
    (∑' i : ι, sigma i) ≤ realNuclearInfimum T := by
  classical
  have hs : Summable sigma :=
    hT.generalIndexSingular_summable b c hb hc sigma hpos hpair
  obtain ⟨u, v, beta, hcostsum, hseries⟩ := hT
  have hnonempty : (RealNuclearCosts T).Nonempty :=
    ⟨∑' n : ℕ, ‖beta n‖ * ‖u n‖ * ‖v n‖,
      ⟨u, v, beta, hcostsum, hseries, rfl⟩⟩
  change (∑' i : ι, sigma i) ≤ sInf (RealNuclearCosts T)
  apply le_csInf hnonempty
  intro cost hcost
  exact hs.tsum_le_of_sum_le
    (fun s => realGeneralIndexSingularFamily_sum_le_cost
      T b c hb hc sigma hpos hpair s hcost)

#print axioms GegenbauerFock.Ultraspherical.realGeneralIndexFiniteTransfer_norm_le
#print axioms GegenbauerFock.Ultraspherical.realGeneralIndexFiniteTrace_rankOne_eq
#print axioms GegenbauerFock.Ultraspherical.realGeneralIndexFiniteTrace_rankOne_abs_le
#print axioms GegenbauerFock.Ultraspherical.realGeneralIndexFiniteTraceCLM_apply
#print axioms GegenbauerFock.Ultraspherical.realGeneralIndexFiniteTrace_abs_le_nuclearCost
#print axioms GegenbauerFock.Ultraspherical.realGeneralIndexSingularFamily_sum_le_cost
#print axioms GegenbauerFock.Ultraspherical.HasRealNuclearRankOneSeries.generalIndexSingular_summable
#print axioms GegenbauerFock.Ultraspherical.HasRealNuclearRankOneSeries.generalIndexSingular_tsum_le_infimum

end GegenbauerFock.Ultraspherical
