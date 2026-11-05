import GegenbauerFock.RealNuclearTwoOrthonormalFiniteTraceDual
import GegenbauerFock.UltrasphericalSturmLiouvilleResolventRealNuclearDualLower

/-!
# V007 — universal mixed real nuclear trace duality

Two independent orthonormal families, possibly both incomplete,
yield a continuous finite-rank mixed trace functional. The sharp
coefficient-one estimate holds against EVERY admissible real nuclear
rank-one representation of an arbitrary bounded operator.

In contrast to a unitary-polar SVD argument, this does not require
equal kernel and cokernel defects. The result is the generic lower
bound needed to handle proper partial isometries and unilateral
nuclear shifts.

The underlying finite rank-one inequality is imported separately.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A continuous mixed finite trace on bounded real Hilbert
operators, evaluated on independent orthonormal families. -/
noncomputable def realTwoOrthonormalFiniteTraceCLM
    (b c : ℕ → H) (N : ℕ) :
    (H →L[ℝ] H) →L[ℝ] ℝ :=
  ∑ n ∈ Finset.range N,
    (innerSL ℝ (c n)).comp
      (ContinuousLinearMap.apply ℝ H (b n))

theorem realTwoOrthonormalFiniteTraceCLM_apply
    (b c : ℕ → H) (N : ℕ) (T : H →L[ℝ] H) :
    realTwoOrthonormalFiniteTraceCLM b c N T =
      ∑ n ∈ Finset.range N, inner ℝ (c n) (T (b n)) := by
  simp only [realTwoOrthonormalFiniteTraceCLM,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply]
  rfl

/-- The mixed finite trace is bounded by EVERY admissible nuclear
representation cost, with sharp universal coefficient one.
Neither orthonormal family need span the whole Hilbert space. -/
theorem realTwoOrthonormalFiniteTrace_abs_le_nuclearCost
    (b c : ℕ → H) (hb : Orthonormal ℝ b)
    (hco : Orthonormal ℝ c) (N : ℕ)
    (T : H →L[ℝ] H) {cost : ℝ}
    (hcost : cost ∈ RealNuclearCosts T) :
    |∑ n ∈ Finset.range N, inner ℝ (c n) (T (b n))| ≤ cost := by
  rcases hcost with ⟨u, v, β, hs, hT, rfl⟩
  let Φ : (H →L[ℝ] H) →L[ℝ] ℝ :=
    realTwoOrthonormalFiniteTraceCLM b c N
  let A : ℕ → (H →L[ℝ] H) :=
    fun k => β k • rankOne ℝ (u k) (v k)
  have hA : Summable A := by
    apply Summable.of_norm
    convert hs using 1
    funext k
    rw [norm_smul, norm_rankOne]
    ring
  have hterm (k : ℕ) :
      ‖Φ (A k)‖ ≤ ‖β k‖ * ‖u k‖ * ‖v k‖ := by
    have htrace :
        |Φ (rankOne ℝ (u k) (v k))| ≤ ‖u k‖ * ‖v k‖ := by
      rw [realTwoOrthonormalFiniteTraceCLM_apply]
      exact realTwoOrthonormalFiniteTrace_rankOne_abs_le
        b c hb hco N (u k) (v k)
    have hscal : Φ (A k) =
        β k • Φ (rankOne ℝ (u k) (v k)) := by
      change Φ (β k • rankOne ℝ (u k) (v k)) = _
      rw [map_smul]
    rw [hscal, norm_smul, Real.norm_eq_abs]
    calc
      ‖β k‖ * |Φ (rankOne ℝ (u k) (v k))| ≤
          ‖β k‖ * (‖u k‖ * ‖v k‖) :=
        mul_le_mul_of_nonneg_left htrace (norm_nonneg _)
      _ = ‖β k‖ * ‖u k‖ * ‖v k‖ := by ring
  have hΦnorm : Summable (fun k : ℕ => ‖Φ (A k)‖) := by
    apply Summable.of_nonneg_of_le
    · intro k
      exact norm_nonneg _
    · exact hterm
    · exact hs
  have hcommute : Φ T = ∑' k : ℕ, Φ (A k) := by
    rw [hT]
    exact Φ.map_tsum hA
  have hsumBound :
      (∑' k : ℕ, ‖Φ (A k)‖) ≤
        ∑' k : ℕ, ‖β k‖ * ‖u k‖ * ‖v k‖ :=
    hΦnorm.tsum_le_tsum hterm hs
  calc
    |∑ n ∈ Finset.range N, inner ℝ (c n) (T (b n))| =
        ‖Φ T‖ := by
          rw [realTwoOrthonormalFiniteTraceCLM_apply]
          exact (Real.norm_eq_abs _).symm
    _ = ‖∑' k : ℕ, Φ (A k)‖ := by rw [hcommute]
    _ ≤ ∑' k : ℕ, ‖Φ (A k)‖ :=
      norm_tsum_le_tsum_norm hΦnorm
    _ ≤ ∑' k : ℕ, ‖β k‖ * ‖u k‖ * ‖v k‖ :=
      hsumBound

#print axioms GegenbauerFock.Ultraspherical.realTwoOrthonormalFiniteTraceCLM_apply
#print axioms GegenbauerFock.Ultraspherical.realTwoOrthonormalFiniteTrace_abs_le_nuclearCost

end GegenbauerFock.Ultraspherical
