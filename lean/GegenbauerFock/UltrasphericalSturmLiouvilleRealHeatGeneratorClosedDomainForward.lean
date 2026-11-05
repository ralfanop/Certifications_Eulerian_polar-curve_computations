import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatGeneratorCoordinateSlope
import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatClosedGraphErrorBound
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# V007 — canonical closed Sturm graph lies in the genuine heat generator graph

Fix lambda>0. Let A be the *canonical graph closure of the actual
polynomial ultraspherical differential Sturm operator*, H_s the
norm-contractive C0 semigroup constructed from genuine L2 Yosida limits,
and b its explicitly complete normalized Gegenbauer Hilbert basis.

For every x in Dom(A), the true Hilbert-space right difference quotient
s^{-1}(H_s x - x) tends strongly to A x. This is NOT merely a statement
on eigenmodes or on finite linear combinations.

The proof applies Tannery's dominated convergence theorem to the squared
actual Hilbert-basis Fourier coefficients of the difference-quotient error.
The certified scalar inequality bounds each nonnegative squared coefficient
uniformly in s>0 by the corresponding square coefficient of A x, whose
sum is finite by Parseval.

The converse inclusion (any strong right derivative implies canonical
closed Sturm domain membership) has its own independently checkable module.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory Filter
open scoped Topology

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- Strong generator equality on every vector of the actual canonical
closed Gegenbauer Sturm domain, proved by dominated Fourier sums. -/
theorem sturmRealHeatLimit_closed_sturm_right_derivative
    (lam : ℝ) (hlam : 0 < lam)
    (x : (sturmRealPartialOperator lam hlam).closure.domain) :
    Tendsto
      (fun s : ℝ => s⁻¹ •
        (sturmRealHeatLimitNonnegativeExtended lam hlam s
          (x : SturmH lam) - (x : SturmH lam)))
      (𝓝[>] (0 : ℝ))
      (𝓝 ((sturmRealPartialOperator lam hlam).closure x)) := by
  let b := sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam
  let A := (sturmRealPartialOperator lam hlam).closure
  let v : SturmH lam := (x : SturmH lam)
  let err : ℝ → SturmH lam :=
    fun s => s⁻¹ • (sturmRealHeatLimitNonnegativeExtended lam hlam s v - v) - A x
  have hsquared (z : SturmH lam) :
      Summable (fun n : ℕ => ((b.repr z) n) ^ 2) := by
    have hsum := b.summable_inner_mul_inner z z
    have hterm (n : ℕ) :
        inner ℝ z (b n) * inner ℝ (b n) z =
          ((b.repr z) n) ^ 2 := by
      rw [HilbertBasis.repr_apply_apply, real_inner_comm z (b n)]
      ring
    exact hsum.congr hterm
  have hclosed (n : ℕ) :
      (b.repr (A x)) n =
        (-((n : ℝ) * ((n : ℝ) + 2 * lam))) * (b.repr v) n := by
    convert (sturmRealClosed_eq_exact_monicGegenbauer_spectral_realization
      lam hlam).2 x n using 1 <;> ring
  have hpoint (n : ℕ) :
      Tendsto (fun s : ℝ => ((b.repr (err s)) n) ^ 2)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have hcoord := sturmRealHeatLimit_fullL2_coordinate_right_slope
      lam hlam v n
    have hsub := hcoord.sub
      (tendsto_const_nhds (x := (b.repr (A x)) n))
    have herror (s : ℝ) :
        (b.repr (err s)) n =
          (b.repr (s⁻¹ •
            (sturmRealHeatLimitNonnegativeExtended lam hlam s v - v))) n -
          (b.repr (A x)) n := by
      dsimp [err]
      rw [map_sub]
      simp only [lp.coeFn_sub, Pi.sub_apply]
    have hfun :
        (fun s : ℝ => (b.repr (err s)) n) =
        (fun s : ℝ =>
          (b.repr (s⁻¹ •
            (sturmRealHeatLimitNonnegativeExtended lam hlam s v - v))) n -
          (b.repr (A x)) n) := by
      funext s
      exact herror s
    have hzero : Tendsto (fun s : ℝ => (b.repr (err s)) n)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
      change Tendsto
        (fun s : ℝ =>
          (b.repr (s⁻¹ •
            (sturmRealHeatLimitNonnegativeExtended lam hlam s v - v))) n -
          (b.repr (A x)) n)
        (𝓝[>] (0 : ℝ))
        (𝓝 ((-((n : ℝ) * ((n : ℝ) + 2 * lam))) *
          (b.repr v) n - (b.repr (A x)) n)) at hsub
      rw [hfun]
      simpa [b, hclosed n] using hsub
    simpa using hzero.pow 2
  have hbound (s : ℝ) (hs : 0 < s) (n : ℕ) :
      ((b.repr (err s)) n) ^ 2 ≤
        ((b.repr (A x)) n) ^ 2 := by
    let w : ℝ := (n : ℝ) * ((n : ℝ) + 2 * lam)
    let c : ℝ := (b.repr v) n
    have hw : 0 ≤ w := by dsimp [w]; positivity
    obtain ⟨hq0, hqw⟩ :=
      sturmRealHeat_scalar_slope_error_bounded w s hw hs
    have hsq :
        (((Real.exp (-s * w) - 1) / s + w)) ^ 2 ≤ w ^ 2 := by
      nlinarith
    have herr := sturmRealHeat_closed_graph_slope_error_repr
      lam hlam s hs x n
    have herr' :
        (b.repr (err s)) n =
          ((Real.exp (-s * w) - 1) / s + w) * c := by
      simpa [err, v, sturmRealHeatLimitNonnegativeExtended,
        max_eq_right hs.le, w, c, b] using herr
    have hA : (b.repr (A x)) n = (-w) * c := by
      convert hclosed n using 1 <;> ring
    rw [herr', hA]
    calc
      (((Real.exp (-s * w) - 1) / s + w) * c) ^ 2 =
        (((Real.exp (-s * w) - 1) / s + w)) ^ 2 * c ^ 2 := by ring
      _ ≤ w ^ 2 * c ^ 2 :=
        mul_le_mul_of_nonneg_right hsq (sq_nonneg c)
      _ = ((-w) * c) ^ 2 := by ring
  have hboundEv :
      ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ n : ℕ,
        ‖((b.repr (err s)) n) ^ 2‖ ≤
          ((b.repr (A x)) n) ^ 2 := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    intro n
    change |((b.repr (err s)) n) ^ 2| ≤
      ((b.repr (A x)) n) ^ 2
    have hsqnonneg :
        0 ≤ ((b.repr (err s)) n : ℝ) ^ 2 := sq_nonneg _
    simpa only [abs_of_nonneg hsqnonneg] using hbound s hs n
  have htannery : Tendsto
      (fun s : ℝ => ∑' n : ℕ, ((b.repr (err s)) n) ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (∑' _n : ℕ, (0 : ℝ))) :=
    tendsto_tsum_of_dominated_convergence
      (hsquared (A x)) hpoint hboundEv
  have hsumzero :
      Tendsto (fun s : ℝ => ∑' n : ℕ, ((b.repr (err s)) n) ^ 2)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [tsum_zero] using htannery
  have hnormsq : Tendsto (fun s : ℝ => ‖err s‖ ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have hfun :
        (fun s : ℝ => ∑' n : ℕ, ((b.repr (err s)) n) ^ 2) =
        (fun s : ℝ => ‖err s‖ ^ 2) := by
      funext s
      exact sturmMonic_realL2_parseval_tsum_sq lam hlam (err s)
    rw [hfun] at hsumzero
    exact hsumzero
  have hroot := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hnormsq
  have hnorm : Tendsto (fun s : ℝ => ‖err s‖)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have hid :
        (fun s : ℝ => Real.sqrt (‖err s‖ ^ 2)) =
          (fun s : ℝ => ‖err s‖) := by
      funext s
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
    have hroot' : Tendsto
        (fun s : ℝ => Real.sqrt (‖err s‖ ^ 2))
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
      simpa only [Function.comp_def, Real.sqrt_zero] using hroot
    rwa [hid] at hroot'
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  change Tendsto (fun s : ℝ => ‖err s‖)
    (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ))
  exact hnorm

#print axioms GegenbauerFock.Ultraspherical.sturmRealHeatLimit_closed_sturm_right_derivative

end GegenbauerFock.Ultraspherical
