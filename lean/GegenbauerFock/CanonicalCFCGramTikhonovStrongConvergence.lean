import GegenbauerFock.CanonicalCFCGramTikhonovDenseRangeError
import GegenbauerFock.TwoSidedGramProperDenseRange
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel

/-!
# V007 — genuine source Gram Tikhonov strong convergence on the full L²

Let G = C* C on the actual complex weighted L² source Hilbert space,
A_eps = G + eps I, E_eps = eps A_eps^{-1}, T_eps = I - E_eps.
For eps>0 the independently proved Gram coercivity and inverse identities
give ||E_eps|| <= 1, while the exact dense-image identity yields
||E_eps (G y)|| <= 2 eps ||y||. The genuine Gram has dense range.

This module extends that convergence to every source vector, not only
finite eigenmode sums or range vectors. No uniform operator-norm
convergence, or bounded inverse of the unshifted compact Gram, is claimed.
-/

noncomputable section

namespace GegenbauerFock.GeneralUltrasphericalFock

open MeasureTheory Filter
open scoped Topology

private abbrev RegH (lam : ℝ) := Lp ℂ 2 (Ultraspherical.measure lam)

private noncomputable def regularizationError
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (eps : ℝ) : RegH lam →L[ℂ] RegH lam :=
  (eps : ℂ) • Ring.inverse (sourceGramPositiveShift lam alpha hlam ha eps)

/-- Uniform quantitative bound by the distance to a genuine Gram-range
vector, plus an O(eps) term, valid for all x,y in actual complex L². -/
theorem sourceGramTikhonov_error_dense_approximation
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (eps : ℝ) (heps : 0 < eps) (x y : RegH lam) :
    ‖regularizationError lam alpha hlam ha eps x‖ ≤
      ‖x - gram lam alpha hlam ha y‖ + 2 * eps * ‖y‖ := by
  let G := gram lam alpha hlam ha
  let E := regularizationError lam alpha hlam ha eps
  have hdiff : ‖E (x - G y)‖ ≤ ‖x - G y‖ := by
    simpa only [E, regularizationError, G] using
      sourceGramTikhonov_error_pointwise_contract
        lam alpha hlam ha eps heps (x - G y)
  have hrange : ‖E (G y)‖ ≤ 2 * eps * ‖y‖ := by
    simpa only [E, regularizationError, G] using
      sourceGramTikhonov_error_on_range_norm
        lam alpha hlam ha eps heps y
  have hsplit : E x = E (x - G y) + E (G y) := by
    rw [map_sub]
    abel
  change ‖E x‖ ≤ ‖x - G y‖ + 2 * eps * ‖y‖
  calc
    ‖E x‖ = ‖E (x - G y) + E (G y)‖ := by rw [← hsplit]
    _ ≤ ‖E (x - G y)‖ + ‖E (G y)‖ := norm_add_le _ _
    _ ≤ ‖x - G y‖ + 2 * eps * ‖y‖ := add_le_add hdiff hrange

/-- The genuine source Gram, not a diagonal surrogate, has dense range. -/
theorem sourceGram_denseRange_for_tikhonov
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    DenseRange (gram lam alpha hlam ha) := by
  apply denseRange_iff_closure_range.mpr
  have h := gram_dense_range lam alpha hlam ha
  have hset := congrArg
    (fun S : Submodule ℂ (RegH lam) => (S : Set (RegH lam))) h
  have hRange :
      ((↑(gram lam alpha hlam ha).toLinearMap.range) : Set (RegH lam)) =
        Set.range (gram lam alpha hlam ha) := by
    ext z
    simp only [SetLike.mem_coe, LinearMap.mem_range, Set.mem_range]
    rfl
  simpa only [Submodule.topologicalClosure_coe, Submodule.top_coe,
    hRange] using hset

/-- Unconditional strong convergence E_eps x -> 0 as eps descends to
zero, for every vector of the full genuine ultraspherical complex L². -/
theorem sourceGramTikhonov_error_strong_tendsto_zero
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (x : RegH lam) :
    Tendsto
      (fun eps : ℝ => regularizationError lam alpha hlam ha eps x)
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds (0 : RegH lam)) := by
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  obtain ⟨y, hy⟩ :=
    (sourceGram_denseRange_for_tikhonov lam alpha hlam ha).exists_dist_lt
      x (show 0 < δ / 2 by positivity)
  have hnear : ‖x - gram lam alpha hlam ha y‖ < δ / 2 := by
    first
    | simpa only [dist_eq_norm] using hy
    | simpa only [dist_eq_norm, norm_sub_rev] using hy
  have hcont :
      ContinuousAt (fun eps : ℝ => 2 * eps * ‖y‖) (0 : ℝ) :=
    (continuousAt_const.mul continuousAt_id).mul continuousAt_const
  have hsmalllim :
      Tendsto (fun eps : ℝ => 2 * eps * ‖y‖)
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds (0 : ℝ)) := by
    simpa only [mul_zero, zero_mul] using
      hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hzeroSmall : ∀ᶠ z : ℝ in nhds (0 : ℝ), z < δ / 2 := by
    exact isOpen_Iio.mem_nhds
      (show (0 : ℝ) ∈ Set.Iio (δ / 2) by
        change (0 : ℝ) < δ / 2
        linarith)
  have hsmall :
      ∀ᶠ eps : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        2 * eps * ‖y‖ < δ / 2 :=
    hsmalllim.eventually hzeroSmall
  filter_upwards [self_mem_nhdsWithin, hsmall] with eps heps hε
  have hbound := sourceGramTikhonov_error_dense_approximation
    lam alpha hlam ha eps heps x y
  calc
    dist (regularizationError lam alpha hlam ha eps x)
        (0 : RegH lam) =
          ‖regularizationError lam alpha hlam ha eps x‖ := dist_zero_right _
    _ ≤ ‖x - gram lam alpha hlam ha y‖ + 2 * eps * ‖y‖ := hbound
    _ < δ / 2 + δ / 2 := add_lt_add hnear hε
    _ = δ := by ring

/-- Strong convergence of the genuine bounded Gram Tikhonov filter
T_eps = G (G + eps I)^(-1) to identity on the entire source Hilbert space. -/
theorem sourceGramTikhonovFilter_fullL2_strong_tendsto
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (x : RegH lam) :
    Tendsto
      (fun eps : ℝ => sourceGramTikhonovFilter lam alpha hlam ha eps x)
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds x) := by
  have hzero := sourceGramTikhonov_error_strong_tendsto_zero
    lam alpha hlam ha x
  have hsub :
      Tendsto
        (fun eps : ℝ => x - regularizationError lam alpha hlam ha eps x)
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds x) := by
    simpa only [sub_zero] using (tendsto_const_nhds.sub hzero)
  have hevent :
      (fun eps : ℝ => sourceGramTikhonovFilter lam alpha hlam ha eps x)
        =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))]
      (fun eps : ℝ => x - regularizationError lam alpha hlam ha eps x) := by
    filter_upwards [self_mem_nhdsWithin] with eps heps
    have heq := sourceGramTikhonov_filter_error_identity
      lam alpha hlam ha eps heps
    have hx := congrArg
      (fun T : RegH lam →L[ℂ] RegH lam => T x) heq
    change x - sourceGramTikhonovFilter lam alpha hlam ha eps x =
      regularizationError lam alpha hlam ha eps x at hx
    calc
      sourceGramTikhonovFilter lam alpha hlam ha eps x =
          x - (x - sourceGramTikhonovFilter lam alpha hlam ha eps x) := by abel
      _ = x - regularizationError lam alpha hlam ha eps x := by rw [hx]
  exact hsub.congr' hevent.symm

#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGramTikhonov_error_dense_approximation
#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGram_denseRange_for_tikhonov
#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGramTikhonov_error_strong_tendsto_zero
#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGramTikhonovFilter_fullL2_strong_tendsto

end GegenbauerFock.GeneralUltrasphericalFock
