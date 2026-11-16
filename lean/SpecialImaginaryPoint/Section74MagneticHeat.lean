import Mathlib

/-! M14 §7.4 (author source 2026-11-16), Theorem 7.5 and Corollary 7.6.
    Scalar spectral core with actual infinite series, not a surrogate finite sum.
    The magnetic Friedrichs operator, compact resolvent, Raymond asymptotics
    and diamagnetic trace bound are separate operator/PDE obligations.
    Classical harmonic-oscillator and summability identities; no novelty claim. -/

open Filter Topology
noncomputable section
namespace Manuscript14.MagneticHeat

def oddEnergy (n : ℕ) : ℝ := 2 * (n : ℝ) + 1
def weight (x : ℝ) (n : ℕ) : ℝ := Real.exp (-x * oddEnergy n)
def heat (x : ℝ) : ℝ := 1 / (2 * Real.sinh x)
def langevin (x : ℝ) : ℝ := Real.cosh x / Real.sinh x - x⁻¹
def fluctuation (x : ℝ) : ℝ := (x^2)⁻¹ - (Real.sinh x^2)⁻¹

theorem weight_geometric (x : ℝ) (n : ℕ) :
    weight x n = Real.exp (-x) * Real.exp (-2 * x) ^ n := by
  unfold weight oddEnergy
  rw [show -x * (2 * (n : ℝ) + 1) = -x + (n : ℝ) * (-2 * x) by ring,
    Real.exp_add, Real.exp_nat_mul]

theorem odd_heat_summable (x : ℝ) (hx : 0 < x) : Summable (weight x) := by
  have h : Real.exp (-2 * x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have he : weight x = fun n => Real.exp (-x) * Real.exp (-2*x)^n :=
    funext (weight_geometric x)
  rw [he]
  exact (summable_geometric_of_lt_one (Real.exp_pos _).le h).mul_left (Real.exp (-x))

/-- Equation (118): actual summed limiting ladder with zero-based index. -/
theorem odd_heat_tsum (x : ℝ) (hx : 0 < x) :
    (∑' n : ℕ, weight x n) = heat x := by
  have h : Real.exp (-2 * x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hs : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx
  simp only [weight_geometric, tsum_mul_left,
    tsum_geometric_of_lt_one (Real.exp_pos _).le h, heat]
  have h1 : Real.exp (-x) * Real.exp x = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have h2 : Real.exp (-x) * Real.exp (-x) = Real.exp (-2 * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hh : Real.exp (-x) * (2 * Real.sinh x) =
      1 - Real.exp (-2 * x) := by
    rw [Real.sinh_eq]
    calc
      Real.exp (-x) * (2 * ((Real.exp x - Real.exp (-x)) / 2)) =
          Real.exp (-x) * Real.exp x - Real.exp (-x) * Real.exp (-x) := by ring
      _ = _ := by rw [h1, h2]
  rw [← div_eq_mul_inv]
  exact (div_eq_div_iff (ne_of_gt (sub_pos.mpr h)) (mul_ne_zero two_ne_zero (ne_of_gt hs))).2 (by simpa only [one_mul] using hh)

/-- Half-time tail, equation (124). The half trace must be summable.
    No magnetic heat-kernel estimate is assumed as a Lean axiom. -/
theorem heat_tail_half (E : ℕ → ℝ) (hE : Monotone E) (s : ℝ)
    (hs : 0 < s) (N : ℕ)
    (hhalf : Summable (fun n => Real.exp (-(s/2) * E n))) :
    (∑' n : ℕ, Real.exp (-s * E (n+N))) ≤
      Real.exp (-(s/2) * E N) * (∑' n : ℕ, Real.exp (-(s/2) * E n)) := by
  let c := Real.exp (-(s/2) * E N)
  have hc : 0 < c := Real.exp_pos _
  have hshift : Summable (fun n : ℕ => Real.exp (-(s/2) * E (n+N))) :=
    (summable_nat_add_iff N).2 hhalf
  have hdom := hshift.mul_left c
  have hp : ∀ n : ℕ, Real.exp (-s * E (n+N)) ≤
      c * Real.exp (-(s/2) * E (n+N)) := by
    intro n
    dsimp [c]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have he : E N ≤ E (n+N) := hE (by omega)
    nlinarith [mul_nonneg hs.le (sub_nonneg.mpr he)]
  have hsum : Summable (fun n : ℕ => Real.exp (-s * E (n+N))) :=
    hdom.of_norm_bounded (fun n => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact hp n)
  have htail : (∑' n : ℕ, Real.exp (-(s/2) * E (n+N))) ≤
      ∑' n : ℕ, Real.exp (-(s/2) * E n) := by
    have he := hhalf.sum_add_tsum_nat_add N
    have hn : 0 ≤ ∑ n ∈ Finset.range N, Real.exp (-(s/2) * E n) :=
      Finset.sum_nonneg (fun n _ => (Real.exp_pos _).le)
    linarith
  calc
    (∑' n : ℕ, Real.exp (-s * E (n+N))) ≤
        ∑' n : ℕ, c * Real.exp (-(s/2) * E (n+N)) :=
      hsum.tsum_le_tsum hp hdom
    _ = c * (∑' n : ℕ, Real.exp (-(s/2) * E (n+N))) := by
      rw [tsum_mul_left]
    _ ≤ _ := mul_le_mul_of_nonneg_left htail hc.le

/-- Abstract limit passage with actual finite approximants, uniform eventual
    tails, and termwise finite limits. This is independent of the PDE. -/
theorem limit_of_truncations {ι : Type*} {l : Filter ι}
    (T : ι → ℝ) (P : ℕ → ι → ℝ) (Q : ℕ → ℝ) (S : ℝ)
    (hP : ∀ n, Tendsto (P n) l (𝓝 (Q n)))
    (hQ : Tendsto Q atTop (𝓝 S))
    (hTail : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
      ∀ᶠ i in l, dist (T i) (P n i) < ε) :
    Tendsto T l (𝓝 S) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨N0, h0⟩ := hTail (ε/3) hε3
  obtain ⟨N1, h1⟩ := eventually_atTop.1
    (Metric.tendsto_nhds.1 hQ (ε/3) hε3)
  let N := max N0 N1
  have hk := h1 N (le_max_right N0 N1)
  filter_upwards [h0 N (le_max_left N0 N1),
    Metric.tendsto_nhds.1 (hP N) (ε/3) hε3] with i hi hj
  have htri1 := dist_triangle (T i) (P N i) S
  have htri2 := dist_triangle (P N i) (Q N) S
  linarith

/-- A factorial bound for differentiated trace summands, all orders:
    apply with u = (δ/2)E and x ≥ δ. -/
theorem polynomial_half_time (u : ℝ) (hu : 0 ≤ u) (k : ℕ) :
    (u^k / (k.factorial : ℝ)) * Real.exp (-2*u) ≤ Real.exp (-u) := by
  calc
    _ ≤ Real.exp u * Real.exp (-2*u) :=
      mul_le_mul_of_nonneg_right (Real.pow_div_factorial_le_exp u hu k) (Real.exp_pos _).le
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- Normalization in (116), written at the spectral level. -/
theorem shift_normalization (lam lam1 h b0 c1 : ℝ) (hh : h ≠ 0) (hc : c1 ≠ 0) :
    1 + (lam - lam1) / (c1 * h^2) =
      ((lam - h*b0)/h^2) / c1 + (1 - ((lam1 - h*b0)/h^2)/c1) := by
  field_simp
  <;> ring

theorem reciprocal_profile (x : ℝ) (hx : 0 < x) :
    2*x*heat x = (Real.sinh x / x)⁻¹ := by
  have hs : Real.sinh x ≠ 0 := Real.sinh_ne_zero.mpr hx.ne'
  unfold heat
  field_simp
  <;> ring

theorem heat_hasDerivAt (x : ℝ) (hx : 0 < x) :
    HasDerivAt heat (-Real.cosh x / (2 * Real.sinh x^2)) x := by
  have hs : Real.sinh x ≠ 0 := Real.sinh_ne_zero.mpr hx.ne'
  have h := (hasDerivAt_const x (1:ℝ)).fun_div
    ((Real.hasDerivAt_sinh x).const_mul 2) (mul_ne_zero two_ne_zero hs)
  refine h.congr_deriv ?_
  field_simp
  <;> ring

theorem mean_difference (x : ℝ) (hx : 0 < x) :
    -deriv heat x / heat x - 1/x = langevin x := by
  rw [(heat_hasDerivAt x hx).deriv]
  have hs : Real.sinh x ≠ 0 := Real.sinh_ne_zero.mpr hx.ne'
  unfold heat langevin
  field_simp
  <;> ring

/-- Corollary 7.6: derivative of the limiting mean, hence minus the
    limiting Gibbs variance. -/
theorem coth_hasDerivAt (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y => Real.cosh y / Real.sinh y)
      (-(Real.sinh x ^ 2)⁻¹) x := by
  have hs : Real.sinh x ≠ 0 := Real.sinh_ne_zero.mpr hx.ne'
  have h := (Real.hasDerivAt_cosh x).fun_div (Real.hasDerivAt_sinh x) hs
  refine h.congr_deriv ?_
  have hcs := Real.cosh_sq_sub_sinh_sq x
  linear_combination (-(Real.sinh x ^ 2)⁻¹) * hcs

theorem variance_difference (x : ℝ) (hx : 0 < x) :
    1/x^2 - (-deriv (fun y => Real.cosh y / Real.sinh y) x) =
      fluctuation x := by
  rw [(coth_hasDerivAt x hx).deriv]
  simp [fluctuation, one_div]

theorem langevin_hasDerivAt (x : ℝ) (hx : 0 < x) :
    HasDerivAt langevin (fluctuation x) x := by
  have hs : Real.sinh x ≠ 0 := Real.sinh_ne_zero.mpr hx.ne'
  have h := ((Real.hasDerivAt_cosh x).fun_div (Real.hasDerivAt_sinh x) hs).fun_sub
    (hasDerivAt_inv hx.ne')
  refine h.congr_deriv ?_
  have hcs := Real.cosh_sq_sub_sinh_sq x
  simp only [fluctuation]
  linear_combination (-(Real.sinh x ^ 2)⁻¹) * hcs

theorem modular_duplication (a : ℝ) (ha : 0 < a) :
    (2*a)*heat (2*a) / (a*heat a) = 1 / Real.cosh a := by
  have hs : Real.sinh a ≠ 0 := Real.sinh_ne_zero.mpr ha.ne'
  have hc : Real.cosh a ≠ 0 := (Real.cosh_pos a).ne'
  unfold heat
  rw [Real.sinh_two_mul]
  field_simp
  <;> ring

#print axioms weight_geometric
#print axioms odd_heat_summable
#print axioms odd_heat_tsum
#print axioms heat_tail_half
#print axioms limit_of_truncations
#print axioms polynomial_half_time
#print axioms shift_normalization
#print axioms reciprocal_profile
#print axioms heat_hasDerivAt
#print axioms mean_difference
#print axioms coth_hasDerivAt
#print axioms variance_difference
#print axioms langevin_hasDerivAt
#print axioms modular_duplication

end Manuscript14.MagneticHeat
