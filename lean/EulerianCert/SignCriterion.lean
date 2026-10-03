/-
# Lemma 3.2 of the V478 manuscript (common-endpoint sign criterion) and its truncation and
# damping cases (Corollaries 3.3, 3.9, 3.11 and Proposition 3.4, abstract form)

We formalise the *common-endpoint sign criterion*, Lemma 3.2.

Let `c d : ℕ → ℝ` with `0 ≤ d n ≤ c n`, `c` summable and `∑' c < b`.  Index `n` here is mode
`n + 1` of the manuscript, with sign `(-1)^n = (-1)^((n+1)+1)`, i.e. the profiles of Eq. (14) are

  `prof b c θ = b + ∑' n, (-1)^n * c n * cos ((n+1) θ)`.

Then, writing `E = ∑' (c n - d n)` (Eqs. 15–16):
* `prof b c` and `prof b d` attain their minimum at `θ = π`;
* `sup_θ |prof b c θ - prof b d θ| = E`, attained at `θ = π`;
* the Hausdorff distance between the polar curves
  `Γ h = {h θ · e^{iθ} : θ ∈ [-π, π]} ⊆ ℂ` equals `E`.

The truncation statement of Lemma 3.2 (and hence, with `c n = |A_{n+1}|`, Corollaries 3.3 and
3.9 and Proposition 3.4) is the case `d n = c n` for `n < N`, `d n = 0` otherwise
(`E = ∑_{n ≥ N} c n`); Corollary 3.11 (coefficient damping) is the case `d n = w n * c n` with
`0 ≤ w n ≤ 1`.
-/
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Real

open Real Complex Metric Set Finset Filter

noncomputable section

namespace EulerianCert

/-- The alternating cosine profile `b + ∑' n, (-1)^n c_n cos((n+1)θ)`. -/
def prof (b : ℝ) (c : ℕ → ℝ) (θ : ℝ) : ℝ :=
  b + ∑' n : ℕ, (-1 : ℝ) ^ n * c n * Real.cos ((n + 1 : ℝ) * θ)

/-- The closed polar curve `θ ↦ h(θ) e^{iθ}`, `θ ∈ [-π, π]`, as a subset of `ℂ ≃ ℝ²`. -/
def polarCurve (h : ℝ → ℝ) : Set ℂ :=
  (fun θ : ℝ => (h θ : ℂ) * Complex.exp (θ * Complex.I)) '' Icc (-π) π

section Lemmas

variable {c : ℕ → ℝ}

lemma cos_succ_mul_pi (n : ℕ) : Real.cos ((n + 1 : ℝ) * π) = (-1 : ℝ) ^ (n + 1) := by
  have := Real.cos_nat_mul_pi (n + 1)
  push_cast at this
  exact this

lemma sign_mul_cos_pi (n : ℕ) : (-1 : ℝ) ^ n * Real.cos ((n + 1 : ℝ) * π) = -1 := by
  rw [cos_succ_mul_pi, ← pow_add]
  have : n + (n + 1) = 2 * n + 1 := by ring
  rw [this, pow_succ, pow_mul]
  norm_num

lemma term_abs_le (hc : ∀ n, 0 ≤ c n) (n : ℕ) (θ : ℝ) :
    |(-1 : ℝ) ^ n * c n * Real.cos ((n + 1 : ℝ) * θ)| ≤ c n := by
  rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg (hc n)]
  exact mul_le_of_le_one_right (hc n) (Real.abs_cos_le_one _)

/-- Every mode is bounded below by `-c n`, with equality at `π`. -/
lemma term_ge (hc : ∀ n, 0 ≤ c n) (n : ℕ) (θ : ℝ) :
    -c n ≤ (-1 : ℝ) ^ n * c n * Real.cos ((n + 1 : ℝ) * θ) :=
  neg_le_of_abs_le (term_abs_le hc n θ)

lemma term_pi (n : ℕ) : (-1 : ℝ) ^ n * c n * Real.cos ((n + 1 : ℝ) * π) = -c n := by
  have h := sign_mul_cos_pi n
  calc (-1 : ℝ) ^ n * c n * Real.cos ((n + 1 : ℝ) * π)
      = c n * ((-1 : ℝ) ^ n * Real.cos ((n + 1 : ℝ) * π)) := by ring
    _ = -c n := by rw [h]; ring

lemma summable_terms (hc : ∀ n, 0 ≤ c n) (hs : Summable c) (θ : ℝ) :
    Summable (fun n : ℕ => (-1 : ℝ) ^ n * c n * Real.cos ((n + 1 : ℝ) * θ)) :=
  Summable.of_norm_bounded hs (fun n => by
    rw [Real.norm_eq_abs]; exact term_abs_le hc n θ)

end Lemmas

/-! ### Helper lemmas on profiles and polar curves -/

section Helpers

lemma prof_pi (b : ℝ) (e : ℕ → ℝ) : prof b e π = b - ∑' n, e n := by
  unfold prof
  simp_rw [term_pi, tsum_neg]
  ring

lemma norm_polar (h : ℝ → ℝ) (θ : ℝ) :
    ‖(h θ : ℂ) * Complex.exp (θ * Complex.I)‖ = |h θ| := by
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

lemma dist_polar (h k : ℝ → ℝ) (θ : ℝ) :
    dist ((h θ : ℂ) * Complex.exp (θ * Complex.I)) ((k θ : ℂ) * Complex.exp (θ * Complex.I)) =
      |h θ - k θ| := by
  rw [dist_eq_norm, ← sub_mul, ← Complex.ofReal_sub]
  simpa using norm_polar (fun t => h t - k t) θ

lemma abs_tsum_terms_le (e : ℕ → ℝ) (he : ∀ n, 0 ≤ e n) (hs : Summable e) (θ : ℝ) :
    |∑' n : ℕ, (-1 : ℝ) ^ n * e n * Real.cos ((n + 1 : ℝ) * θ)| ≤ ∑' n, e n := by
  have hsum := summable_terms he hs θ
  have hn : Summable (fun n : ℕ => ‖(-1 : ℝ) ^ n * e n * Real.cos ((n + 1 : ℝ) * θ)‖) := by
    simpa [Real.norm_eq_abs] using hsum.abs
  calc |∑' n : ℕ, (-1 : ℝ) ^ n * e n * Real.cos ((n + 1 : ℝ) * θ)|
      ≤ ∑' n : ℕ, ‖(-1 : ℝ) ^ n * e n * Real.cos ((n + 1 : ℝ) * θ)‖ := by
        rw [← Real.norm_eq_abs]; exact norm_tsum_le_tsum_norm hn
    _ ≤ ∑' n, e n := hn.tsum_le_tsum (fun n => by
          rw [Real.norm_eq_abs]; exact term_abs_le he n θ) hs

lemma abs_prof_le (b : ℝ) (e : ℕ → ℝ) (he : ∀ n, 0 ≤ e n) (hs : Summable e) (θ : ℝ) :
    |prof b e θ| ≤ |b| + ∑' n, e n := by
  unfold prof
  have h1 := abs_add_le b (∑' n : ℕ, (-1 : ℝ) ^ n * e n * Real.cos ((n + 1 : ℝ) * θ))
  have h2 := abs_tsum_terms_le e he hs θ
  linarith

lemma polarCurve_bounded (b : ℝ) (e : ℕ → ℝ) (he : ∀ n, 0 ≤ e n) (hs : Summable e) :
    Bornology.IsBounded (polarCurve (prof b e)) := by
  rw [isBounded_iff_forall_norm_le]
  refine ⟨|b| + ∑' n, e n, ?_⟩
  rintro _ ⟨θ, -, rfl⟩
  rw [norm_polar]
  exact abs_prof_le b e he hs θ

lemma pi_mem : π ∈ Icc (-π) π := ⟨by linarith [Real.pi_pos], le_rfl⟩

end Helpers

/-! ### The general comparison theorem -/

section General

variable {b : ℝ} {c d : ℕ → ℝ}

/-- Hypotheses of the generalised sign criterion. -/
structure Hyp (b : ℝ) (c d : ℕ → ℝ) : Prop where
  d_nonneg : ∀ n, 0 ≤ d n
  d_le_c : ∀ n, d n ≤ c n
  summable : Summable c
  tsum_lt : ∑' n, c n < b

namespace Hyp

variable (H : Hyp b c d)
include H

lemma c_nonneg (n : ℕ) : 0 ≤ c n := (H.d_nonneg n).trans (H.d_le_c n)

lemma summable_d : Summable d :=
  Summable.of_nonneg_of_le H.d_nonneg H.d_le_c H.summable

lemma summable_diff : Summable (fun n => c n - d n) := H.summable.sub H.summable_d

lemma diff_nonneg (n : ℕ) : 0 ≤ c n - d n := sub_nonneg.2 (H.d_le_c n)

/-- The two profiles differ by an alternating cosine series with coefficients `c - d ≥ 0`. -/
lemma prof_sub (θ : ℝ) :
    prof b c θ - prof b d θ =
      ∑' n : ℕ, (-1 : ℝ) ^ n * (c n - d n) * Real.cos ((n + 1 : ℝ) * θ) := by
  unfold prof
  rw [add_sub_add_left_eq_sub,
    ← (summable_terms H.c_nonneg H.summable θ).tsum_sub
      (summable_terms H.d_nonneg H.summable_d θ)]
  congr 1
  ext n
  ring

/-- `prof b c` attains its global minimum `b - ∑' c` at `θ = π`. -/
lemma prof_min_c (θ : ℝ) : prof b c π ≤ prof b c θ := by
  have key : prof b c θ - prof b c π =
      ∑' n : ℕ, ((-1 : ℝ) ^ n * c n * Real.cos ((n + 1 : ℝ) * θ) + c n) := by
    unfold prof
    simp_rw [term_pi, tsum_neg]
    rw [(summable_terms H.c_nonneg H.summable θ).tsum_add H.summable]
    ring
  have : 0 ≤ prof b c θ - prof b c π := by
    rw [key]
    exact tsum_nonneg (fun n => by linarith [term_ge H.c_nonneg n θ])
  linarith

lemma prof_min_d (θ : ℝ) : prof b d π ≤ prof b d θ := by
  have Hd : Hyp b d d := ⟨H.d_nonneg, fun _ => le_rfl, H.summable_d,
    lt_of_le_of_lt (H.summable_d.tsum_le_tsum H.d_le_c H.summable) H.tsum_lt⟩
  exact Hd.prof_min_c θ

lemma tsum_c_pos_lt : 0 < b - ∑' n, c n := sub_pos.2 H.tsum_lt

lemma prof_c_pos (θ : ℝ) : 0 < prof b c θ := by
  have := H.prof_min_c θ
  rw [prof_pi b] at this
  linarith [H.tsum_c_pos_lt]

lemma tsum_d_le : ∑' n, d n ≤ ∑' n, c n := H.summable_d.tsum_le_tsum H.d_le_c H.summable

lemma prof_d_pos (θ : ℝ) : 0 < prof b d θ := by
  have := H.prof_min_d θ
  rw [prof_pi b] at this
  linarith [H.tsum_c_pos_lt, H.tsum_d_le]

/-- The common exact error `E = ∑' (c - d)`. -/
lemma err_eq : prof b d π - prof b c π = ∑' n, (c n - d n) := by
  rw [prof_pi b, prof_pi b, H.summable.tsum_sub H.summable_d]
  ring

/-- Uniform bound: `|prof c - prof d| ≤ E` everywhere. -/
lemma abs_sub_le (θ : ℝ) : |prof b c θ - prof b d θ| ≤ ∑' n, (c n - d n) := by
  rw [H.prof_sub θ]
  exact abs_tsum_terms_le (fun n => c n - d n) H.diff_nonneg H.summable_diff θ

/-- ... with equality at `θ = π`. -/
lemma abs_sub_pi : |prof b c π - prof b d π| = ∑' n, (c n - d n) := by
  rw [abs_sub_comm, H.err_eq, abs_of_nonneg (tsum_nonneg H.diff_nonneg)]

/-- **Sharp uniform error**: `E` is the maximum of `|prof c - prof d|`, attained at `π`. -/
theorem isGreatest_abs_sub :
    IsGreatest (range fun θ => |prof b c θ - prof b d θ|) (∑' n, (c n - d n)) :=
  ⟨⟨π, H.abs_sub_pi⟩, by rintro _ ⟨θ, rfl⟩; exact H.abs_sub_le θ⟩

/-- **Exact Hausdorff distance** between the two polar curves. -/
theorem hausdorffDist_eq :
    hausdorffDist (polarCurve (prof b c)) (polarCurve (prof b d)) = ∑' n, (c n - d n) := by
  set E := ∑' n, (c n - d n) with hE
  have hE0 : 0 ≤ E := tsum_nonneg H.diff_nonneg
  apply le_antisymm
  · -- equal-angle pairing
    apply hausdorffDist_le_of_mem_dist hE0
    · rintro _ ⟨θ, hθ, rfl⟩
      exact ⟨_, ⟨θ, hθ, rfl⟩, by rw [dist_polar]; exact H.abs_sub_le θ⟩
    · rintro _ ⟨θ, hθ, rfl⟩
      exact ⟨_, ⟨θ, hθ, rfl⟩, by rw [dist_polar, abs_sub_comm]; exact H.abs_sub_le θ⟩
  · -- the endpoint `p = γ_c(π)` is at distance `≥ E` from every point of `Γ_d`
    set p : ℂ := (prof b c π : ℂ) * Complex.exp (π * Complex.I)
    have hp : p ∈ polarCurve (prof b c) := ⟨π, pi_mem, rfl⟩
    have hne : (polarCurve (prof b d)).Nonempty := ⟨_, ⟨π, pi_mem, rfl⟩⟩
    have fin : hausdorffEDist (polarCurve (prof b c)) (polarCurve (prof b d)) ≠ ⊤ :=
      hausdorffEDist_ne_top_of_nonempty_of_bounded ⟨p, hp⟩ hne
        (polarCurve_bounded b c H.c_nonneg H.summable)
        (polarCurve_bounded b d H.d_nonneg H.summable_d)
    refine le_trans ?_ (infDist_le_hausdorffDist_of_mem hp fin)
    rw [le_infDist hne]
    rintro _ ⟨θ, -, rfl⟩
    have hpn : ‖p‖ = prof b c π := by
      rw [norm_polar, abs_of_pos (H.prof_c_pos π)]
    have hyn : ‖(prof b d θ : ℂ) * Complex.exp (θ * Complex.I)‖ = prof b d θ := by
      rw [norm_polar, abs_of_pos (H.prof_d_pos θ)]
    have tri : ‖(prof b d θ : ℂ) * Complex.exp (θ * Complex.I)‖ - ‖p‖ ≤
        dist p ((prof b d θ : ℂ) * Complex.exp (θ * Complex.I)) := by
      rw [dist_comm, dist_eq_norm]
      exact norm_sub_norm_le _ _
    rw [hpn, hyn] at tri
    have := H.prof_min_d θ
    have := H.err_eq
    linarith

end Hyp

/-- **Lemma 3.2 (common-endpoint sign criterion), Eqs. (15)–(16).**  For `0 ≤ d ≤ c`, `c`
summable, `∑' c < b`, with `q = b - ∑' c` and `E = ∑' (c - d)`: both profiles are positive and
minimal at `π`, `f_c(π) = q`, `f_d(π) = q + E`, the sup-norm error is `E` (attained at `π`), and
the Hausdorff distance between the polar curves in `ℂ` is `E`. -/
theorem common_endpoint_sign_criterion (H : Hyp b c d) :
    (∀ θ, prof b c π ≤ prof b c θ) ∧ prof b c π = b - ∑' n, c n ∧
    (∀ θ, prof b d π ≤ prof b d θ) ∧ prof b d π = (b - ∑' n, c n) + ∑' n, (c n - d n) ∧
    (∀ θ, 0 < prof b c θ ∧ 0 < prof b d θ) ∧
    IsGreatest (range fun θ => |prof b c θ - prof b d θ|) (∑' n, (c n - d n)) ∧
    hausdorffDist (polarCurve (prof b c)) (polarCurve (prof b d)) = ∑' n, (c n - d n) := by
  refine ⟨H.prof_min_c, prof_pi b c, H.prof_min_d, ?_,
    fun θ => ⟨H.prof_c_pos θ, H.prof_d_pos θ⟩, H.isGreatest_abs_sub, H.hausdorffDist_eq⟩
  have := H.err_eq
  rw [prof_pi b c] at this
  linarith

end General

/-! ### Fourier truncations (Lemma 3.2, Corollaries 3.3 and 3.9, Proposition 3.4) -/

section Truncation

variable {b : ℝ} {c : ℕ → ℝ}

/-- Coefficients of the truncation `P_N f`: modes `1, …, N` kept. -/
def trunc (c : ℕ → ℝ) (N : ℕ) (n : ℕ) : ℝ := if n < N then c n else 0

lemma prof_trunc (N : ℕ) (θ : ℝ) :
    prof b (trunc c N) θ =
      b + ∑ n ∈ range N, (-1 : ℝ) ^ n * c n * Real.cos ((n + 1 : ℝ) * θ) := by
  unfold prof
  congr 1
  rw [tsum_eq_sum (s := range N)]
  · refine Finset.sum_congr rfl (fun n hn => ?_)
    simp [trunc, Finset.mem_range.1 hn]
  · intro n hn
    simp [trunc, Finset.mem_range.not.1 hn]

lemma tail_eq (hs : Summable c) (N : ℕ) :
    ∑' n, (c n - trunc c N n) = ∑' n, c (n + N) := by
  have h1 : Summable (fun n => c n - trunc c N n) := by
    refine hs.sub ?_
    exact summable_of_ne_finset_zero (s := range N) (fun n hn => by
      simp [trunc, Finset.mem_range.not.1 hn])
  rw [← h1.sum_add_tsum_nat_add N]
  have : ∑ i ∈ range N, (c i - trunc c N i) = 0 :=
    Finset.sum_eq_zero (fun i hi => by simp [trunc, Finset.mem_range.1 hi])
  rw [this, zero_add]
  congr 1
  ext n
  simp only [trunc]
  rw [ite_eq_right (by omega)]
  ring

/-- **Lemma 3.2, truncation case.**  For `c ≥ 0` summable with `∑' c < b`:
the profile and every truncation attain their minima at `π`; the sharp uniform error and the
Hausdorff distance both equal the coefficient tail `η_N = ∑_{n ≥ N} c n`. -/
theorem sign_criterion (hc : ∀ n, 0 ≤ c n) (hs : Summable c) (hb : ∑' n, c n < b) (N : ℕ) :
    (∀ θ, prof b c π ≤ prof b c θ) ∧ prof b c π = b - ∑' n, c n ∧
    (∀ θ, prof b (trunc c N) π ≤ prof b (trunc c N) θ) ∧
    prof b (trunc c N) π = (b - ∑' n, c n) + ∑' n, c (n + N) ∧
    IsGreatest (range fun θ => |prof b c θ - prof b (trunc c N) θ|) (∑' n, c (n + N)) ∧
    hausdorffDist (polarCurve (prof b c)) (polarCurve (prof b (trunc c N))) =
      ∑' n, c (n + N) := by
  have H : Hyp b c (trunc c N) :=
    ⟨fun n => by unfold trunc; split_ifs <;> simp [hc n],
     fun n => by unfold trunc; split_ifs <;> simp [hc n], hs, hb⟩
  refine ⟨H.prof_min_c, prof_pi b c, H.prof_min_d, ?_, ?_, ?_⟩
  · have := H.err_eq
    rw [tail_eq hs N] at this
    rw [prof_pi b c] at this
    linarith
  · rw [← tail_eq hs N]; exact H.isGreatest_abs_sub
  · rw [← tail_eq hs N]; exact H.hausdorffDist_eq

/-- **Corollary 3.11 (coefficient damping).**  Retaining mode `n+1` with weight `w n ∈ [0,1]`
(and dropping modes with `n ≥ N`) gives exact uniform and Hausdorff errors
`∑_{n<N} (1 - w n) c n + ∑_{n ≥ N} c n`. -/
theorem damping (hc : ∀ n, 0 ≤ c n) (hs : Summable c) (hb : ∑' n, c n < b)
    (N : ℕ) (w : ℕ → ℝ) (hw0 : ∀ n, 0 ≤ w n) (hw1 : ∀ n, w n ≤ 1) :
    let d : ℕ → ℝ := fun n => if n < N then w n * c n else 0
    IsGreatest (range fun θ => |prof b c θ - prof b d θ|)
        (∑ n ∈ range N, (1 - w n) * c n + ∑' n, c (n + N)) ∧
    hausdorffDist (polarCurve (prof b c)) (polarCurve (prof b d)) =
        ∑ n ∈ range N, (1 - w n) * c n + ∑' n, c (n + N) := by
  intro d
  have H : Hyp b c d :=
    ⟨fun n => by simp only [d]; split_ifs <;> simp [mul_nonneg (hw0 n) (hc n)],
     fun n => by
       simp only [d]; split_ifs
       · exact mul_le_of_le_one_left (hc n) (hw1 n)
       · exact hc n, hs, hb⟩
  have hE : ∑' n, (c n - d n) = ∑ n ∈ range N, (1 - w n) * c n + ∑' n, c (n + N) := by
    rw [← H.summable_diff.sum_add_tsum_nat_add N]
    congr 1
    · refine Finset.sum_congr rfl (fun n hn => ?_)
      simp only [d, ite_eq_left (Finset.mem_range.1 hn)]; ring
    · congr 1; ext n; simp only [d]; rw [ite_eq_right (by omega)]; ring
  rw [← hE]
  exact ⟨H.isGreatest_abs_sub, H.hausdorffDist_eq⟩

end Truncation

end EulerianCert
