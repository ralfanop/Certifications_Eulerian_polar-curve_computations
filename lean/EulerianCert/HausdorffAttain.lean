/-
# Theorem 3.13 of the V001 manuscript: Eq. (73), attainment, uniqueness, `h* < ε_rad`

* **Eq. (73)**: for every `h ≥ 0`, `d_H(Γ_E, Γ_h) = max{h, Q(h)}`.  Upper bound: an Eulerian point
  inside `Ω_h` has an equal-angle point of `Γ_h` within `h` (because `ℓ ≤ f`); one outside has a
  point of `Γ_h` on the segment to its nearest point in `Ω_h` (the polar gauge changes sign there);
  a point of `Γ_h` outside the Eulerian region has an equal-angle Eulerian point within `h`; one
  inside follows the outward normal until it meets `Γ_E` (gauge sign change), and the supporting
  half-plane of the convex `Ω_h` gives `dist(z, Ω_h) ≥` the distance travelled.
* **Attainment**: `d_H(Γ_E, Γ_{m, c+h*}) = h*`, so `h*` is the minimum over all admissible limaçons.
* **Uniqueness**: a limaçon with `d_H = h*` has `a = m`, `b = c + h*`.
* **`h* < ε_rad`** (Eq. (72)): `Q(ε_rad) < ε_rad`.
-/
import EulerianCert.LimaconConvex
import Mathlib.Topology.Order.IntermediateValue

open Real Set Metric

noncomputable section

namespace EulerianCert.HausdorffAttain

open EulerianCert.Limacon (q c m)
open EulerianCert.HausdorffMinimax
open EulerianCert.LimaconConvex

local notation "rE" => EulerianCert.FourierModes.rE

lemma rE_ge_ℓ {θ : ℝ} (hθ : θ ∈ Icc (-π) π) : c + m * Real.cos θ ≤ rE θ := by
  have := RadialMinimax.h_nonneg (RadialMinimax.cos_mem θ)
  simp only [RadialMinimax.h, RadialMinimax.ℓ] at this
  rw [RadialMinimax.rE_eq_f_cos hθ]; linarith

lemma rE_arccos (t : ℝ) (ht : t ∈ Icc (-π) π) : rE (Real.arccos (Real.cos t)) = rE t := by
  rw [← RadialMinimax.f_eq_rE_arccos, ← RadialMinimax.rE_eq_f_cos ht]

lemma pt_ne_zero {r t : ℝ} (hr : 0 < r) : pt r t ≠ 0 := by
  intro h0; have := congrArg norm h0
  rw [norm_pt, norm_zero, abs_of_pos hr] at this; linarith

lemma dist_pt_same {r r' t : ℝ} : dist (pt r t) (pt r' t) = |r - r'| := dist_pt r r' t

/-! ### Eulerian points (first half of Eq. (73)) -/

lemma seg_dist (p y : ℂ) (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) 1) :
    dist p (y + (lam : ℂ) * (p - y)) = (1 - lam) * dist p y := by
  rw [dist_eq_norm, dist_eq_norm]
  have : p - (y + (lam : ℂ) * (p - y)) = ((1 - lam : ℝ) : ℂ) * (p - y) := by push_cast; ring
  rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [hlam.2])]

theorem eulerian_point_close {h : ℝ} (hh : 0 ≤ h) {p : ℂ} (hp : p ∈ ΓE) :
    ∃ y ∈ Γh h, dist p y ≤ max h (Q h) := by
  obtain ⟨θ, hθ, rfl⟩ := hp
  change ∃ y ∈ Γh h, dist (pt (rE θ) θ) y ≤ max h (Q h)
  have hr := rE_pos hθ
  rcases le_or_gt (rE θ) (R h θ) with hin | hout
  · refine ⟨pt (R h θ) θ, γh_mem hh θ, ?_⟩
    rw [dist_pt_same, abs_sub_comm, abs_of_nonneg (by linarith)]
    have := rE_ge_ℓ hθ
    rw [R_eq hh]
    exact le_max_of_le_left (by linarith)
  · set p := pt (rE θ) θ with hpdef
    obtain ⟨y0, hy0, hd⟩ := (isCompact_Ω h).exists_infDist_eq_dist (Ω_nonempty h) p
    have hQ : dist p y0 ≤ Q h := hd ▸ le_Q ⟨θ, hθ, rfl⟩ h
    suffices H : ∃ y ∈ Γh h, dist p y ≤ dist p y0 from
      let ⟨y, hy, hdy⟩ := H; ⟨y, hy, hdy.trans (hQ.trans (le_max_right _ _))⟩
    set σ : ℝ → ℂ := fun lam => y0 + (lam : ℂ) * (p - y0) with hσ
    by_cases hz : ∃ lam ∈ Icc (0 : ℝ) 1, σ lam = 0
    · obtain ⟨lam0, hlam0, h0⟩ := hz
      refine ⟨pt (R h θ) θ, γh_mem hh θ, ?_⟩
      have e := seg_dist p y0 lam0 hlam0
      simp only [hσ] at h0
      rw [h0, dist_zero_right, hpdef, norm_pt, abs_of_pos hr] at e
      rw [dist_pt_same, abs_of_pos (by linarith)]
      have := R_pos hh θ
      nlinarith [hlam0.1, dist_nonneg (x := pt (rE θ) θ) (y := y0)]
    · push Not at hz
      set g : ℝ → ℝ := fun lam => ‖σ lam‖ - (c + h + m * ((σ lam).re / ‖σ lam‖)) with hg
      have hσc : Continuous σ := by simp only [hσ]; fun_prop
      have hgc : ContinuousOn g (Icc 0 1) := by
        apply ContinuousOn.sub (continuous_norm.comp hσc).continuousOn
        apply continuousOn_const.add (continuousOn_const.mul _)
        apply ContinuousOn.div (Complex.continuous_re.comp hσc).continuousOn
          (continuous_norm.comp hσc).continuousOn
        intro lam hlam'; exact norm_ne_zero_iff.2 (hz lam hlam')
      have hσ1 : σ 1 = p := by simp [hσ]
      have hσ0 : σ 0 = y0 := by simp [hσ]
      have hg1 : 0 < g 1 := by
        show 0 < ‖σ 1‖ - (c + h + m * ((σ 1).re / ‖σ 1‖))
        rw [hσ1, hpdef, gauge_pt hr, norm_pt, abs_of_pos hr]
        rw [R_eq hh] at hout; linarith
      have hg0 : g 0 ≤ 0 := by
        have hy0ne : y0 ≠ 0 := by rw [← hσ0]; exact hz 0 ⟨le_rfl, zero_le_one⟩
        obtain ⟨⟨t, s⟩, ⟨ht, hs⟩, rfl⟩ := hy0
        simp only at ht hs hy0ne
        have hsR : 0 < s * R h t := by
          rcases eq_or_lt_of_le (mul_nonneg hs.1 (R_pos hh t).le) with e | e
          · exact absurd (by rw [← e]; simp [pt]) hy0ne
          · exact e
        have e0 : σ 0 = pt (s * R h t) t := hσ0
        show ‖σ 0‖ - (c + h + m * ((σ 0).re / ‖σ 0‖)) ≤ 0
        rw [e0, gauge_pt hsR, norm_pt, abs_of_pos hsR, ← R_eq hh]
        nlinarith [hs.2, R_pos hh t]
      obtain ⟨lam1, hlam1, hgz⟩ := intermediate_value_Icc zero_le_one hgc ⟨hg0, hg1.le⟩
      refine ⟨σ lam1, mem_Γh_of_gauge (hz lam1 hlam1) (by simp only [hg] at hgz; linarith), ?_⟩
      rw [show σ lam1 = y0 + (lam1 : ℂ) * (p - y0) from rfl, seg_dist p y0 lam1 hlam1]
      nlinarith [hlam1.1, dist_nonneg (x := p) (y := y0)]

/-! ### Limaçon points (second half of Eq. (73)) -/

lemma norm_N_pos {h : ℝ} (hh : 0 ≤ h) (t₀ : ℝ) : 0 < ‖N h t₀‖ := by
  have e := dot_γ_N (h := h) t₀
  have hR := R_pos hh t₀
  have := abs_dot_le (pt (R h t₀) t₀) (N h t₀)
  rw [e, norm_pt, abs_of_pos hR, abs_of_pos (by positivity)] at this
  by_contra hN; push Not at hN
  have : ‖N h t₀‖ = 0 := le_antisymm hN (norm_nonneg _)
  nlinarith

theorem limacon_point_close {h : ℝ} (hh : 0 ≤ h) {p : ℂ} (hp : p ∈ Γh h) :
    ∃ y ∈ ΓE, dist p y ≤ max h (Q h) := by
  obtain ⟨t₀, ht₀, rfl⟩ := hp
  change ∃ y ∈ ΓE, dist (pt (c + h + m * Real.cos t₀) t₀) y ≤ max h (Q h)
  rw [← R_eq hh]
  have hR := R_pos hh t₀
  rcases le_or_gt (rE t₀) (R h t₀) with hout | hin
  · refine ⟨pt (rE t₀) t₀, ⟨t₀, ht₀, rfl⟩, ?_⟩
    rw [dist_pt_same, abs_of_nonneg (by linarith)]
    have := rE_ge_ℓ ht₀
    rw [R_eq hh]
    exact le_max_of_le_left (by linarith)
  · set p := pt (R h t₀) t₀ with hpdef
    set Nv := N h t₀
    have hN := norm_N_pos hh t₀
    set n : ℂ := ((‖Nv‖⁻¹ : ℝ) : ℂ) * Nv with hn
    have hnorm_n : ‖n‖ = 1 := by
      rw [hn, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hN),
        inv_mul_cancel₀ hN.ne']
    have hdot_n : dot n Nv = ‖Nv‖ := by
      rw [hn, dot_smul_left, dot_self]; field_simp
    set z : ℝ → ℂ := fun τ => p + (τ : ℂ) * n with hz
    have hdot_z : ∀ τ, dot (z τ) Nv = R h t₀ ^ 2 + τ * ‖Nv‖ := by
      intro τ
      simp only [hz]
      rw [dot_add_left, dot_smul_left, hdot_n, hpdef, dot_γ_N]
    have hz_ne : ∀ τ, 0 ≤ τ → z τ ≠ 0 := by
      intro τ hτ h0
      have := hdot_z τ
      rw [h0] at this
      simp [dot] at this
      nlinarith [mul_nonneg hτ hN.le]
    have hsep : ∀ τ, 0 ≤ τ → ∀ w ∈ Ω h, τ ≤ dist (z τ) w := by
      intro τ hτ w hw
      have h1 := supporting hh t₀ hw
      have h2 := dot_le_norm (z τ - w) n hnorm_n
      rw [dist_eq_norm]
      have e : dot (z τ - w) n = (dot (z τ) Nv - dot w Nv) / ‖Nv‖ := by
        rw [dot_sub_left]
        have hc : ∀ u : ℂ, dot u n = dot u Nv / ‖Nv‖ := by
          intro u; simp only [hn, dot, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
            Complex.ofReal_im]; field_simp; ring
        rw [hc, hc]; ring
      rw [e, hdot_z, div_le_iff₀ hN] at h2
      have : τ * ‖Nv‖ ≤ ‖z τ - w‖ * ‖Nv‖ := by nlinarith
      exact le_of_mul_le_mul_right this hN
    set G : ℝ → ℝ := fun τ => ‖z τ‖ - rE (Real.arccos ((z τ).re / ‖z τ‖)) with hG
    have hzc : Continuous z := by simp only [hz]; fun_prop
    have hGc : ContinuousOn G (Icc 0 2) := by
      apply ContinuousOn.sub (continuous_norm.comp hzc).continuousOn
      apply EulerianCert.FourierModes.continuous_rE.comp_continuousOn
      apply Real.continuous_arccos.comp_continuousOn
      apply ContinuousOn.div (Complex.continuous_re.comp hzc).continuousOn
        (continuous_norm.comp hzc).continuousOn
      intro τ hτ; exact norm_ne_zero_iff.2 (hz_ne τ hτ.1)
    have hG0 : G 0 < 0 := by
      have e : z 0 = p := by simp [hz]
      show ‖z 0‖ - rE (Real.arccos ((z 0).re / ‖z 0‖)) < 0
      rw [e, hpdef, gauge_pt hR, rE_arccos t₀ ht₀, norm_pt, abs_of_pos hR]
      linarith
    have hG2 : 0 < G 2 := by
      have hn2 : 2 < ‖z 2‖ := by
        have h1 := dot_le_norm (z 2) n hnorm_n
        have e : dot (z 2) n = dot (z 2) Nv / ‖Nv‖ := by
          simp only [hn, dot, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
            Complex.ofReal_im]; field_simp; ring
        rw [e, hdot_z, add_div, mul_div_assoc, div_self hN.ne', mul_one] at h1
        have : 0 < R h t₀ ^ 2 / ‖Nv‖ := by positivity
        linarith
      simp only [hG]
      have := EulerianCert.HausdorffMinimax.rE_le_one (Real.arccos ((z 2).re / ‖z 2‖))
      linarith
    obtain ⟨τ1, hτ1, hGz⟩ := intermediate_value_Icc (show (0 : ℝ) ≤ 2 by norm_num) hGc
      ⟨hG0.le, hG2.le⟩
    have hmem : z τ1 ∈ ΓE := mem_ΓE_of_gauge (hz_ne τ1 hτ1.1) (by simp only [hG] at hGz; linarith)
    refine ⟨z τ1, hmem, ?_⟩
    have hdist : dist p (z τ1) = τ1 := by
      simp only [hz]
      rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_mul, hnorm_n, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hτ1.1]
    rw [hdist]
    have : τ1 ≤ infDist (z τ1) (Ω h) :=
      (le_infDist (Ω_nonempty h)).2 (fun w hw => hsep τ1 hτ1.1 w hw)
    exact (this.trans (le_Q hmem h)).trans (le_max_right _ _)

/-! ### Eq. (73) -/

/-- **Eq. (73)**: `d_H(Γ_E, Γ_h) = max{h, Q(h)}` for `h ≥ 0`. -/
theorem hausdorff_envelope {h : ℝ} (hh : 0 ≤ h) :
    hausdorffDist ΓE (Γh h) = max h (Q h) := by
  apply le_antisymm
  · exact hausdorffDist_le_of_mem_dist (le_max_of_le_left hh)
      (fun p hp => eulerian_point_close hh hp)
      (fun p hp => let ⟨y, hy, hd⟩ := limacon_point_close hh hp; ⟨y, hy, hd⟩)
  · apply max_le
    · -- the point `(1 + h, 0)` of `Γ_h` is at distance `≥ h` from `Γ_E`
      have hz : pt (1 + h) 0 ∈ Γh h := ⟨0, zero_mem_angle, by
        show pt (c + h + m * Real.cos 0) 0 = pt (1 + h) 0
        rw [Real.cos_zero, mul_one]; congr 1; simp only [c, m]; ring⟩
      have hle := infDist_le_hausdorffDist_of_mem hz (fin_ab' m (c + h))
      rw [hausdorffDist_comm] at hle
      have : h ≤ infDist (pt (1 + h) 0) ΓE := by
        rw [le_infDist ΓE_nonempty]
        intro p hp
        have := norm_sub_norm_le (pt (1 + h) 0) p
        rw [← dist_eq_norm, norm_pt, abs_of_nonneg (by linarith)] at this
        linarith [norm_le_one hp]
      linarith
    · exact Q_le fun p hp =>
        (infDist_le_infDist_of_subset (Γh_subset_Ω hh) (Γ_nonempty m (c + h))).trans
          (infDist_le_hausdorffDist_of_mem hp (fin_ab m (c + h)))

/-- **Attainment**: `d_H(Γ_E, Γ_{m, c+h*}) = h*`. -/
theorem hausdorff_attained : hausdorffDist ΓE (Γ m (c + hstar)) = hstar := by
  have := hausdorff_envelope (h := hstar) hstar_mem.1.le
  rw [Q_hstar, max_self] at this
  exact this

lemma admissible_optimum : 0 < m ∧ 2 * m ≤ c + hstar := by
  refine ⟨EulerianCert.Limacon.m_pos, ?_⟩
  have := EulerianCert.Limacon.c_sub_two_m_pos
  linarith [hstar_mem.1]

/-- **Theorem 3.13, minimum**: `h*` is the least Hausdorff distance between `Γ_E` and an admissible
limaçon (`b ≥ 2a > 0`), attained at `a_H = m`, `b_H = c + h*` (Eq. (69)). -/
theorem hausdorff_isLeast :
    IsLeast {D | ∃ a b : ℝ, 0 < a ∧ 2 * a ≤ b ∧ D = hausdorffDist ΓE (Γ a b)} hstar := by
  refine ⟨⟨m, c + hstar, admissible_optimum.1, admissible_optimum.2, hausdorff_attained.symm⟩, ?_⟩
  rintro _ ⟨a, b, ha, hab, rfl⟩
  exact hausdorff_lower a b ha hab

end EulerianCert.HausdorffAttain
