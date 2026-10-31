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

/-! ### Uniqueness of the minimiser -/

lemma ΓE_compact : IsCompact ΓE := by
  apply isCompact_Icc.image
  have := EulerianCert.FourierModes.continuous_rE
  fun_prop

lemma Γ_compact (a b : ℝ) : IsCompact (Γ a b) := by
  apply isCompact_Icc.image
  fun_prop

lemma norm_sub_smul_sq (u v : ℂ) (l : ℝ) :
    ‖u - (l : ℂ) * v‖ ^ 2 = ‖u‖ ^ 2 - 2 * l * dot u v + l ^ 2 * ‖v‖ ^ 2 := by
  rw [norm_sq_eq, norm_sq_eq, norm_sq_eq]
  simp only [dot, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- Variational inequality for a nearest point in the convex body `Ω_h`. -/
theorem variational {h : ℝ} (hh : 0 ≤ h) {p y : ℂ} (hy : y ∈ Ω h)
    (hd : dist p y = infDist p (Ω h)) {w : ℂ} (hw : w ∈ Ω h) : dot (p - y) (w - y) ≤ 0 := by
  by_contra hpos; push Not at hpos
  set d := dot (p - y) (w - y)
  have hb : 0 < ‖w - y‖ ^ 2 := by
    rcases eq_or_ne (w - y) 0 with e | e
    · exfalso
      have : d = 0 := by simp only [d, e]; simp [dot]
      linarith
    · positivity
  set l := min 1 (d / ‖w - y‖ ^ 2) with hl
  have hl0 : 0 < l := lt_min one_pos (div_pos hpos hb)
  have hl1 : l ≤ 1 := min_le_left _ _
  have hl2 : l * ‖w - y‖ ^ 2 ≤ d := by
    have := min_le_right 1 (d / ‖w - y‖ ^ 2)
    rw [← hl] at this
    calc l * ‖w - y‖ ^ 2 ≤ d / ‖w - y‖ ^ 2 * ‖w - y‖ ^ 2 := by gcongr
      _ = d := div_mul_cancel₀ _ hb.ne'
  have hmem : y + (l : ℂ) * (w - y) ∈ Ω h := by
    have := convex_Ω hh hy hw (sub_nonneg.2 hl1) hl0.le (by ring)
    convert this using 1
    simp only [Complex.real_smul]; push_cast; ring
  have h1 := infDist_le_dist_of_mem (x := p) hmem
  rw [← hd, dist_eq_norm, dist_eq_norm] at h1
  have h2 : ‖p - y‖ ^ 2 ≤ ‖p - (y + (l : ℂ) * (w - y))‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  rw [show p - (y + (l : ℂ) * (w - y)) = (p - y) - (l : ℂ) * (w - y) by ring,
    norm_sub_smul_sq] at h2
  have h3 : 2 * l * d ≤ l * (l * ‖w - y‖ ^ 2) := by nlinarith
  have h4 : 2 * d ≤ l * ‖w - y‖ ^ 2 := by
    have := (mul_le_mul_iff_of_pos_left hl0).1 (by linarith : l * (2 * d) ≤ l * (l * ‖w - y‖ ^ 2))
    exact this
  linarith

/-- Two nearest points of `Ω_h` coincide. -/
theorem nearest_unique {h : ℝ} (hh : 0 ≤ h) {p y w : ℂ} (hy : y ∈ Ω h) (hw : w ∈ Ω h)
    (hdy : dist p y = infDist p (Ω h)) (hdw : dist p w = infDist p (Ω h)) : y = w := by
  have h1 := variational hh hy hdy hw
  have h2 := variational hh hw hdw hy
  have e : dot (p - y) (w - y) + dot (p - w) (y - w) = ‖w - y‖ ^ 2 := by
    rw [norm_sq_eq]; simp only [dot, Complex.sub_re, Complex.sub_im]; ring
  have : ‖w - y‖ ^ 2 ≤ 0 := by linarith
  have : ‖w - y‖ = 0 := by nlinarith [norm_nonneg (w - y)]
  rw [norm_eq_zero, sub_eq_zero] at this
  exact this.symm

/-- A nearest point of `Ω_h` to an exterior point lies on `Γ_h`: its scale factor is `1`. -/
theorem nearest_on_boundary {h : ℝ} (hh : 0 ≤ h) {p : ℂ} {t s : ℝ} (ht : t ∈ Icc (-π) π)
    (hs : s ∈ Icc (0 : ℝ) 1) (hpos : 0 < infDist p (Ω h))
    (hd : dist p (pt (s * R h t) t) = infDist p (Ω h)) : s = 1 := by
  by_contra hs1
  have hlt : s < 1 := lt_of_le_of_ne hs.2 hs1
  set y := pt (s * R h t) t
  set r := ‖p - y‖ with hr
  have hrpos : 0 < r := by rw [hr, ← dist_eq_norm, hd]; exact hpos
  set δ := min ((1 - s) * (q + h)) (r / 2) with hδ
  have hδ0 : 0 < δ := lt_min (mul_pos (by linarith) (by linarith [q_pos])) (by linarith)
  set v : ℂ := ((δ / r : ℝ) : ℂ) * (p - y)
  have hv : ‖v‖ = δ := by
    simp only [v]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hδ0 hrpos), ← hr]
    field_simp
  have hmem := interior_of_lt_one hh ht hs.1 hlt (v := v) (by rw [hv]; exact min_le_left _ _)
  have h1 := infDist_le_dist_of_mem (x := p) hmem
  rw [← hd, dist_eq_norm, dist_eq_norm] at h1
  have e : p - (y + v) = ((1 - δ / r : ℝ) : ℂ) * (p - y) := by simp only [v]; push_cast; ring
  rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs] at h1
  have hδr : δ ≤ r / 2 := min_le_right _ _
  have : 0 ≤ 1 - δ / r := by rw [sub_nonneg, div_le_one hrpos]; linarith
  rw [abs_of_nonneg this, ← hr] at h1
  have : (1 - δ / r) * r = r - δ := by field_simp
  linarith

lemma cos_ne_of_far {h : ℝ} (hh : 0 ≤ h) {θ : ℝ} (hθ : θ ∈ Icc (-π) π)
    (hpos : 0 < infDist (pt (rE θ) θ) (Ω h)) : Real.cos θ ≠ 1 ∧ Real.cos θ ≠ -1 := by
  have inside : ∀ x, (x = 1 ∨ x = -1) → Real.cos θ = x → False := by
    intro x hx hc
    have hf : RadialMinimax.f x = c + m * x := by
      rcases hx with rfl | rfl
      · rw [RadialMinimax.f_one]; simp only [c, m, q]; ring
      · rw [RadialMinimax.f_neg_one]; simp only [c, m]; ring
    have hrE : rE θ = c + m * Real.cos θ := by
      rw [RadialMinimax.rE_eq_f_cos hθ, hc, hf]
    have hmem : pt (rE θ) θ ∈ Ω h := by
      apply mem_Ω_of_le hθ (rE_pos hθ).le
      rw [R_eq hh, hrE]; linarith
    rw [infDist_zero_of_mem hmem] at hpos; exact lt_irrefl _ hpos
  exact ⟨fun hc => inside 1 (Or.inl rfl) hc, fun hc => inside (-1) (Or.inr rfl) hc⟩

lemma sin_ne_zero_of_cos {θ : ℝ} (h1 : Real.cos θ ≠ 1) (h2 : Real.cos θ ≠ -1) :
    Real.sin θ ≠ 0 := by
  intro hs
  have := Real.sin_sq_add_cos_sq θ
  rw [hs] at this
  have : (Real.cos θ - 1) * (Real.cos θ + 1) = 0 := by nlinarith
  rcases mul_eq_zero.1 this with e | e
  · exact h1 (by linarith)
  · exact h2 (by linarith)

/-- The nearest boundary point to an off-axis Eulerian point is off the axis. -/
theorem nearest_off_axis {h : ℝ} (hh : 0 ≤ h) {p : ℂ} (hp : p.im ≠ 0) {t : ℝ}
    (ht : t ∈ Icc (-π) π) (hd : dist p (pt (R h t) t) = infDist p (Ω h)) : Real.sin t ≠ 0 := by
  intro hst
  set z := pt (R h t) t
  have hz : z ∈ Ω h := mem_Ω_of_le ht (R_pos hh t).le le_rfl
  set φ : ℝ → ℝ := fun τ => dot (p - z) (pt (R h τ) τ - z)
  have hle : ∀ τ, φ τ ≤ 0 := fun τ =>
    variational hh hz hd (Γh_subset_Ω hh (γh_mem hh τ))
  have hzero : φ t = 0 := by simp [φ, z, dot]
  have hmax : IsLocalMax φ t :=
    Filter.Eventually.of_forall (fun τ => by rw [hzero]; exact hle τ)
  have hderiv : HasDerivAt φ ((p - z).re * ((-m * Real.sin t) * Real.cos t - R h t * Real.sin t) +
      (p - z).im * ((-m * Real.sin t) * Real.sin t + R h t * Real.cos t)) t := by
    have hR : ∀ τ, R h τ = c + h + m * Real.cos τ := R_eq hh
    have e : φ = fun τ => (p - z).re * ((c + h + m * Real.cos τ) * Real.cos τ - z.re) +
        (p - z).im * ((c + h + m * Real.cos τ) * Real.sin τ - z.im) := by
      ext τ; simp only [φ, dot, Complex.sub_re, Complex.sub_im, pt_re, pt_im, hR]
    rw [e]
    have hRd : HasDerivAt (fun τ => c + h + m * Real.cos τ) (-m * Real.sin t) t := by
      have := ((Real.hasDerivAt_cos t).const_mul m).const_add (c + h)
      convert this using 1; ring
    have h1 := ((hRd.mul (Real.hasDerivAt_cos t)).sub_const z.re).const_mul (p - z).re
    have h2 := ((hRd.mul (Real.hasDerivAt_sin t)).sub_const z.im).const_mul (p - z).im
    convert h1.add h2 using 1
    rw [hR]; ring
  have h0 := hmax.hasDerivAt_eq_zero hderiv
  rw [hst] at h0
  have hc : Real.cos t ≠ 0 := by
    intro hc; have := Real.sin_sq_add_cos_sq t; rw [hst, hc] at this; norm_num at this
  have hRp := R_pos hh t
  have him : (p - z).im = 0 := by
    have : (p - z).im * (R h t * Real.cos t) = 0 := by linarith
    rcases mul_eq_zero.1 this with e | e
    · exact e
    · exfalso; exact mul_ne_zero hRp.ne' hc e
  have hzim : z.im = 0 := by simp only [z, pt_im, hst, mul_zero]
  simp only [Complex.sub_im, hzim, sub_zero] at him
  exact hp him

/-- **Theorem 3.13, uniqueness**: an admissible limaçon at Hausdorff distance `h*` from `Γ_E` is
`a = m`, `b = c + h*`. -/
theorem minimiser_unique (a b : ℝ) (ha : 0 < a) (hab : 2 * a ≤ b)
    (hD : hausdorffDist ΓE (Γ a b) = hstar) : a = m ∧ b = c + hstar := by
  obtain ⟨e1, e2⟩ := endpoint_bounds a b ha hab
  rw [hD] at e1 e2
  have hh : 0 ≤ hstar := hstar_mem.1.le
  by_cases heq : b + a = 1 + hstar ∧ b - a = q + hstar
  · exact EulerianCert.Limacon.endpoint_equalities a b hstar heq.1 heq.2
  exfalso
  have hstrict : b + a < 1 + hstar ∨ b - a < q + hstar := by
    by_contra hns; push Not at hns
    exact heq ⟨le_antisymm e1 hns.1, le_antisymm e2 hns.2⟩
  -- an Eulerian point realising `Q(h*) = h*`
  obtain ⟨p, hp, hpmax⟩ := ΓE_compact.exists_isMaxOn ΓE_nonempty
    (continuous_infDist_pt (Ω hstar)).continuousOn
  have hQp : infDist p (Ω hstar) = hstar := by
    apply le_antisymm
    · calc infDist p (Ω hstar) ≤ Q hstar := le_Q hp hstar
        _ = hstar := Q_hstar
    · calc hstar = Q hstar := Q_hstar.symm
        _ ≤ infDist p (Ω hstar) := Q_le fun x hx => by simpa using hpmax hx
  have hpos : 0 < infDist p (Ω hstar) := by rw [hQp]; exact hstar_mem.1
  obtain ⟨θ, hθ, rfl⟩ := hp
  change 0 < infDist (pt (rE θ) θ) (Ω hstar) at hpos
  change infDist (pt (rE θ) θ) (Ω hstar) = hstar at hQp
  obtain ⟨hc1, hc2⟩ := cos_ne_of_far hh hθ hpos
  have hpim : (pt (rE θ) θ).im ≠ 0 := by
    rw [pt_im]; exact mul_ne_zero (rE_pos hθ).ne' (sin_ne_zero_of_cos hc1 hc2)
  -- its nearest point `z` in `Ω_{h*}`: on `Γ_{h*}` and off the axis
  obtain ⟨z, hz, hdz⟩ := (isCompact_Ω hstar).exists_infDist_eq_dist (Ω_nonempty hstar)
    (pt (rE θ) θ)
  obtain ⟨⟨t, s⟩, ⟨ht, hs⟩, rfl⟩ := hz
  simp only at ht hs hdz
  have hs1 := nearest_on_boundary hh ht hs hpos hdz.symm
  rw [hs1, one_mul] at hdz
  have hst := nearest_off_axis hh hpim ht hdz.symm
  -- a nearest point of `Γ_{a,b}`, which lies in `Ω_{h*}` and therefore equals `z`
  obtain ⟨w, hw, hdw⟩ := (Γ_compact a b).exists_infDist_eq_dist (Γ_nonempty a b) (pt (rE θ) θ)
  have hwΩ := Γ_subset_Ω a b hstar ha hab e1 e2 hw
  have hdw' : dist (pt (rE θ) θ) w = infDist (pt (rE θ) θ) (Ω hstar) := by
    apply le_antisymm
    · rw [← hdw, hQp, ← hD]
      exact infDist_le_hausdorffDist_of_mem ⟨θ, hθ, rfl⟩ (fin_ab a b)
    · exact infDist_le_dist_of_mem hwΩ
  have hzw := nearest_unique hh (mem_Ω_of_le ht (R_pos hh t).le le_rfl) hwΩ hdz.symm hdw'
  obtain ⟨t', -, rfl⟩ := hw
  change pt (R hstar t) t = pt (b + a * Real.cos t') t' at hzw
  have hRt := R_pos hh t
  have hb' : 0 < b + a * Real.cos t' := by nlinarith [Real.neg_one_le_cos t']
  have hn := congrArg norm hzw
  rw [norm_pt, norm_pt, abs_of_pos hRt, abs_of_pos hb'] at hn
  have hre := congrArg Complex.re hzw
  rw [pt_re, pt_re, hn] at hre
  have hcos : Real.cos t' = Real.cos t := (mul_left_cancel₀ hb'.ne' hre).symm
  have hcs1 : Real.cos t ≠ 1 := by
    intro e; have := Real.sin_sq_add_cos_sq t; rw [e] at this
    exact hst (by nlinarith)
  have hcs2 : Real.cos t ≠ -1 := by
    intro e; have := Real.sin_sq_add_cos_sq t; rw [e] at this
    exact hst (by nlinarith)
  have hlt := EulerianCert.Limacon.endpoint_containment_strict a b hstar t e1 e2 hstrict hcs1 hcs2
  rw [hcos, R_eq hh] at hn
  linarith

/-! ### `h* < ε_rad`, Eq. (72) -/

open EulerianCert.RadialMinimax (εrad Δ xs)

lemma εrad_pos : 0 < εrad := by simp only [εrad]; linarith [RadialMinimax.Δ_pos]

/-- Every Eulerian point is at distance `< ε_rad` from `Ω_{ε_rad}`. -/
theorem infDist_lt_εrad {θ : ℝ} (hθ : θ ∈ Icc (-π) π) :
    infDist (pt (rE θ) θ) (Ω εrad) < εrad := by
  have hε := εrad_pos
  have hh : (0 : ℝ) ≤ εrad := hε.le
  have hx := RadialMinimax.cos_mem θ
  have hfx : rE θ = RadialMinimax.f (Real.cos θ) := RadialMinimax.rE_eq_f_cos hθ
  have hgap : rE θ - R εrad θ = RadialMinimax.h (Real.cos θ) - εrad := by
    rw [R_eq hh, hfx]; simp only [RadialMinimax.h, RadialMinimax.ℓ]; ring
  have hΔ : Δ = 2 * εrad := by simp only [εrad]; ring
  rcases le_or_gt (rE θ) (R εrad θ) with hin | hout
  · rw [infDist_zero_of_mem (mem_Ω_of_le hθ (rE_pos hθ).le hin)]; exact hε
  have hγ : pt (R εrad θ) θ ∈ Ω εrad := mem_Ω_of_le hθ (R_pos hh θ).le le_rfl
  have hle := RadialMinimax.h_le_Δ hx
  rcases lt_or_eq_of_le hle with hlt | heqΔ
  · calc infDist (pt (rE θ) θ) (Ω εrad) ≤ dist (pt (rE θ) θ) (pt (R εrad θ) θ) :=
          infDist_le_dist_of_mem hγ
      _ = rE θ - R εrad θ := by rw [dist_pt_same, abs_of_pos (by linarith)]
      _ < εrad := by rw [hgap]; linarith
  · -- the alternation angle: the equal-angle displacement is not normal to `Γ_ε`
    have hcx : Real.cos θ = xs := by
      apply RadialMinimax.xs_unique hx
      intro y hy
      show RadialMinimax.h y ≤ RadialMinimax.h (Real.cos θ)
      rw [heqΔ]; exact RadialMinimax.h_le_Δ hy
    have hsin : Real.sin θ ≠ 0 := by
      intro hs
      have := Real.sin_sq_add_cos_sq θ
      rw [hs, hcx] at this
      have hxi := RadialMinimax.xs_interior
      nlinarith [hxi.1, hxi.2]
    set ε := εrad
    set rr := rE θ
    set ψ : ℝ → ℝ := fun τ => (rr * Real.cos θ - (c + ε + m * Real.cos τ) * Real.cos τ) ^ 2 +
      (rr * Real.sin θ - (c + ε + m * Real.cos τ) * Real.sin τ) ^ 2 with hψ
    have hψd : HasDerivAt ψ (2 * m * (rr - R ε θ) * Real.sin θ) θ := by
      have hRd : HasDerivAt (fun τ => c + ε + m * Real.cos τ) (-m * Real.sin θ) θ := by
        have := ((Real.hasDerivAt_cos θ).const_mul m).const_add (c + ε)
        convert this using 1; ring
      have h1 := ((hRd.mul (Real.hasDerivAt_cos θ)).const_sub (rr * Real.cos θ)).pow 2
      have h2 := ((hRd.mul (Real.hasDerivAt_sin θ)).const_sub (rr * Real.sin θ)).pow 2
      convert h1.add h2 using 1
      rw [R_eq hh]
      simp only [Pi.mul_apply, Nat.cast_ofNat]
      have := Real.sin_sq_add_cos_sq θ
      linear_combination (-2 * m * (rr - (c + ε + m * Real.cos θ)) * Real.sin θ) * this
    have hne : 2 * m * (rr - R ε θ) * Real.sin θ ≠ 0 := by
      have := EulerianCert.Limacon.m_pos
      exact mul_ne_zero (mul_ne_zero (by positivity) (by linarith)) hsin
    have hnotmin : ¬ IsLocalMin ψ θ := fun hmin => hne (hmin.hasDerivAt_eq_zero hψd)
    rw [IsLocalMin, IsMinFilter, Filter.not_eventually] at hnotmin
    obtain ⟨τ, hτ⟩ := hnotmin.exists
    push Not at hτ
    have hψθ : ψ θ = (rr - R ε θ) ^ 2 := by
      simp only [hψ, R_eq hh]
      have := Real.sin_sq_add_cos_sq θ
      linear_combination ((rr - (c + ε + m * Real.cos θ)) ^ 2) * this
    have hmemτ : pt (R ε τ) τ ∈ Ω ε := Γh_subset_Ω hh (γh_mem hh τ)
    have hdτ : dist (pt rr θ) (pt (R ε τ) τ) ^ 2 = ψ τ := by
      rw [dist_eq_norm, norm_sq_eq]
      simp only [Complex.sub_re, Complex.sub_im, pt_re, pt_im, hψ, R_eq hh]
    have hgap' : rr - R ε θ = ε := by rw [hgap, heqΔ, hΔ]; ring
    have hlt : dist (pt rr θ) (pt (R ε τ) τ) < ε := by
      have : dist (pt rr θ) (pt (R ε τ) τ) ^ 2 < ε ^ 2 := by
        rw [hdτ]; rw [hψθ, hgap'] at hτ; exact hτ
      exact lt_of_pow_lt_pow_left₀ 2 hh this
    exact lt_of_le_of_lt (infDist_le_dist_of_mem hmemτ) hlt

/-- **Eq. (72)**: `Q(ε_rad) < ε_rad`, hence `h* < ε_rad`. -/
theorem Q_εrad_lt : Q εrad < εrad := by
  obtain ⟨p, hp, hpmax⟩ := ΓE_compact.exists_isMaxOn ΓE_nonempty
    (continuous_infDist_pt (Ω εrad)).continuousOn
  have hQ : Q εrad ≤ infDist p (Ω εrad) := Q_le fun x hx => hpmax hx
  obtain ⟨θ, hθ, rfl⟩ := hp
  exact lt_of_le_of_lt hQ (infDist_lt_εrad hθ)

theorem hstar_lt_εrad : hstar < εrad := hstar_lt εrad Q_εrad_lt

end EulerianCert.HausdorffAttain
