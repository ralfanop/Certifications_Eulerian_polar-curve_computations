/-
# Theorem 3.13 of the V001 manuscript: the scalar balance and the global lower bound

Points of the plane are complex numbers; `pt r t = r e^{it}`.  For `h ∈ ℝ` the filled limaçon
body is (Eq. (65); the radius is clipped at `0` so that `Ω_h` is defined for every real `h`)
  `Ω_h = { s · R_h(t) e^{it} : t ∈ [-π, π], s ∈ [0, 1] }`,  `R_h(t) = max(0, c + h + m cos t)`,
and the exterior-distance function (Eq. (66)) is
  `Q(h) = sup_{p ∈ Γ_E} dist(p, Ω_h)`.
Proved here:
* `Q` is antitone and `1`-Lipschitz (hence continuous): nested bodies, equal-angle comparison;
* `Q(Δ) = 0` (every Eulerian point lies in `Ω_Δ`, because `0 ≤ f − ℓ ≤ Δ`), and `Q(0) > 0`
  (the Eulerian point at the alternation angle `θ*` lies outside the compact `Ω_0`);
* Eq. (67): `Q(h) = h` has exactly one real solution `h*`, and `0 < h* < Δ`;
* **global lower bound, Eqs. (74)–(76)**: for every limaçon `Γ_{a,b}` with `b ≥ 2a > 0`,
  `d_H(Γ_E, Γ_{a,b}) ≥ h*` (the proof uses only norms and the radial containment, no convexity);
* the existing scalar-balance lemmas of `Limacon` (`balance_bracket`, `balance_lt`, …) now apply to
  this concrete `Q`, whose antitonicity was previously a hypothesis.
Not formalised: the upper bound of Eq. (73) (attainment `d_H(Γ_E, Γ_{h*}) = h*`, which needs the
convexity of `Ω_h` and the outward-normal exit argument) and the uniqueness of the minimiser.
-/
import EulerianCert.RadialMinimax
import EulerianCert.SignCriterion
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Order.IntermediateValue

open Real Set Metric

noncomputable section

namespace EulerianCert.HausdorffMinimax

open EulerianCert.Limacon (q c m)
open EulerianCert.RadialMinimax (Δ xs)

local notation "rE" => EulerianCert.FourierModes.rE

def pt (r t : ℝ) : ℂ := (r : ℂ) * Complex.exp ((t : ℂ) * Complex.I)

lemma norm_pt (r t : ℝ) : ‖pt r t‖ = |r| := by
  rw [pt, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

lemma dist_pt (r r' t : ℝ) : dist (pt r t) (pt r' t) = |r - r'| := by
  rw [dist_eq_norm, pt, pt, ← sub_mul, ← Complex.ofReal_sub]
  exact norm_pt (r - r') t

def R (h t : ℝ) : ℝ := max 0 (c + h + m * Real.cos t)

lemma R_nonneg (h t : ℝ) : 0 ≤ R h t := le_max_left _ _

lemma R_mono {h k : ℝ} (hk : h ≤ k) (t : ℝ) : R h t ≤ R k t :=
  max_le_max le_rfl (by linarith)

lemma continuous_R (h : ℝ) : Continuous (R h) := by
  unfold R; fun_prop

def Ω (h : ℝ) : Set ℂ :=
  (fun p : ℝ × ℝ => pt (p.2 * R h p.1) p.1) '' (Icc (-π) π ×ˢ Icc (0 : ℝ) 1)

lemma mem_Ω {h t s : ℝ} (ht : t ∈ Icc (-π) π) (hs : s ∈ Icc (0 : ℝ) 1) :
    pt (s * R h t) t ∈ Ω h := ⟨(t, s), ⟨ht, hs⟩, rfl⟩

lemma pi_mem : π ∈ Icc (-π) π := ⟨by linarith [pi_pos], le_rfl⟩
lemma zero_mem_angle : (0 : ℝ) ∈ Icc (-π) π := ⟨by linarith [pi_pos], pi_pos.le⟩

lemma zero_mem_Ω (h : ℝ) : (0 : ℂ) ∈ Ω h := by
  have := mem_Ω (h := h) zero_mem_angle (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨le_rfl, zero_le_one⟩)
  simpa [pt] using this

lemma Ω_nonempty (h : ℝ) : (Ω h).Nonempty := ⟨0, zero_mem_Ω h⟩

lemma isCompact_Ω (h : ℝ) : IsCompact (Ω h) := by
  apply (isCompact_Icc.prod isCompact_Icc).image
  unfold pt
  have := continuous_R h
  fun_prop

/-- A radial point with radius between `0` and `R h t` lies in `Ω h`. -/
lemma mem_Ω_of_le {h t r : ℝ} (ht : t ∈ Icc (-π) π) (hr0 : 0 ≤ r) (hr : r ≤ R h t) :
    pt r t ∈ Ω h := by
  rcases eq_or_lt_of_le (R_nonneg h t) with h0 | hpos
  · have : r = 0 := le_antisymm (h0 ▸ hr) hr0
    have := mem_Ω (h := h) ht (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨le_rfl, zero_le_one⟩)
    simpa [‹r = 0›] using this
  · have hs : r / R h t ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg hr0 hpos.le, (div_le_one hpos).2 hr⟩
    have := mem_Ω (h := h) ht hs
    rwa [div_mul_cancel₀ _ hpos.ne'] at this

lemma Ω_mono {h k : ℝ} (hk : h ≤ k) : Ω h ⊆ Ω k := by
  rintro _ ⟨⟨t, s⟩, ⟨ht, hs⟩, rfl⟩
  exact mem_Ω_of_le ht (mul_nonneg hs.1 (R_nonneg h t))
    ((mul_le_of_le_one_left (R_nonneg h t) hs.2).trans (R_mono hk t))

/-! ### The Eulerian curve -/

def ΓE : Set ℂ := EulerianCert.polarCurve rE

lemma ΓE_eq : ΓE = (fun θ => pt (rE θ) θ) '' Icc (-π) π := rfl

lemma rE_pos {θ : ℝ} (hθ : θ ∈ Icc (-π) π) : 0 < rE θ := by
  apply sinc_pos; rw [abs_lt]; constructor <;> linarith [hθ.1, hθ.2, pi_pos]

lemma rE_le_one (θ : ℝ) : rE θ ≤ 1 := sinc_le_one _

lemma norm_le_one {p : ℂ} (hp : p ∈ ΓE) : ‖p‖ ≤ 1 := by
  obtain ⟨θ, hθ, rfl⟩ := hp
  show ‖pt (rE θ) θ‖ ≤ 1
  rw [norm_pt, abs_of_pos (rE_pos hθ)]; exact rE_le_one θ

lemma ΓE_nonempty : ΓE.Nonempty := ⟨_, ⟨π, pi_mem, rfl⟩⟩

instance : Nonempty ΓE := ΓE_nonempty.to_subtype

lemma infDist_le_one {p : ℂ} (hp : p ∈ ΓE) (h : ℝ) : infDist p (Ω h) ≤ 1 := by
  calc infDist p (Ω h) ≤ dist p 0 := infDist_le_dist_of_mem (zero_mem_Ω h)
    _ = ‖p‖ := dist_zero_right p
    _ ≤ 1 := norm_le_one hp

/-! ### The exterior-distance function `Q` -/

def Q (h : ℝ) : ℝ := ⨆ p : ΓE, infDist (p : ℂ) (Ω h)

lemma bdd (h : ℝ) : BddAbove (Set.range fun p : ΓE => infDist (p : ℂ) (Ω h)) :=
  ⟨1, by rintro _ ⟨p, rfl⟩; exact infDist_le_one p.2 h⟩

lemma le_Q {p : ℂ} (hp : p ∈ ΓE) (h : ℝ) : infDist p (Ω h) ≤ Q h :=
  le_ciSup (f := fun p : ΓE => infDist (p : ℂ) (Ω h)) (bdd h) ⟨p, hp⟩

lemma Q_le {h D : ℝ} (H : ∀ p ∈ ΓE, infDist p (Ω h) ≤ D) : Q h ≤ D :=
  ciSup_le fun p => H p.1 p.2

/-- `Q` is antitone (nested bodies). -/
theorem Q_antitone : Antitone Q := fun h k hk =>
  Q_le fun p hp => (infDist_le_infDist_of_subset (Ω_mono hk) (Ω_nonempty h)).trans (le_Q hp h)

/-- Equal-angle comparison: `dist(p, Ω_h) ≤ dist(p, Ω_k) + |h − k|`. -/
lemma infDist_lip (p : ℂ) (h k : ℝ) : infDist p (Ω h) ≤ infDist p (Ω k) + |h - k| := by
  have : infDist p (Ω h) - |h - k| ≤ infDist p (Ω k) := by
    rw [le_infDist (Ω_nonempty k)]
    rintro _ ⟨⟨t, s⟩, ⟨ht, hs⟩, rfl⟩
    have hmem := mem_Ω (h := h) ht hs
    have h1 := infDist_le_dist_of_mem (x := p) hmem
    have h2 : dist (pt (s * R h t) t) (pt (s * R k t) t) ≤ |h - k| := by
      rw [dist_pt, ← mul_sub, abs_mul, abs_of_nonneg hs.1]
      have : |R h t - R k t| ≤ |h - k| := by
        unfold R
        rw [max_comm 0, max_comm 0]
        refine (abs_max_sub_max_le_abs _ _ _).trans (le_of_eq ?_)
        congr 1; ring
      calc s * |R h t - R k t| ≤ 1 * |h - k| :=
            mul_le_mul hs.2 this (abs_nonneg _) zero_le_one
        _ = |h - k| := one_mul _
    have h3 := dist_triangle p (pt (s * R k t) t) (pt (s * R h t) t)
    rw [dist_comm (pt (s * R k t) t)] at h3
    simp only
    linarith
  linarith

/-- `Q` is `1`-Lipschitz, hence continuous. -/
theorem Q_lip (h k : ℝ) : Q h ≤ Q k + |h - k| :=
  Q_le fun p hp => (infDist_lip p h k).trans (by linarith [le_Q hp k])

theorem continuous_Q : Continuous Q := by
  apply LipschitzWith.continuous (K := 1)
  apply LipschitzWith.of_dist_le_mul
  intro h k
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul, abs_le]
  constructor
  · have := Q_lip k h; rw [abs_sub_comm] at this; linarith
  · have := Q_lip h k; linarith

/-! ### `Q(Δ) = 0` and `Q(0) > 0` -/

lemma rE_eq_f_cos {θ : ℝ} (hθ : θ ∈ Icc (-π) π) : rE θ = RadialMinimax.f (Real.cos θ) :=
  RadialMinimax.rE_eq_f_cos hθ

theorem Q_Δ : Q Δ = 0 := by
  apply le_antisymm _ (le_trans infDist_nonneg (le_Q ⟨π, pi_mem, rfl⟩ Δ))
  apply Q_le
  rintro _ ⟨θ, hθ, rfl⟩
  apply le_of_eq
  apply infDist_zero_of_mem
  have hle := RadialMinimax.h_le_Δ (RadialMinimax.cos_mem θ)
  simp only [RadialMinimax.h, RadialMinimax.ℓ] at hle
  rw [← rE_eq_f_cos hθ] at hle
  apply mem_Ω_of_le hθ (rE_pos hθ).le
  unfold R
  exact le_max_of_le_right (by linarith)

lemma arccos_xs_mem : Real.arccos xs ∈ Ioo 0 π :=
  ⟨Real.arccos_pos.2 RadialMinimax.xs_interior.2, Real.arccos_lt_pi.2 RadialMinimax.xs_interior.1⟩

/-- The Eulerian point at the alternation angle is outside `Ω_0`. -/
lemma pstar_not_mem : pt (rE (Real.arccos xs)) (Real.arccos xs) ∉ Ω 0 := by
  set θ := Real.arccos xs with hθdef
  have hθ := arccos_xs_mem
  have hθI : θ ∈ Icc (-π) π := ⟨by linarith [hθ.1, pi_pos], hθ.2.le⟩
  have hval : rE θ = c + m * Real.cos θ + Δ := by
    have e : RadialMinimax.f xs = rE θ := rfl
    have hcos : Real.cos θ = xs :=
      Real.cos_arccos RadialMinimax.xs_mem.1 RadialMinimax.xs_mem.2
    have : Δ = RadialMinimax.f xs - (c + m * xs) := rfl
    rw [this, e, hcos]; ring
  rintro ⟨⟨t, s⟩, ⟨ht, hs⟩, heq⟩
  simp only at heq ht hs
  have hrpos := rE_pos hθI
  -- equal norms
  have hn := congrArg norm heq
  rw [norm_pt, norm_pt, abs_of_nonneg (mul_nonneg hs.1 (R_nonneg 0 t)),
    abs_of_pos hrpos] at hn
  -- equal arguments
  have hexp : Complex.exp ((t : ℂ) * Complex.I) = Complex.exp ((θ : ℂ) * Complex.I) := by
    have h' : ((s * R 0 t : ℝ) : ℂ) * Complex.exp ((t : ℂ) * Complex.I) =
        ((s * R 0 t : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
      calc ((s * R 0 t : ℝ) : ℂ) * Complex.exp ((t : ℂ) * Complex.I) = pt (s * R 0 t) t := rfl
        _ = pt (rE θ) θ := heq
        _ = _ := by rw [pt, ← hn]
    have hne : ((s * R 0 t : ℝ) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero, hn]; exact hrpos.ne'
    exact mul_left_cancel₀ hne h'
  obtain ⟨n, hn'⟩ := Complex.exp_eq_exp_iff_exists_int.1 hexp
  have him := congrArg Complex.im hn'
  simp at him
  -- him : t = θ + n * (2 * π)
  have hn0 : n = 0 := by
    have h1 : (n : ℝ) * (2 * π) < π := by linarith [ht.2, hθ.1]
    have h2 : -(2 * π) < (n : ℝ) * (2 * π) := by linarith [ht.1, hθ.2]
    have h3 : (n : ℝ) < 1 / 2 := by nlinarith [pi_pos]
    have h4 : (-1 : ℝ) < n := by nlinarith [pi_pos]
    have : n < 1 := by exact_mod_cast (show (n : ℝ) < 1 by linarith)
    have : -1 < n := by exact_mod_cast h4
    omega
  rw [hn0] at him
  simp at him
  rw [him] at hn
  have hR : R 0 θ = c + m * Real.cos θ := by
    have := EulerianCert.Limacon.m_pos
    have hc : c - m = q := by simp only [c, m]; ring
    have hq : 0 < q := by simp only [q]; positivity
    have hnn : 0 ≤ c + 0 + m * Real.cos θ := by nlinarith [Real.neg_one_le_cos θ]
    unfold R
    rw [max_eq_right hnn]; ring
  rw [hR] at hn
  have := mul_le_of_le_one_left (show 0 ≤ c + m * Real.cos θ by rw [← hR]; exact R_nonneg 0 θ) hs.2
  linarith [RadialMinimax.Δ_pos]

theorem Q_zero_pos : 0 < Q 0 := by
  have hθ := arccos_xs_mem
  have hθI : Real.arccos xs ∈ Icc (-π) π := ⟨by linarith [hθ.1, pi_pos], hθ.2.le⟩
  have hpos := ((isCompact_Ω 0).isClosed.notMem_iff_infDist_pos (Ω_nonempty 0)).1 pstar_not_mem
  exact lt_of_lt_of_le hpos (le_Q ⟨_, hθI, rfl⟩ 0)

/-! ### The balance point `h*`, Eq. (67) -/

theorem exists_balance : ∃ hs ∈ Ioo 0 Δ, Q hs = hs := by
  have hΔ := RadialMinimax.Δ_pos
  have hcont : ContinuousOn (fun h => Q h - h) (Icc 0 Δ) :=
    (continuous_Q.sub continuous_id).continuousOn
  have hivt := intermediate_value_Icc' hΔ.le hcont
  have h0 : (0 : ℝ) ∈ Icc (Q Δ - Δ) (Q 0 - 0) := by
    rw [Q_Δ]; constructor <;> linarith [Q_zero_pos]
  obtain ⟨hs, hsI, hsv⟩ := hivt h0
  simp only at hsv
  refine ⟨hs, ⟨lt_of_le_of_ne hsI.1 ?_, lt_of_le_of_ne hsI.2 ?_⟩, by linarith⟩
  · rintro rfl; linarith [Q_zero_pos]
  · rintro rfl; rw [Q_Δ] at hsv; linarith

def hstar : ℝ := exists_balance.choose
lemma hstar_mem : hstar ∈ Ioo 0 Δ := exists_balance.choose_spec.1
lemma Q_hstar : Q hstar = hstar := exists_balance.choose_spec.2

/-- **Eq. (67)**: `Q(h) = h` has exactly one solution, `h*`, and `0 < h* < Δ`. -/
theorem balance_unique (h : ℝ) (e : Q h = h) : h = hstar :=
  EulerianCert.Limacon.balance_unique Q Q_antitone h hstar e Q_hstar

/-! ### Global lower bound, Eqs. (74)–(76) -/

/-- The limaçon `Γ_{a,b}` (Eq. (68)). -/
def Γ (a b : ℝ) : Set ℂ := EulerianCert.polarCurve (fun t => b + a * Real.cos t)

lemma Γ_eq (a b : ℝ) : Γ a b = (fun t => pt (b + a * Real.cos t) t) '' Icc (-π) π := rfl

lemma Γ_nonempty (a b : ℝ) : (Γ a b).Nonempty := ⟨_, ⟨0, zero_mem_angle, rfl⟩⟩

lemma ΓE_bounded : Bornology.IsBounded ΓE := by
  rw [isBounded_iff_forall_norm_le]; exact ⟨1, fun p hp => norm_le_one hp⟩

lemma Γ_bounded (a b : ℝ) : Bornology.IsBounded (Γ a b) := by
  rw [isBounded_iff_forall_norm_le]
  refine ⟨|b| + |a|, ?_⟩
  rintro _ ⟨t, -, rfl⟩
  show ‖pt (b + a * Real.cos t) t‖ ≤ _
  rw [norm_pt]
  calc |b + a * Real.cos t| ≤ |b| + |a * Real.cos t| := abs_add_le _ _
    _ ≤ |b| + |a| := by
      rw [abs_mul]; gcongr
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one t)

lemma fin_ab (a b : ℝ) : hausdorffEDist ΓE (Γ a b) ≠ ⊤ :=
  hausdorffEDist_ne_top_of_nonempty_of_bounded ΓE_nonempty (Γ_nonempty a b) ΓE_bounded
    (Γ_bounded a b)

lemma fin_ab' (a b : ℝ) : hausdorffEDist (Γ a b) ΓE ≠ ⊤ := by
  rw [hausdorffEDist_comm]; exact fin_ab a b

/-- **Eq. (74)**: the endpoint bounds `b + a ≤ 1 + D`, `b − a ≤ q + D`, `D = d_H(Γ_E, Γ_{a,b})`. -/
theorem endpoint_bounds (a b : ℝ) (ha : 0 < a) (hab : 2 * a ≤ b) :
    b + a ≤ 1 + hausdorffDist ΓE (Γ a b) ∧ b - a ≤ q + hausdorffDist ΓE (Γ a b) := by
  set D := hausdorffDist ΓE (Γ a b) with hD
  have hrad : ∀ t, b - a ≤ b + a * Real.cos t := fun t => by
    nlinarith [Real.neg_one_le_cos t]
  constructor
  · have hz : pt (b + a) 0 ∈ Γ a b := ⟨0, zero_mem_angle, by
      show pt (b + a * Real.cos 0) 0 = pt (b + a) 0
      rw [Real.cos_zero, mul_one]⟩
    have hle := infDist_le_hausdorffDist_of_mem hz (fin_ab' a b)
    rw [hausdorffDist_comm] at hle
    have : b + a - 1 ≤ infDist (pt (b + a) 0) ΓE := by
      rw [le_infDist ΓE_nonempty]
      intro p hp
      have := norm_sub_norm_le (pt (b + a) 0) p
      rw [← dist_eq_norm, norm_pt, abs_of_nonneg (by linarith)] at this
      linarith [norm_le_one hp]
    linarith
  · have hp0 : pt (2 / π) π ∈ ΓE := ⟨π, pi_mem, by
      show pt (rE π) π = pt (2 / π) π
      rw [EulerianCert.FourierModes.rE_pi]⟩
    have hle := infDist_le_hausdorffDist_of_mem hp0 (fin_ab a b)
    have : b - a - q ≤ infDist (pt (2 / π) π) (Γ a b) := by
      rw [le_infDist (Γ_nonempty a b)]
      rintro _ ⟨t, -, rfl⟩
      show b - a - q ≤ dist (pt (2 / π) π) (pt (b + a * Real.cos t) t)
      have := norm_sub_norm_le (pt (b + a * Real.cos t) t) (pt (2 / π) π)
      rw [← dist_eq_norm, dist_comm, norm_pt, norm_pt,
        abs_of_nonneg (by linarith [hrad t]), abs_of_pos (by positivity)] at this
      have := hrad t
      simp only [q]
      linarith
    linarith

/-- **Eq. (75)**: radial containment `Γ_{a,b} ⊆ Ω_D`. -/
theorem Γ_subset_Ω (a b D : ℝ) (ha : 0 < a) (hab : 2 * a ≤ b) (e1 : b + a ≤ 1 + D)
    (e2 : b - a ≤ q + D) : Γ a b ⊆ Ω D := by
  rintro _ ⟨t, ht, rfl⟩
  apply mem_Ω_of_le ht (by nlinarith [Real.neg_one_le_cos t])
  unfold R
  exact le_max_of_le_right (EulerianCert.Limacon.endpoint_containment a b D t e1 e2)

/-- **Theorem 3.13, global lower bound**: every admissible limaçon (`b ≥ 2a > 0`) satisfies
`d_H(Γ_E, Γ_{a,b}) ≥ h*` (Eq. (76)). -/
theorem hausdorff_lower (a b : ℝ) (ha : 0 < a) (hab : 2 * a ≤ b) :
    hstar ≤ hausdorffDist ΓE (Γ a b) := by
  obtain ⟨e1, e2⟩ := endpoint_bounds a b ha hab
  have hsub := Γ_subset_Ω a b _ ha hab e1 e2
  have hQD : Q (hausdorffDist ΓE (Γ a b)) ≤ hausdorffDist ΓE (Γ a b) := Q_le fun p hp =>
    (infDist_le_infDist_of_subset hsub (Γ_nonempty a b)).trans
      (infDist_le_hausdorffDist_of_mem hp (fin_ab a b))
  exact EulerianCert.Limacon.balance_lower Q Q_antitone hstar _ Q_hstar hQD

/-- The logic of the 80-digit certificate (Eq. (70)) for the concrete `Q`:
`Q(L) > L` and `Q(U) < U` imply `L < h* < U`. -/
theorem hstar_bracket (L U : ℝ) (hL : L < Q L) (hU : Q U < U) : L < hstar ∧ hstar < U :=
  EulerianCert.Limacon.balance_bracket Q Q_antitone hstar L U Q_hstar hL hU

/-- Eq. (72), logic: `Q(ε_rad) < ε_rad` implies `h* < ε_rad`. -/
theorem hstar_lt (ε : ℝ) (hε : Q ε < ε) : hstar < ε :=
  EulerianCert.Limacon.balance_lt Q Q_antitone hstar ε Q_hstar hε

end EulerianCert.HausdorffMinimax
