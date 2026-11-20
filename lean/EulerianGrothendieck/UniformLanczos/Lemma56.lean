import UniformLanczos.Joined
import Bridge.Saddle.LogConcave

/-!
# Manuscript 12, Lemma 5.6 (interior part) for the actual `φ_M = -(1/M) log g_M`

Source: frozen `12.tex`, label `lem:ul-spline`.  With `g_M(x) = M w_M(M x)` one has
`φ_M'(x) = -w_M'(M x) / w_M(M x)` on `(-1/2, 1/2)`.  From the strict interior log-concavity of the
cardinal B-spline proved in `Bridge.Saddle.LogConcave` (no premise from Floater's paper) we get,
for every `M ≥ 3`:

* `lemma_5_6_strictMono`: `φ_M'` is strictly increasing on `(-1/2, 1/2)`;
* `lemma_5_6_continuousOn`: `φ_M'` is continuous on `(-1/2, 1/2)`;
* `deriv_φM_odd`, `deriv_φM_zero`: `φ_M'` is odd and `φ_M'(0) = 0` (already for `M ≥ 2`);
* `lemma_5_6_hc`, `lemma_5_6_hm`: the same facts in the form of the hypotheses `hc`, `hm` of
  `UniformLanczos.Profile.lemma_5_7a`.

The blow-up of `φ_M'` at the endpoint `1/2` (last sentence of Lemma 5.6) is not in this file.
-/

open Set Filter Topology
open EulerianBridge.Saddle

namespace UniformLanczos.Lemma56

/-- `φ_M'(x) = -w_M'(M x) / w_M(M x)`, for `M ≥ 3` (the version in `Bridge.Saddle.Corollary` is
stated for `M ≥ 4`). -/
theorem hasDerivAt_φM_three {M : ℕ} (hM : 3 ≤ M) {x : ℝ} (hw : 0 < w M (M * x)) :
    HasDerivAt (φM M) (-(deriv (w M) (M * x) / w M (M * x))) x := by
  have hMpos : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hg : gM M x ≠ 0 := by unfold gM; positivity
  have h := ((hasDerivAt_gM hM x).log hg).const_mul (-(1 / (M:ℝ)))
  unfold φM
  convert h using 1
  unfold gM
  field_simp

theorem mem_scaled {M : ℕ} (hM : 1 ≤ M) {x : ℝ} (hx : x ∈ Ioo (-(1/2):ℝ) (1/2)) :
    (M:ℝ) * x ∈ Ioo (-((M:ℝ) / 2)) ((M:ℝ) / 2) := by
  have hMpos : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have h1 : 0 < (M:ℝ) * (x + 1/2) := mul_pos hMpos (by linarith [hx.1])
  have h2 : 0 < (M:ℝ) * (1/2 - x) := mul_pos hMpos (by linarith [hx.2])
  constructor
  · nlinarith [h1]
  · nlinarith [h2]

theorem w_scaled_pos {M : ℕ} (hM : 2 ≤ M) {x : ℝ} (hx : x ∈ Ioo (-(1/2):ℝ) (1/2)) :
    0 < w M (M * x) :=
  w_pos M hM _ (abs_lt.mpr (mem_scaled (M := M) (by omega) hx))

/-- **Lemma 5.6**, strict monotonicity: for `M ≥ 3`, `φ_M'` is strictly increasing on
`(-1/2, 1/2)`. -/
theorem lemma_5_6_strictMono {M : ℕ} (hM : 3 ≤ M) :
    StrictMonoOn (deriv (φM M)) (Ioo (-(1/2):ℝ) (1/2)) := by
  have hMpos : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hM2 : 2 ≤ M := by omega
  have hM1 : 1 ≤ M := by omega
  intro x hx y hy hxy
  rw [(hasDerivAt_φM_three hM (w_scaled_pos hM2 hx)).deriv,
    (hasDerivAt_φM_three hM (w_scaled_pos hM2 hy)).deriv]
  have hlt : deriv (w M) (M * y) / w M (M * y) < deriv (w M) (M * x) / w M (M * x) :=
    w_logDeriv_strictAnti M hM (mem_scaled hM1 hx) (mem_scaled hM1 hy)
      (mul_lt_mul_of_pos_left hxy hMpos)
  linarith

/-- **Lemma 5.6**, continuity: for `M ≥ 3`, `φ_M'` is continuous on `(-1/2, 1/2)`. -/
theorem lemma_5_6_continuousOn {M : ℕ} (hM : 3 ≤ M) :
    ContinuousOn (deriv (φM M)) (Ioo (-(1/2):ℝ) (1/2)) := by
  have hM2 : 2 ≤ M := by omega
  have h1 : Continuous fun x : ℝ => deriv (w M) (M * x) :=
    (continuous_deriv_w_three hM).comp (continuous_const.mul continuous_id)
  have h2 : Continuous fun x : ℝ => w M (M * x) :=
    (w_continuous M hM2).comp (continuous_const.mul continuous_id)
  have hc : ContinuousOn (fun x : ℝ => -(deriv (w M) (M * x) / w M (M * x)))
      (Ioo (-(1/2):ℝ) (1/2)) := fun x hx =>
    ((h1.continuousAt.div h2.continuousAt (w_scaled_pos hM2 hx).ne').neg).continuousWithinAt
  exact hc.congr (fun x hx => (hasDerivAt_φM_three hM (w_scaled_pos hM2 hx)).deriv)

theorem φM_even {M : ℕ} (hM : 2 ≤ M) (x : ℝ) : φM M (-x) = φM M x := by
  have he : (M:ℝ) * -x = -((M:ℝ) * x) := by ring
  unfold φM gM
  rw [he, UniformLanczos.Joined.w_even M hM]

/-- `φ_M'` is odd. -/
theorem deriv_φM_odd {M : ℕ} (hM : 2 ≤ M) (x : ℝ) : deriv (φM M) (-x) = -deriv (φM M) x := by
  have heq : (fun y => φM M (-y)) = φM M := funext (φM_even hM)
  have h1 : deriv (fun y => φM M (-y)) x = -deriv (φM M) (-x) := deriv_comp_neg (φM M) x
  rw [heq] at h1
  linarith

theorem deriv_φM_zero {M : ℕ} (hM : 2 ≤ M) : deriv (φM M) 0 = 0 := by
  have h := deriv_φM_odd hM 0
  rw [neg_zero] at h
  linarith

/-- Hypothesis `hc` of `UniformLanczos.Profile.lemma_5_7a` for `G = φ_M'`, `M ≥ 3`. -/
theorem lemma_5_6_hc {M : ℕ} (hM : 3 ≤ M) :
    ∀ b : ℝ, b < 1 / 2 → ContinuousOn (deriv (φM M)) (Icc 0 b) := fun b hb =>
  (lemma_5_6_continuousOn hM).mono fun y hy => ⟨by linarith [hy.1], lt_of_le_of_lt hy.2 hb⟩

/-- Hypothesis `hm` of `UniformLanczos.Profile.lemma_5_7a` for `G = φ_M'`, `M ≥ 3`. -/
theorem lemma_5_6_hm {M : ℕ} (hM : 3 ≤ M) :
    StrictMonoOn (deriv (φM M)) (Ico 0 (1 / 2)) :=
  (lemma_5_6_strictMono hM).mono fun y hy => ⟨by linarith [hy.1], hy.2⟩

end UniformLanczos.Lemma56

#print axioms UniformLanczos.Lemma56.lemma_5_6_strictMono
#print axioms UniformLanczos.Lemma56.lemma_5_6_continuousOn
#print axioms UniformLanczos.Lemma56.deriv_φM_odd
#print axioms UniformLanczos.Lemma56.deriv_φM_zero
#print axioms UniformLanczos.Lemma56.lemma_5_6_hc
#print axioms UniformLanczos.Lemma56.lemma_5_6_hm
