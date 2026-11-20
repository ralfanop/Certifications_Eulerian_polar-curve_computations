import UniformLanczos.Lemma56Endpoint
import UniformLanczos.ClassQ
import UniformLanczos.MRS

/-!
# Manuscript 12, Lemma 5.8: conditions (ii) and (v) for the actual weights

Source: frozen `12.tex`, label `lem:ul-classQ`, eqs. (ul-QjM), (ul-QjM-part3), (ul-MRSbox).

For `0 < a < 1/2` (to be the root `ξ_{j,M}` of `Φ_M(ξ) = j/M`) let, as in (ul-QjM),
`Q_{j,M}(y) = (M/(2j)) φ_M(a y) - log a/(2j)` on `(-1/(2a), 1/(2a))`.  This file proves, for the
actual `φ_M` and every `M ≥ 3`, `j ≥ 1`:

* `hasDerivAt_QjM`: `Q_{j,M}'(y) = (a M/(2j)) φ_M'(a y)` (ul-QjM-part3);
* `QjM'_strictMonoOn`, `QjM'_continuousOn`: condition (ii) of Definition 1.1 of Levin and
  Lubinsky, *Bounds and Asymptotics for Orthogonal Polynomials for Varying Weights* (2018);
* `mrs_first_actual`: the first Mhaskar–Rakhmanov–Saff equation, in the form
  `(1/π)∫_0^π cos θ Q_{j,M}'(cos θ) dθ = 1`, holds if and only if `Φ_M(a) = j/M` (ul-MRSbox);
* `mrs_actual`: at a root both Mhaskar–Rakhmanov–Saff equations hold; by Remark (b) after
  Definition 1.1 of the same monograph they are equivalent to condition (v).

Conditions (i), (iii), (iv) and the uniformity in `(j, M)` are not in this file.
-/

open Set Filter Topology
open EulerianBridge.Saddle
open UniformLanczos.Lemma56

namespace UniformLanczos.Lemma58

/-- `Q_{j,M}` of (ul-QjM), with a free endpoint parameter `a`. -/
noncomputable def QjM (M j : ℕ) (a y : ℝ) : ℝ :=
  (M:ℝ) / (2 * (j:ℝ)) * φM M (a * y) - Real.log a / (2 * (j:ℝ))

/-- `Q_{j,M}'` of (ul-QjM-part3). -/
noncomputable def QjM' (M j : ℕ) (a y : ℝ) : ℝ :=
  a * (M:ℝ) / (2 * (j:ℝ)) * deriv (φM M) (a * y)

theorem mem_half_of_mem {a y : ℝ} (ha : 0 < a)
    (hy : y ∈ Ioo (-(1 / (2 * a))) (1 / (2 * a))) : a * y ∈ Ioo (-(1/2):ℝ) (1/2) := by
  have hane : a ≠ 0 := ha.ne'
  have h2 : a * (1 / (2 * a)) = 1 / 2 := by field_simp
  have h3 := mul_lt_mul_of_pos_left hy.2 ha
  have h4 := mul_lt_mul_of_pos_left hy.1 ha
  have h5 : a * -(1 / (2 * a)) = -(a * (1 / (2 * a))) := by ring
  constructor
  · linarith
  · linarith

/-- (ul-QjM-part3): the derivative of `Q_{j,M}`. -/
theorem hasDerivAt_QjM {M : ℕ} (j : ℕ) (hM : 3 ≤ M) {a y : ℝ} (ha : 0 < a)
    (hy : y ∈ Ioo (-(1 / (2 * a))) (1 / (2 * a))) :
    HasDerivAt (QjM M j a) (QjM' M j a y) y := by
  have hmem := mem_half_of_mem ha hy
  have hφ : HasDerivAt (φM M) (deriv (φM M) (a * y)) (a * y) :=
    (hasDerivAt_φM_three hM (w_scaled_pos (by omega) hmem)).differentiableAt.hasDerivAt
  unfold QjM QjM'
  exact UniformLanczos.Q_hasDerivAt (M := (M:ℝ)) (N := (j:ℝ)) hφ

/-- Condition (ii), monotonicity: `Q_{j,M}'` is strictly increasing on `(-1/(2a), 1/(2a))`. -/
theorem QjM'_strictMonoOn {M j : ℕ} (hM : 3 ≤ M) (hj : 1 ≤ j) {a : ℝ} (ha : 0 < a) :
    StrictMonoOn (QjM' M j a) (Ioo (-(1 / (2 * a))) (1 / (2 * a))) := by
  have hMpos : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hjpos : (0:ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have himg : (fun y => a * y) '' Ioo (-(1 / (2 * a))) (1 / (2 * a)) ⊆
      Ioo (-(1/2):ℝ) (1/2) := by
    rintro _ ⟨y, hy, rfl⟩
    exact mem_half_of_mem ha hy
  unfold QjM'
  exact UniformLanczos.Qprime_strictMono ha hMpos hjpos ((lemma_5_6_strictMono hM).mono himg)

/-- Condition (ii), continuity: `Q_{j,M}'` is continuous on `(-1/(2a), 1/(2a))`. -/
theorem QjM'_continuousOn {M : ℕ} (j : ℕ) (hM : 3 ≤ M) {a : ℝ} (ha : 0 < a) :
    ContinuousOn (QjM' M j a) (Ioo (-(1 / (2 * a))) (1 / (2 * a))) := by
  unfold QjM'
  exact continuousOn_const.mul ((lemma_5_6_continuousOn hM).comp
    (continuous_const.mul continuous_id).continuousOn (fun _ hy => mem_half_of_mem ha hy))

theorem QjM'_odd {M : ℕ} (j : ℕ) (hM : 2 ≤ M) (a y : ℝ) :
    QjM' M j a (-y) = -QjM' M j a y := by
  have h : a * -y = -(a * y) := by ring
  unfold QjM'
  rw [h, deriv_φM_odd hM]
  ring

/-- `φ_M'` composed with the clamp to `[-b, b]`: for `0 ≤ b < 1/2` a continuous odd function on
the whole line which equals `φ_M'` on `[-b, b]`. -/
noncomputable def clampDeriv (M : ℕ) (b y : ℝ) : ℝ := deriv (φM M) (max (-b) (min b y))

theorem clamp_odd {b : ℝ} (hb0 : 0 ≤ b) (y : ℝ) :
    max (-b) (min b (-y)) = -max (-b) (min b y) := by
  rcases le_total y (-b) with h1 | h1
  · rw [min_eq_left (by linarith : b ≤ -y), max_eq_right (by linarith : -b ≤ b),
      min_eq_right (by linarith : y ≤ b), max_eq_left h1, neg_neg]
  · rcases le_total y b with h2 | h2
    · rw [min_eq_right (by linarith : -y ≤ b), max_eq_right (by linarith : -b ≤ -y),
        min_eq_right h2, max_eq_right h1]
    · rw [min_eq_right (by linarith : -y ≤ b), max_eq_left (by linarith : -y ≤ -b),
        min_eq_left h2, max_eq_right (by linarith : -b ≤ b)]

theorem clampDeriv_continuous {M : ℕ} (hM : 3 ≤ M) {b : ℝ} (hb0 : 0 ≤ b) (hb : b < 1/2) :
    Continuous (clampDeriv M b) := by
  have hmem : ∀ y : ℝ, max (-b) (min b y) ∈ Ioo (-(1/2):ℝ) (1/2) := fun y =>
    ⟨lt_of_lt_of_le (by linarith) (le_max_left _ _),
      max_lt (by linarith) (lt_of_le_of_lt (min_le_left _ _) hb)⟩
  unfold clampDeriv
  exact (lemma_5_6_continuousOn hM).comp_continuous
    (continuous_const.max (continuous_const.min continuous_id)) hmem

theorem clampDeriv_odd {M : ℕ} (hM : 2 ≤ M) {b : ℝ} (hb0 : 0 ≤ b) (y : ℝ) :
    clampDeriv M b (-y) = -clampDeriv M b y := by
  unfold clampDeriv
  rw [clamp_odd hb0, deriv_φM_odd hM]

theorem clampDeriv_eq (M : ℕ) {b u : ℝ} (hu : |u| ≤ b) :
    clampDeriv M b u = deriv (φM M) u := by
  have h1 := abs_le.mp hu
  unfold clampDeriv
  rw [min_eq_right h1.2, max_eq_right h1.1]

/-- (ul-MRSbox): the first Mhaskar–Rakhmanov–Saff equation for `Q_{j,M}` holds if and only if
`Φ_M(a) = j/M`, where `Φ_M = Hint (fun y => y * φ_M'(y))`. -/
theorem mrs_first_actual {M j : ℕ} (hM : 3 ≤ M) (hj : 1 ≤ j) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hb : b < 1/2) :
    (1 / Real.pi) * ∫ θ in (0:ℝ)..Real.pi, Real.cos θ * QjM' M j a (Real.cos θ) = 1 ↔
      Hint (fun y => y * deriv (φM M) y) a = (j:ℝ) / M := by
  have hMpos : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hjpos : (0:ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hb0 : 0 ≤ b := by linarith
  have key := UniformLanczos.mrs_first_iff (clampDeriv_continuous hM hb0 hb)
    (clampDeriv_odd (by omega) hb0) (a := a) hMpos hjpos
  have hL : (∫ θ in (0:ℝ)..Real.pi, Real.cos θ * QjM' M j a (Real.cos θ)) =
      ∫ θ in (0:ℝ)..Real.pi,
        Real.cos θ * (a * (M:ℝ) / (2 * (j:ℝ)) * clampDeriv M b (a * Real.cos θ)) := by
    apply intervalIntegral.integral_congr
    intro θ _
    have hu : |a * Real.cos θ| ≤ b := by
      rw [abs_mul, abs_of_pos ha]
      calc a * |Real.cos θ| ≤ a * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_cos_le_one θ) ha.le
        _ ≤ b := by linarith
    show Real.cos θ * (a * (M:ℝ) / (2 * (j:ℝ)) * deriv (φM M) (a * Real.cos θ)) =
      Real.cos θ * (a * (M:ℝ) / (2 * (j:ℝ)) * clampDeriv M b (a * Real.cos θ))
    rw [clampDeriv_eq M hu]
  have hR : Hint (fun y => y * deriv (φM M) y) a = Hint (fun y => y * clampDeriv M b y) a := by
    unfold Hint
    congr 1
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [uIcc_of_le (by positivity : (0:ℝ) ≤ Real.pi / 2)] at hθ
    have hs0 : 0 ≤ Real.sin θ :=
      Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
    have hu : |a * Real.sin θ| ≤ b := by
      rw [abs_of_nonneg (mul_nonneg ha.le hs0)]
      calc a * Real.sin θ ≤ a * 1 := mul_le_mul_of_nonneg_left (Real.sin_le_one θ) ha.le
        _ ≤ b := by linarith
    show a * Real.sin θ * deriv (φM M) (a * Real.sin θ) =
      a * Real.sin θ * clampDeriv M b (a * Real.sin θ)
    rw [clampDeriv_eq M hu]
  rw [hL, hR]
  exact key

/-- At a root `a` of `Φ_M(a) = j/M` both Mhaskar–Rakhmanov–Saff equations hold for `Q_{j,M}`. -/
theorem mrs_actual {M j : ℕ} (hM : 3 ≤ M) (hj : 1 ≤ j) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hb : b < 1/2) (hroot : Hint (fun y => y * deriv (φM M) y) a = (j:ℝ) / M) :
    (1 / Real.pi) * ∫ θ in (0:ℝ)..Real.pi, Real.cos θ * QjM' M j a (Real.cos θ) = 1 ∧
      ∫ θ in (0:ℝ)..Real.pi, QjM' M j a (Real.cos θ) = 0 :=
  ⟨(mrs_first_actual hM hj ha hab hb).mpr hroot,
    UniformLanczos.mrs_second (Qp := QjM' M j a) (QjM'_odd j (by omega) a)⟩

end UniformLanczos.Lemma58

#print axioms UniformLanczos.Lemma58.hasDerivAt_QjM
#print axioms UniformLanczos.Lemma58.QjM'_strictMonoOn
#print axioms UniformLanczos.Lemma58.QjM'_continuousOn
#print axioms UniformLanczos.Lemma58.mrs_first_actual
#print axioms UniformLanczos.Lemma58.mrs_actual
