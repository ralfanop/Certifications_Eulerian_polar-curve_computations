import CriticalWindowVacuumIdentification
import EulerianGrothendieck.VectorOptimum

/-! M12 revised 25 November, cor:cross-Q12, eq:cross-Qlim and eq:cross-Qzero.
Use the actual orthogonal Fock vacuum and actual bilinear matrix quotient.
The compact-uniform theorem is a transfer from the precise normalized norm
statement of the separate uniform-convergence module, not a claim that it
has already passed CI. -/
namespace M12CriticalCorrelation

open Filter MeasureTheory ProbabilityTheory
open scoped Topology
set_option maxHeartbeats 2000000
open M12CriticalPointwise M12CriticalDCT M12CriticalVacuum
open EulerianGrothendieck EulerianGrothendieck.Fock

noncomputable abbrev Fcrit := M12CriticalDCT.F

noncomputable def P (M : ℕ) (lam : ℝ) : ℝ :=
  fockVacuumProbability ((1/12+lam*scale M^2)*(M:ℝ)) M

noncomputable def B (M : ℕ) (lam : ℝ) : ℝ := (scale M)⁻¹ * P M lam

noncomputable def Q (M : ℕ) (lam : ℝ) : ℝ :=
  bilinearRatio (Real.sqrt (P M lam)) eulerianPhase

noncomputable def C : ℝ := 1/(2*(Real.pi^2+1))

theorem C_pos : 0 < C := by unfold C; positivity

theorem scale_mul_B (M : ℕ) (hM : 0 < M) (lam : ℝ) :
    scale M * B M lam = P M lam := by
  unfold B
  rw [← mul_assoc, mul_inv_cancel₀ (scale_pos M hM).ne', one_mul]

theorem actual_ratio_limit :
    Tendsto (fun p : ℝ => (bilinearRatio (Real.sqrt p) eulerianPhase-1)/p)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 C) := by
  have h := eulerian_variational_ratio_limit
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono
    (show nhdsWithin (0:ℝ) (Set.Ioi 0) ≤ 𝓝 0 from inf_le_left)] with p hp hp1
  rw [bilinearRatio_eulerian p (le_of_lt hp) hp1.le, frameGrothendieckRatio_eq_variational]

theorem Fcrit_antitone : Antitone Fcrit := by
  intro a b hab
  unfold Fcrit M12CriticalDCT.F
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply integral_mono_ae (profile_integrable b) (profile_integrable a)
  apply Eventually.of_forall
  intro u
  unfold profile
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_right hab (sq_nonneg u)
  linarith

section Probability
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable (U : ℕ → Ω → ℝ) (hU : ∀ i, Measurable (U i))
variable (hind : iIndepFun U μ) (hlaw : ∀ i, μ.map (U i) = V033.UniformSum.uniformLaw)
include hU hind hlaw

theorem B_tendsto (lam : ℝ) : Tendsto (fun M : ℕ => B M lam) atTop (𝓝 ((Fcrit lam)⁻¹)) :=
  actual_vacuum_critical_limit U hU hind hlaw lam

theorem P_tendsto (lam : ℝ) : Tendsto (fun M : ℕ => P M lam) atTop (𝓝 0) := by
  have h := scale_tendsto.mul (B_tendsto U hU hind hlaw lam)
  rw [zero_mul] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with M hM
  exact scale_mul_B M (by omega) lam

theorem eventual_P_pos (lam : ℝ) : ∀ᶠ M : ℕ in atTop, 0 < P M lam := by
  have hpos : 0 < (Fcrit lam)⁻¹ := inv_pos.mpr (F_pos lam)
  filter_upwards [eventually_ge_atTop 1,
    (B_tendsto U hU hind hlaw lam).eventually (lt_mem_nhds hpos)] with M hm hb
  rw [← scale_mul_B M (by omega) lam]
  exact mul_pos (scale_pos M (by omega)) hb

theorem actual_correlation_limit (lam : ℝ) :
    Tendsto (fun M : ℕ => (scale M)⁻¹ * (Q M lam-1)) atTop
      (𝓝 (1/(2*(Real.pi^2+1)*Fcrit lam))) := by
  have hp : Tendsto (fun M : ℕ => P M lam) atTop (nhdsWithin 0 (Set.Ioi 0)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨P_tendsto U hU hind hlaw lam, eventual_P_pos U hU hind hlaw lam⟩
  have ht := (actual_ratio_limit.comp hp).mul (B_tendsto U hU hind hlaw lam)
  have hcoeff : C*(Fcrit lam)⁻¹ = 1/(2*(Real.pi^2+1)*Fcrit lam) := by
    unfold C
    rw [one_div, ← mul_inv, ← one_div]
  rw [hcoeff] at ht
  apply ht.congr'
  filter_upwards [eventual_P_pos U hU hind hlaw lam] with M hM
  change (Q M lam-1)/P M lam * ((scale M)⁻¹ * P M lam) = _
  field_simp [hM.ne'] <;> ring

theorem actual_correlation_at_critical :
    Tendsto (fun M : ℕ => (scale M)⁻¹ *
      (bilinearRatio (Real.sqrt (fockVacuumProbability ((M:ℝ)/12) M)) eulerianPhase-1))
      atTop (𝓝 (2*Real.sqrt Real.pi/
        ((Real.pi^2+1)*(40:ℝ)^(1/4:ℝ)*Real.Gamma (1/4)))) := by
  have h := actual_correlation_limit U hU hind hlaw 0
  have hF : Fcrit 0 = (40:ℝ)^(1/4:ℝ)*Real.Gamma (1/4)/(4*Real.sqrt Real.pi) := F_zero
  rw [hF] at h
  have hcoeff : 1/(2*(Real.pi^2+1)*
      ((40:ℝ)^(1/4:ℝ)*Real.Gamma (1/4)/(4*Real.sqrt Real.pi))) =
      2*Real.sqrt Real.pi/((Real.pi^2+1)*(40:ℝ)^(1/4:ℝ)*Real.Gamma (1/4)) := by
    have hp : Real.pi^2+1 ≠ 0 := by positivity
    have hs : Real.sqrt Real.pi ≠ 0 := by positivity
    have h40 : (40:ℝ)^(1/4:ℝ) ≠ 0 := by positivity
    have hg : Real.Gamma (1/4:ℝ) ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
    field_simp [hp,hs,h40,hg] <;> ring
  rw [hcoeff] at h
  apply h.congr'
  exact Eventually.of_forall fun M => by
    have ha : (1/12+0*scale M^2)*(M:ℝ) = (M:ℝ)/12 := by ring
    simp only [Q,P,ha]

/- The exact premise delivered by PR #609. It is isolated to permit an
independent audit of the subsequent uniform inversion and correlation transfer. -/
omit hU hind hlaw in
def UniformNorm : Prop :=
  ∀ L : ℝ, 0 ≤ L → ∀ eps : ℝ, 0 < eps →
    ∀ᶠ M : ℕ in atTop, ∀ lam : ℝ, |lam| ≤ L →
      |scale M * M12CriticalAssembly.originalFockNorm M
        ((1/12+lam*scale M^2)*(M:ℝ))-Fcrit lam| < eps

theorem uniform_vacuum_of_norm (hnorm : UniformNorm) (L : ℝ) (hL : 0 ≤ L)
    (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ M : ℕ in atTop, ∀ lam : ℝ, |lam| ≤ L →
      0 < P M lam ∧ |B M lam-(Fcrit lam)⁻¹| < eps := by
  let m := Fcrit L
  have hm : 0 < m := F_pos L
  let d := min (m/2) (eps*(m*m/2))
  have hd : 0 < d := lt_min (by positivity) (by positivity)
  filter_upwards [hnorm L hL d hd, eventual_scale_conditions L hL] with M hN hS
  rcases hS with ⟨hM,hsmall,_⟩
  intro lam hlam
  let a := scale M * M12CriticalAssembly.originalFockNorm M
        ((1/12+lam*scale M^2)*(M:ℝ))
  let f := Fcrit lam
  have hf : m ≤ f := Fcrit_antitone (le_trans (le_abs_self lam) hlam)
  have hdiff : |a-f| < d := hN lam hlam
  have ha : m/2 < a := by
    have h := (abs_lt.mp hdiff).1
    have hd' : d ≤ m/2 := min_le_left _ _
    linarith
  have ha0 : 0 < a := by linarith
  have hf0 : 0 < f := lt_of_lt_of_le hm hf
  have hc : 0 < (1/12:ℝ)+lam*scale M^2 := by
    have hl : -L ≤ lam := by linarith [neg_abs_le lam]
    nlinarith only [hsmall,mul_le_mul_of_nonneg_right hl (sq_nonneg (scale M))]
  have hα : 0 < (1/12+lam*scale M^2)*(M:ℝ) :=
    mul_pos hc (by exact_mod_cast hM)
  have hB : B M lam = a⁻¹ := by
    unfold B P a
    rw [vacuum_eq_original_inv U hU hind hlaw M hα, mul_inv_rev, mul_comm]
  have hp : 0 < P M lam := by
    rw [← scale_mul_B M hM lam,hB]
    exact mul_pos (scale_pos M hM) (inv_pos.mpr ha0)
  refine ⟨hp,?_⟩
  rw [hB]
  change |a⁻¹-f⁻¹| < eps
  have he : a⁻¹-f⁻¹ = (f-a)/(a*f) := by field_simp [ha0.ne',hf0.ne'] <;> ring
  rw [he,abs_div,abs_of_pos (mul_pos ha0 hf0),abs_sub_comm]
  apply (div_lt_iff₀ (mul_pos ha0 hf0)).mpr
  have hprod : m*m/2 ≤ a*f := by
    have hh := mul_le_mul ha.le hf hm.le ha0.le
    nlinarith only [hh]
  exact lt_of_lt_of_le hdiff ((min_le_right _ _).trans
    (mul_le_mul_of_nonneg_left hprod heps.le))

/-- Compact-uniform transfer to the actual finite-order matrix ratio. -/
theorem uniform_correlation_of_norm (hnorm : UniformNorm) (L : ℝ) (hL : 0 ≤ L)
    (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ M : ℕ in atTop, ∀ lam : ℝ, |lam| ≤ L →
      |(scale M)⁻¹ * (Q M lam-1)-C*(Fcrit lam)⁻¹| < eps := by
  let T := (Fcrit L)⁻¹+1
  have hT : 0 < T := by dsimp [T]; have h := inv_pos.mpr (F_pos L); linarith
  have hCp := C_pos
  obtain ⟨delta,hdelta,hRatio⟩ :=
    (Metric.tendsto_nhdsWithin_nhds.mp actual_ratio_limit) (eps/(2*T)) (by positivity)
  have hscale : Tendsto (fun M : ℕ => scale M*T) atTop (𝓝 0) := by
    simpa using scale_tendsto.mul_const T
  have hd : 0 < min delta 1 := lt_min hdelta (by norm_num)
  let e := min 1 (eps/(2*C))
  have he : 0 < e := lt_min (by norm_num) (by positivity)
  filter_upwards [eventually_ge_atTop 1, uniform_vacuum_of_norm U hU hind hlaw hnorm L hL e he,
    hscale.eventually (gt_mem_nhds hd)] with M hM hV hS
  intro lam hlam
  obtain ⟨hp,hB⟩ := hV lam hlam
  have hm : 0 < Fcrit L := F_pos L
  have hf : Fcrit L ≤ Fcrit lam := Fcrit_antitone (le_trans (le_abs_self lam) hlam)
  have hInv : (Fcrit lam)⁻¹ ≤ (Fcrit L)⁻¹ := by simpa only [one_div] using one_div_le_one_div_of_le hm hf
  have hB1 : B M lam ≤ T := by
    have hh := (abs_lt.mp hB).2
    have he1 : e ≤ 1 := min_le_left _ _
    dsimp [T]
    linarith
  have hB0 : 0 ≤ B M lam := by
    unfold B
    exact mul_nonneg (inv_nonneg.mpr (scale_pos M (by omega)).le) hp.le
  have hpdelta : P M lam < delta := by
    rw [← scale_mul_B M (by omega) lam]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hB1 (scale_pos M (by omega)).le)
      (lt_of_lt_of_le hS (min_le_left _ _))
  have hR := hRatio (show P M lam ∈ Set.Ioi (0:ℝ) from hp)
    (by rw [Real.dist_eq,sub_zero,abs_of_pos hp]; exact hpdelta)
  rw [Real.dist_eq] at hR
  change |(Q M lam-1)/P M lam-C| < eps/(2*T) at hR
  have hEq : (scale M)⁻¹*(Q M lam-1) = ((Q M lam-1)/P M lam)*B M lam := by
    unfold B
    field_simp [hp.ne'] <;> ring
  rw [hEq]
  have hSplit : (Q M lam-1)/P M lam*B M lam-C*(Fcrit lam)⁻¹ =
      ((Q M lam-1)/P M lam-C)*B M lam+C*(B M lam-(Fcrit lam)⁻¹) := by ring
  rw [hSplit]
  calc
    _ ≤ |((Q M lam-1)/P M lam-C)*B M lam| + |C*(B M lam-(Fcrit lam)⁻¹)| := abs_add_le _ _
    _ = |(Q M lam-1)/P M lam-C| * B M lam + C * |B M lam-(Fcrit lam)⁻¹| := by
      rw [abs_mul,abs_mul,abs_of_nonneg hB0,abs_of_pos hCp]
    _ < (eps/(2*T))*T+C*(eps/(2*C)) := by
      apply add_lt_add_of_le_of_lt
      · exact mul_le_mul hR.le hB1 hB0 (by positivity)
      · exact mul_lt_mul_of_pos_left (lt_of_lt_of_le hB (min_le_right _ _)) hCp
    _ = eps := by field_simp [hT.ne',hCp.ne'] <;> ring

end Probability
end M12CriticalCorrelation

#print axioms M12CriticalCorrelation.C_pos
#print axioms M12CriticalCorrelation.scale_mul_B
#print axioms M12CriticalCorrelation.actual_ratio_limit
#print axioms M12CriticalCorrelation.Fcrit_antitone
#print axioms M12CriticalCorrelation.B_tendsto
#print axioms M12CriticalCorrelation.P_tendsto
#print axioms M12CriticalCorrelation.eventual_P_pos
#print axioms M12CriticalCorrelation.actual_correlation_limit
#print axioms M12CriticalCorrelation.actual_correlation_at_critical
#print axioms M12CriticalCorrelation.uniform_vacuum_of_norm
#print axioms M12CriticalCorrelation.uniform_correlation_of_norm
