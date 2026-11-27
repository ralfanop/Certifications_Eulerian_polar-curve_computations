import EulerianGrothendieck.JacobiStrongCompressions20261127
import EulerianGrothendieck.JacobiPropagation20261127
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! Strong compression limits for the actual operator exponential and
its Duhamel integral. Counting-measure dominated convergence handles
the exponential series. Lebesgue dominated convergence then handles
both the interval integral and the Fourier integral. -/
set_option maxHeartbeats 2000000
noncomputable section
open Filter Set MeasureTheory NormedSpace
open scoped Topology ENNReal InnerProductSpace
namespace M12SmoothCompressions
open M12BilateralJacobi M12JacobiFrechet M12DKBilateral M12StrongCompressions
open M12JacobiPropagation M12JacobiFourier

theorem count_integral_eq_tsum (f : ℕ → H) (hf : Summable (fun n => ‖f n‖)) :
    (∫ n, f n ∂Measure.count) = ∑' n, f n := by
  rw [integral_countable (integrable_count_iff.mpr hf)]
  simp

theorem tsum_dominated (F : ℕ → ℕ → H) (f : ℕ → H) (g : ℕ → ℝ)
    (hg : Summable g) (hg0 : ∀ n, 0 ≤ g n)
    (hb : ∀ N n, ‖F N n‖ ≤ g n) (hf : ∀ n, ‖f n‖ ≤ g n)
    (hlim : ∀ n, Tendsto (fun N => F N n) atTop (𝓝 (f n))) :
    Tendsto (fun N => ∑' n, F N n) atTop (𝓝 (∑' n, f n)) := by
  have hg' : Integrable g Measure.count := integrable_count_iff.mpr
    (by simpa only [Real.norm_eq_abs,abs_of_nonneg (hg0 _)] using hg)
  have hFN : ∀ N, Summable (fun n => ‖F N n‖) :=
    fun N => Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (hb N) hg
  have hfn : Summable (fun n => ‖f n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hf hg
  have h := tendsto_integral_of_dominated_convergence (μ := Measure.count) g
    (fun N => (integrable_count_iff.mpr (hFN N)).aestronglyMeasurable)
    hg' (fun N => Eventually.of_forall (hb N)) (Eventually.of_forall hlim)
  simpa only [count_integral_eq_tsum _ hfn, count_integral_eq_tsum _ (hFN _)] using h

def A (u : Bonds) (t : ℝ) : Op := ((t:ℂ)*Complex.I) • J u
def E (u : Bonds) (t : ℝ) : Op := exp (A u t)

theorem generator_power_strong (u : Bonds) (t : ℝ) (n : ℕ) (x : H) :
    Tendsto (fun N : ℕ => (A (cut u N) t)^n x) atTop (𝓝 ((A u t)^n x)) := by
  unfold A
  simp only [smul_pow,ContinuousLinearMap.smul_apply]
  exact (cutoff_power_strong u n x).const_smul (((t:ℂ)*Complex.I)^n)

theorem exp_apply_series (B : Op) (x : H) :
    exp B x = ∑' n : ℕ, ((n.factorial:ℂ)⁻¹) • (B^n) x := by
  let L : Op →L[ℂ] H := ContinuousLinearMap.apply ℂ H x
  change L (exp B) = _
  rw [NormedSpace.exp_eq_tsum ℂ,
    ContinuousLinearMap.map_tsum _ (NormedSpace.expSeries_summable' (𝕂 := ℂ) B)]
  simp only [map_smul]
  rfl

theorem cutoff_exp_strong (u : Bonds) (t : ℝ) (x : H) :
    Tendsto (fun N : ℕ => E (cut u N) t x) atTop (𝓝 (E u t x)) := by
  let F : ℕ → ℕ → H := fun N n => ((n.factorial:ℂ)⁻¹) • (A (cut u N) t)^n x
  let f : ℕ → H := fun n => ((n.factorial:ℂ)⁻¹) • (A u t)^n x
  let g : ℕ → ℝ := fun n => ((n.factorial:ℝ)⁻¹)*|t|^n*‖x‖
  have hg : Summable g := (exp_real_summable |t|).mul_right ‖x‖
  have hb (v : Bonds) (n : ℕ) :
      ‖((n.factorial:ℂ)⁻¹) • (A v t)^n x‖ ≤ g n := by
    rw [norm_smul,norm_inv,Complex.norm_natCast]
    calc
      _ ≤ ((n.factorial:ℝ)⁻¹)*(‖(A v t)^n‖*‖x‖) :=
        mul_le_mul_of_nonneg_left ((A v t)^n).le_opNorm x (by positivity)
      _ ≤ ((n.factorial:ℝ)⁻¹)*(|t|^n*‖x‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (generator_power_norm v t n) (norm_nonneg x)) (by positivity)
      _ = g n := by dsimp [g]; ring
  have ht := tsum_dominated F f g hg (fun n => by dsimp [g]; positivity)
    (fun N n => hb (cut u N) n) (hb u)
    (fun n => (generator_power_strong u t n x).const_smul ((n.factorial:ℂ)⁻¹))
  simpa only [E,exp_apply_series,F,f] using ht

theorem phase_norm (u : Bonds) (t : ℝ) : ‖E u t‖ = 1 :=
  CStarRing.norm_of_mem_unitary (jacobi_unitary u t)

def density (u : Bonds) (t s : ℝ) (m : ℤ) : Op :=
  E u ((1-s)*t) * bond m * E u (s*t)

theorem density_strong (u : Bonds) (t s : ℝ) (m : ℤ) (x : H) :
    Tendsto (fun N : ℕ => density (cut u N) t s m x) atTop (𝓝 (density u t s m x)) := by
  have h₁ := cutoff_exp_strong u (s*t) x
  have h₂ := (bond m).continuous.continuousAt.tendsto.comp h₁
  have h₃ := strong_apply (fun N => E (cut u N) ((1-s)*t)) (E u ((1-s)*t))
    (fun N => bond m (E (cut u N) (s*t) x)) (bond m (E u (s*t) x))
    (cutoff_exp_strong u ((1-s)*t)) 1 zero_le_one
    (fun N => le_of_eq (phase_norm _ _)) h₂
  exact h₃

theorem density_norm (u : Bonds) (t s : ℝ) (m : ℤ) : ‖density u t s m‖ ≤ 2 := by
  unfold density
  calc
    _ ≤ ‖E u ((1-s)*t)*bond m‖*‖E u (s*t)‖ := norm_mul_le _ _
    _ ≤ (‖E u ((1-s)*t)‖*‖bond m‖)*‖E u (s*t)‖ :=
      mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ = ‖bond m‖ := by rw [phase_norm,phase_norm,one_mul,mul_one]
    _ ≤ 2 := bond_norm_le m

theorem density_joint_cont (u : Bonds) (m : ℤ) :
    Continuous (fun p : ℝ × ℝ => density u p.1 p.2 m) := by
  have hE : Continuous (E u) := by
    unfold E A
    apply (show Continuous (exp : Op → Op) from M12ExpFrechet.exp_cont).comp
    exact (Complex.continuous_ofReal.mul (continuous_const : Continuous (fun _ : ℝ => Complex.I))).smul continuous_const
  unfold density
  exact (((hE.comp ((continuous_const.sub continuous_snd).mul continuous_fst)).mul continuous_const).mul
    (hE.comp (continuous_snd.mul continuous_fst)))

def D (u : Bonds) (t : ℝ) (m : ℤ) : Op :=
  ∫ s in (0:ℝ)..1, density u t s m

theorem integrated_density_norm (u : Bonds) (t : ℝ) (m : ℤ) : ‖D u t m‖ ≤ 2 := by
  unfold D
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := 1) (C := 2) (f := fun s => density u t s m)
    (fun s _ => density_norm u t s m)

theorem integrated_density_strong (u : Bonds) (t : ℝ) (m : ℤ) (x : H) :
    Tendsto (fun N : ℕ => D (cut u N) t m x) atTop (𝓝 (D u t m x)) := by
  let L : Op →L[ℂ] H := ContinuousLinearMap.apply ℂ H x
  have hi (v : Bonds) : IntervalIntegrable (fun s : ℝ => density v t s m) volume 0 1 :=
    ((density_joint_cont v m).comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 1
  have he (v : Bonds) : D v t m x = ∫ s in Set.Ioc 0 1, density v t s m x := by
    change L (∫ s in (0:ℝ)..1, density v t s m) = _
    rw [← L.intervalIntegral_comp_comm (hi v),intervalIntegral.integral_of_le zero_le_one]
    rfl
  simp only [he]
  apply tendsto_integral_of_dominated_convergence (fun _ : ℝ => 2*‖x‖)
  · intro N
    exact (L.continuous.comp ((density_joint_cont (cut u N) m).comp
      (continuous_const.prodMk continuous_id))).aestronglyMeasurable
  · exact integrable_const _
  · intro N
    filter_upwards [] with s
    exact ((density (cut u N) t s m).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (density_norm _ _ _ _) (norm_nonneg _))
  · exact Eventually.of_forall fun s => density_strong u t s m x

/-- Strong convergence of the literal Fourier-Duhamel integrals,
with only the scalar Fourier density and first moment as inputs. -/
theorem fourier_derivative_strong (u : Bonds) (w : ℝ → ℂ) (m : ℤ) (x : H)
    (hw : AEStronglyMeasurable w volume)
    (hm : Integrable (fun t : ℝ => ‖w t‖*|t|)) :
    Tendsto (fun N : ℕ => ∫ t : ℝ, (w t*((t:ℂ)*Complex.I)) • D (cut u N) t m x)
      atTop (𝓝 (∫ t : ℝ, (w t*((t:ℂ)*Complex.I)) • D u t m x)) := by
  have hC (v : Bonds) : Continuous (fun t : ℝ => D v t m) := by
    unfold D
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact density_joint_cont v m
  have hw' : AEStronglyMeasurable (fun t : ℝ => w t*((t:ℂ)*Complex.I)) volume :=
    hw.mul (Complex.continuous_ofReal.mul continuous_const).aestronglyMeasurable
  apply tendsto_integral_of_dominated_convergence (fun t : ℝ => (2*‖x‖)*(‖w t‖*|t|))
  · intro N
    exact hw'.smul (((ContinuousLinearMap.apply ℂ H x).continuous.comp
      (hC (cut u N))).aestronglyMeasurable)
  · exact hm.const_mul _
  · intro N
    filter_upwards [] with t
    rw [norm_smul,norm_mul,norm_mul,Complex.norm_real,Complex.norm_I,mul_one,Real.norm_eq_abs]
    have h := ((D (cut u N) t m).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (integrated_density_norm _ _ _) (norm_nonneg _))
    calc
      _ ≤ (‖w t‖*|t|)*(2*‖x‖) :=
        mul_le_mul_of_nonneg_left h (mul_nonneg (norm_nonneg _) (abs_nonneg _))
      _ = _ := by ring
  · exact Eventually.of_forall fun t =>
      (integrated_density_strong u t m x).const_smul (w t*((t:ℂ)*Complex.I))

end M12SmoothCompressions
#print axioms M12SmoothCompressions.count_integral_eq_tsum
#print axioms M12SmoothCompressions.tsum_dominated
#print axioms M12SmoothCompressions.generator_power_strong
#print axioms M12SmoothCompressions.exp_apply_series
#print axioms M12SmoothCompressions.cutoff_exp_strong
#print axioms M12SmoothCompressions.phase_norm
#print axioms M12SmoothCompressions.density_strong
#print axioms M12SmoothCompressions.density_norm
#print axioms M12SmoothCompressions.density_joint_cont
#print axioms M12SmoothCompressions.integrated_density_norm
#print axioms M12SmoothCompressions.integrated_density_strong
#print axioms M12SmoothCompressions.fourier_derivative_strong
