import EulerianGrothendieck.JacobiSmoothCompressions20261127
import EulerianGrothendieck.JacobiSchwartzFourier20261127
import Mathlib.Analysis.Complex.RealDeriv

/-! M12 (182): derive the scalar divided difference from the same
angular-frequency Fourier density used by the literal bilateral
Duhamel integral; close the passage from finite spectral Gram forms
to the actual bilateral real kernel. The identification of the finite
matrix eigendecomposition with its Fourier-Duhamel entries is explicit
in the remaining spectral representation premise. -/
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory NormedSpace Set Filter Finset
open scoped SchwartzMap Topology ContDiff ENNReal
namespace M12DKFourierBridge
open M12BilateralJacobi M12DKBilateral M12SchwartzFourier

def phase (t x : ℝ) : ℂ := Complex.exp (((t:ℂ)*Complex.I)*(x:ℂ))

theorem phase_norm (t x : ℝ) : ‖phase t x‖ = 1 := by
  unfold phase
  rw [Complex.norm_exp]
  simp [Complex.mul_re,Complex.mul_im]

theorem phase_derivative (t x : ℝ) :
    HasDerivAt (phase t) (((t:ℂ)*Complex.I)*phase t x) x := by
  have h := (Complex.hasDerivAt_exp (((t:ℂ)*Complex.I)*(x:ℂ))).comp (x:ℂ)
    ((hasDerivAt_id (x:ℂ)).const_mul ((t:ℂ)*Complex.I))
  have h' := h.comp_ofReal (z := x)
  simpa [phase,mul_comm] using h'

theorem scalar_derivative (f : 𝓢(ℝ,ℂ)) (x : ℝ) :
    HasDerivAt (fun y : ℝ => f y)
      (∫ t : ℝ, weight f t*((t:ℂ)*Complex.I)*phase t x) x := by
  let F := fun (y t : ℝ) => weight f t*phase t y
  let F' := fun (y t : ℝ) => weight f t*((t:ℂ)*Complex.I)*phase t y
  have hc (y : ℝ) : Continuous (fun t : ℝ => phase t y) := by
    unfold phase
    exact Complex.continuous_exp.comp ((Complex.continuous_ofReal.mul continuous_const).mul continuous_const)
  have hF (y : ℝ) : Continuous (F y) := (weight_continuous f).mul (hc y)
  have hF' (y : ℝ) : Continuous (F' y) :=
    ((weight_continuous f).mul (Complex.continuous_ofReal.mul continuous_const)).mul (hc y)
  have hi : Integrable (F x) := by
    apply (weight f).integrable.norm.mono' (hF x).aestronglyMeasurable
    filter_upwards [] with t
    change ‖weight f t*phase t x‖ ≤ ‖weight f t‖
    rw [norm_mul,phase_norm,mul_one]
  have hm : Integrable (fun t : ℝ => ‖weight f t‖*|t|) := by
    simpa using weight_moment f 0
  have hb (t y : ℝ) : ‖F' y t‖ ≤ ‖weight f t‖*|t| := by
    dsimp [F']
    rw [norm_mul,norm_mul,norm_mul,Complex.norm_real,Complex.norm_I,mul_one,phase_norm,mul_one,Real.norm_eq_abs]
  have hd (t y : ℝ) : HasDerivAt (fun a => F a t) (F' y t) y := by
    simpa [F,F',mul_assoc] using (phase_derivative t y).const_mul (weight f t)
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := (Set.univ : Set ℝ)) (F := F) (F' := F') (x₀ := x)
    (bound := fun t => ‖weight f t‖*|t|)
    univ_mem (Eventually.of_forall fun y => (hF y).aestronglyMeasurable)
    hi (hF' x).aestronglyMeasurable
    (Eventually.of_forall fun t y _ => hb t y) hm
    (Eventually.of_forall fun t y _ => hd t y)).2
  have he : (fun y : ℝ => ∫ t, F y t) = fun y => f y := by
    funext y
    exact (scalar_inversion f y).symm
  rw [he] at h
  exact h

def dd (f fp : ℝ → ℝ) (a b : ℝ) : ℝ :=
  if a=b then fp a else (f a-f b)/(a-b)

theorem dividedDifference_nonneg (f fp : ℝ → ℝ)
    (hmono : MonotoneOn f (Icc (-1:ℝ) 1))
    (hfp : ∀ a ∈ Icc (-1:ℝ) 1, 0 ≤ fp a)
    {a b : ℝ} (ha : a ∈ Icc (-1:ℝ) 1) (hb : b ∈ Icc (-1:ℝ) 1) :
    0 ≤ dd f fp a b := by
  unfold dd
  split_ifs with h
  · exact hfp a ha
  · rcases le_total a b with hab|hba
    · exact div_nonneg_of_nonpos (sub_nonpos.mpr (hmono ha hb hab)) (sub_nonpos.mpr hab)
    · exact div_nonneg (sub_nonneg.mpr (hmono hb ha hba)) (sub_nonneg.mpr hba)

def scalarDK (g : 𝓢(ℝ,ℂ)) (a b : ℝ) : ℂ :=
  ∫ t : ℝ, weight g t*((t:ℂ)*Complex.I) *
    (∫ s in (0:ℝ)..1, phase t ((1-s)*a+s*b))

theorem scalar_DK_diag (g : 𝓢(ℝ,ℂ)) (a : ℝ) :
    scalarDK g a a = deriv (fun x : ℝ => g x) a := by
  unfold scalarDK
  rw [(scalar_derivative g a).deriv]
  apply integral_congr_ae
  filter_upwards [] with t
  have he : (fun s : ℝ => phase t ((1-s)*a+s*a)) = fun _ => phase t a := by
    funext s
    congr 1
    ring
  rw [he]
  simp

theorem scalar_DK_offdiag (g : 𝓢(ℝ,ℂ)) (a b : ℝ) (hab : a ≠ b) :
    scalarDK g a b = (g a-g b)/((a:ℂ)-(b:ℂ)) := by
  have hne : (b:ℂ)-(a:ℂ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr (Ne.symm hab)
  have hFTC (t : ℝ) :
      ((t:ℂ)*Complex.I)* (∫ s in (0:ℝ)..1, phase t ((1-s)*a+s*b)) *
        ((b:ℂ)-(a:ℂ)) = phase t b-phase t a := by
    let p := fun s : ℝ => (1-s)*a+s*b
    have hp (s : ℝ) : HasDerivAt p (b-a) s := by
      have h := (((hasDerivAt_const s (1:ℝ)).sub (hasDerivAt_id' s)).mul_const a).add
        ((hasDerivAt_id' s).mul_const b)
      convert h using 1 <;> simp [p] <;> ring
    have hd (s : ℝ) : HasDerivAt (fun s => phase t (p s))
        ((((t:ℂ)*Complex.I)*phase t (p s))*((b:ℂ)-(a:ℂ))) s := by
      have h := (phase_derivative t (p s)).scomp s (hp s)
      convert h using 1 <;> simp [Complex.real_smul] <;> ring
    have hc : Continuous (fun s => phase t (p s)) :=
      (continuous_iff_continuousAt.mpr fun s => (phase_derivative t s).continuousAt).comp
        (((continuous_const.sub continuous_id).mul continuous_const).add (continuous_id.mul continuous_const))
    have hi : IntervalIntegrable (fun s => (((t:ℂ)*Complex.I)*phase t (p s))*((b:ℂ)-(a:ℂ))) volume 0 1 :=
      ((continuous_const.mul hc).mul continuous_const).intervalIntegrable _ _
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => hd s) hi
    rw [intervalIntegral.integral_mul_const,intervalIntegral.integral_const_mul] at h
    simpa [p] using h
  have he (t : ℝ) : ((t:ℂ)*Complex.I)*
        (∫ s in (0:ℝ)..1, phase t ((1-s)*a+s*b)) =
        (phase t b-phase t a)/((b:ℂ)-(a:ℂ)) :=
    (eq_div_iff hne).2 (hFTC t)
  unfold scalarDK
  have hi (x : ℝ) : Integrable (fun t : ℝ => weight g t*phase t x) := by
    apply (weight g).integrable.norm.mono'
    · exact ((weight_continuous g).mul (Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.mul continuous_const).mul continuous_const))).aestronglyMeasurable
    · filter_upwards [] with t
      change ‖weight g t*phase t x‖ ≤ ‖weight g t‖
      rw [norm_mul,phase_norm,mul_one]
  calc
    _ = ∫ t : ℝ, (weight g t*phase t b-weight g t*phase t a)/((b:ℂ)-(a:ℂ)) := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [mul_assoc,he]
      ring
    _ = ((∫ t : ℝ, weight g t*phase t b)-(∫ t : ℝ, weight g t*phase t a))/((b:ℂ)-(a:ℂ)) := by
      rw [integral_div,integral_sub (hi b) (hi a)]
    _ = _ := by
      rw [← scalar_inversion g b,← scalar_inversion g a]
      have hn : (a:ℂ)-(b:ℂ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hab
      field_simp <;> ring

theorem scalar_DK (g : 𝓢(ℝ,ℂ)) (f fp : ℝ → ℝ)
    (hf : ∀ x, g x = (f x:ℂ))
    (hfp : ∀ x, deriv (fun y : ℝ => g y) x = (fp x:ℂ)) (a b : ℝ) :
    scalarDK g a b = (dd f fp a b:ℂ) := by
  by_cases h : a=b
  · subst b
    rw [scalar_DK_diag,hfp]
    simp [dd]
  · rw [scalar_DK_offdiag g a b h,hf,hf]
    simp [dd,h,Complex.ofReal_div,Complex.ofReal_sub]

def gram {ι : Type*} [Fintype ι] (c : ι → ℝ) (v : ℤ → ι → ℝ) (k m : ℤ) :=
  ∑ i, c i*v k i*v m i

theorem gram_symmetric {ι : Type*} [Fintype ι] (c : ι → ℝ) (v : ℤ → ι → ℝ)
    (k m : ℤ) : gram c v k m = gram c v m k := by
  unfold gram
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem gram_psd {ι : Type*} [Fintype ι] (c : ι → ℝ) (v : ℤ → ι → ℝ)
    (hc : ∀ i, 0 ≤ c i) (W : Finset ℤ) (x : ℤ → ℝ) :
    0 ≤ ∑ k ∈ W, ∑ m ∈ W, gram c v k m*x k*x m := by
  classical
  unfold gram
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_nonneg
  intro i _
  rw [Finset.sum_comm]
  have he :
      (∑ k ∈ W, ∑ m ∈ W, c i*v k i*v m i*x k*x m) =
      c i*(∑ k ∈ W, v k i*x k)^2 := by
    rw [pow_two,Finset.mul_sum]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro m _
    ring
  rw [he]
  exact mul_nonneg (hc i) (sq_nonneg _)

def actualKernel (g : 𝓢(ℝ,ℂ)) (u : Bonds) (k m : ℤ) : ℝ :=
  (∫ t : ℝ, (weight g t*((t:ℂ)*Complex.I)) •
    M12SmoothCompressions.D u t m (lp.single 2 (k-1) 1) : H) k |>.re

theorem kernel_entry_limit (g : 𝓢(ℝ,ℂ)) (u : Bonds) (k m : ℤ) :
    Tendsto (fun N : ℕ => actualKernel g (cut u N) k m)
      atTop (𝓝 (actualKernel g u k m)) := by
  have hm : Integrable (fun t : ℝ => ‖weight g t‖*|t|) := by
    simpa using weight_moment g 0
  have h := M12SmoothCompressions.fourier_derivative_strong u (weight g) m
    (lp.single 2 (k-1) 1) (weight_continuous g).aestronglyMeasurable hm
  let ev : H →L[ℂ] ℂ := lp.evalCLM ℂ (by norm_num : (2:ℝ≥0∞) ≠ 0) k
  exact Complex.continuous_re.continuousAt.tendsto.comp (ev.continuous.continuousAt.tendsto.comp h)

/-- Actual bilateral PSD, with finite spectral equality on each fixed
window eventually; the strong limit and the finite PSD inequality are
derived here, not assumed. -/
theorem bilateral_psd (g : 𝓢(ℝ,ℂ)) (u : Bonds) (f fp : ℝ → ℝ)
    (hmono : MonotoneOn f (Icc (-1:ℝ) 1))
    (hfp : ∀ a ∈ Icc (-1:ℝ) 1, 0 ≤ fp a)
    (W : Finset ℤ) (x : ℤ → ℝ)
    (hfinite : ∀ᶠ N : ℕ in atTop, ∃ (n : ℕ) (λ : Fin n → ℝ)
      (v : ℤ → Fin n × Fin n → ℝ),
      (∀ i, λ i ∈ Icc (-1:ℝ) 1) ∧
      ∀ k ∈ W, ∀ m ∈ W, actualKernel g (cut u N) k m =
        gram (fun i : Fin n × Fin n => (1/2:ℝ)*dd f fp (λ i.1) (λ i.2)) v k m) :
    0 ≤ ∑ k ∈ W, ∑ m ∈ W, actualKernel g u k m*x k*x m := by
  have h : Tendsto (fun N : ℕ => ∑ k ∈ W, ∑ m ∈ W,
      actualKernel g (cut u N) k m*x k*x m) atTop
      (𝓝 (∑ k ∈ W, ∑ m ∈ W, actualKernel g u k m*x k*x m)) := by
    apply tendsto_finset_sum
    intro k _
    apply tendsto_finset_sum
    intro m _
    exact ((kernel_entry_limit g u k m).mul tendsto_const_nhds).mul tendsto_const_nhds
  apply le_of_tendsto_of_tendsto tendsto_const_nhds h
  filter_upwards [hfinite] with N hN
  obtain ⟨n,λ,v,hλ,he⟩ := hN
  have hg := gram_psd (fun i : Fin n × Fin n => (1/2:ℝ)*dd f fp (λ i.1) (λ i.2)) v
    (fun i => mul_nonneg (by norm_num) (dividedDifference_nonneg f fp hmono hfp (hλ i.1) (hλ i.2))) W x
  convert hg using 1
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro m hm
  rw [he k hk m hm]

theorem bilateral_symmetric (g : 𝓢(ℝ,ℂ)) (u : Bonds) (k m : ℤ)
    (hfinite : ∀ᶠ N : ℕ in atTop, actualKernel g (cut u N) k m =
      actualKernel g (cut u N) m k) :
    actualKernel g u k m = actualKernel g u m k := by
  exact tendsto_nhds_unique_of_eventuallyEq (kernel_entry_limit g u k m)
    (kernel_entry_limit g u m k) hfinite

end M12DKFourierBridge
#print axioms M12DKFourierBridge.phase_norm
#print axioms M12DKFourierBridge.phase_derivative
#print axioms M12DKFourierBridge.scalar_derivative
#print axioms M12DKFourierBridge.dividedDifference_nonneg
#print axioms M12DKFourierBridge.scalar_DK_diag
#print axioms M12DKFourierBridge.scalar_DK_offdiag
#print axioms M12DKFourierBridge.scalar_DK
#print axioms M12DKFourierBridge.gram_symmetric
#print axioms M12DKFourierBridge.gram_psd
#print axioms M12DKFourierBridge.kernel_entry_limit
#print axioms M12DKFourierBridge.bilateral_psd
#print axioms M12DKFourierBridge.bilateral_symmetric
