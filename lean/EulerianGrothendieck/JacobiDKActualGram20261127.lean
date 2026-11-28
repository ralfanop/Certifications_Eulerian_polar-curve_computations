import EulerianGrothendieck.JacobiDKFourierBridge20261127
import EulerianGrothendieck.JacobiFiniteSpectrum20261127
import EulerianGrothendieck.JacobiFourierLocality20261127

/-! Identify the actual finite-cutoff Fourier-Duhamel bond kernel with
the finite Daleckii-Krein Gram form. Then use the already proved strong
compression limit to remove the finite spectral equality premise. -/
set_option maxHeartbeats 3000000
noncomputable section
open MeasureTheory NormedSpace Set Filter Finset
open scoped Topology SchwartzMap ENNReal
namespace M12DKActualGram
open M12BilateralJacobi M12DKBilateral M12FiniteSpectrum
open M12DKFourierBridge M12SchwartzFourier M12JacobiPropagation

theorem dd_symmetric (f fp : ℝ → ℝ) (a b : ℝ) :
    dd f fp a b = dd f fp b a := by
  by_cases h : a=b
  · subst b; rfl
  · unfold dd
    rw [if_neg h,if_neg (Ne.symm h)]
    have ha : a-b ≠ 0 := sub_ne_zero.mpr h
    have hb : b-a ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
    field_simp <;> ring

theorem phase_continuous : Continuous (fun p : ℝ × ℝ => phase p.1 p.2) := by
  unfold phase
  exact Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const |>.mul
      (Complex.continuous_ofReal.comp continuous_snd))

theorem phase_affine_add (t s a b : ℝ) :
    phase ((1-s)*t) a * phase (s*t) b = phase t ((1-s)*a+s*b) := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

def scalarInner (t a b : ℝ) : ℂ :=
  ∫ s in (0:ℝ)..1, phase t ((1-s)*a+s*b)

theorem scalar_inner_norm (t a b : ℝ) : ‖scalarInner t a b‖ ≤ 1 := by
  unfold scalarInner
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := 1) (C := 1)
    (f := fun s => phase t ((1-s)*a+s*b))
    (fun s _ => le_of_eq (M12DKFourierBridge.phase_norm _ _))

theorem scalar_inner_continuous (a b : ℝ) : Continuous (fun t => scalarInner t a b) := by
  unfold scalarInner
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact phase_continuous.comp (continuous_fst.prodMk
    (((continuous_const.sub continuous_snd).mul continuous_const).add
      (continuous_snd.mul continuous_const)))

theorem scalar_integrable (g : 𝓢(ℝ,ℂ)) (a b : ℝ) :
    Integrable (fun t => weight g t*((t:ℂ)*Complex.I)*scalarInner t a b) := by
  have hm : Integrable (fun t : ℝ => ‖weight g t‖*|t|) := by
    simpa using weight_moment g 0
  apply hm.mono'
  · exact (((weight_continuous g).mul (Complex.continuous_ofReal.mul continuous_const)).mul
      (scalar_inner_continuous a b)).aestronglyMeasurable
  · filter_upwards [] with t
    change ‖weight g t*((t:ℂ)*Complex.I)*scalarInner t a b‖ ≤ ‖weight g t‖*|t|
    rw [norm_mul,norm_mul,norm_mul,Complex.norm_real,Complex.norm_I,mul_one,Real.norm_eq_abs]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (scalar_inner_norm t a b)
      (mul_nonneg (norm_nonneg (weight g t)) (abs_nonneg t))

def pairAmp (u : Bonds) (N : ℕ) (m mp : sites N) (r q : sites N) : ℝ :=
  basis u N r m * basis u N q mp + basis u N r mp * basis u N q m

def coeff (u : Bonds) (N : ℕ) (k kp m mp : sites N) (r q : sites N) : ℝ :=
  basis u N r k * basis u N q kp * pairAmp u N m mp r q

theorem density_entry_expansion (u : Bonds) (N : ℕ) (t s : ℝ)
    (k kp m mp : sites N) (hmp : (mp:ℤ)=(m:ℤ)-1) :
    entry (M12SmoothCompressions.density (cut u N) t s (m:ℤ)) k kp =
    ∑ r : sites N, ∑ q : sites N, (coeff u N k kp m mp r q:ℂ) *
      phase t ((1-s)*eigenvalues u N r+s*eigenvalues u N q) := by
  unfold M12SmoothCompressions.density
  rw [M12FourierLocality.bond_product_entry,← hmp]
  rw [phase_entry u N ((1-s)*t) k m,phase_entry u N (s*t) mp kp,
      phase_entry u N ((1-s)*t) k mp,phase_entry u N (s*t) m kp]
  simp_rw [Finset.sum_mul,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro q _
  rw [← phase_affine_add t s (eigenvalues u N r) (eigenvalues u N q)]
  unfold coeff pairAmp phase
  push_cast
  ring

theorem duhamel_entry_expansion (u : Bonds) (N : ℕ) (t : ℝ)
    (k kp m mp : sites N) (hmp : (mp:ℤ)=(m:ℤ)-1) :
    entry (M12SmoothCompressions.D (cut u N) t (m:ℤ)) k kp =
    ∑ r : sites N, ∑ q : sites N, (coeff u N k kp m mp r q:ℂ) *
      scalarInner t (eigenvalues u N r) (eigenvalues u N q) := by
  have hi : IntervalIntegrable (fun s : ℝ => M12SmoothCompressions.density (cut u N) t s (m:ℤ)) volume 0 1 :=
    ((M12SmoothCompressions.density_joint_cont (cut u N) (m:ℤ)).comp
      (continuous_const.prodMk continuous_id)).intervalIntegrable 0 1
  have hc (r q : sites N) : Continuous (fun s : ℝ =>
    (coeff u N k kp m mp r q:ℂ) * phase t ((1-s)*eigenvalues u N r+s*eigenvalues u N q)) :=
    continuous_const.mul (phase_continuous.comp (continuous_const.prodMk
      (((continuous_const.sub continuous_id).mul continuous_const).add
        (continuous_id.mul continuous_const))))
  unfold M12SmoothCompressions.D
  rw [← entryMap_apply,← (entryMap k kp).intervalIntegral_comp_comm hi]
  simp_rw [entryMap_apply,density_entry_expansion u N t _ k kp m mp hmp]
  rw [intervalIntegral.integral_finsetSum (fun r _ =>
    (continuous_finset_sum _ (fun q _ => hc r q)).intervalIntegrable 0 1)]
  apply Finset.sum_congr rfl
  intro r _
  rw [intervalIntegral.integral_finsetSum (fun q _ => (hc r q).intervalIntegrable 0 1)]
  apply Finset.sum_congr rfl
  intro q _
  rw [intervalIntegral.integral_const_mul]
  rfl

def complexEntry (g : 𝓢(ℝ,ℂ)) (u : Bonds) (k m : ℤ) : ℂ :=
  ∫ t : ℝ, weight g t*((t:ℂ)*Complex.I)*entry (M12SmoothCompressions.D u t m) k (k-1)

theorem actual_complex_entry (g : 𝓢(ℝ,ℂ)) (u : Bonds) (k m : ℤ) :
    actualKernel g u k m = (complexEntry g u k m).re := by
  let x : H := lp.single 2 (k-1) 1
  let ev : H →L[ℂ] ℂ := lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 k
  have hC : Continuous (fun t : ℝ => M12SmoothCompressions.D u t m) := by
    unfold M12SmoothCompressions.D
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact M12SmoothCompressions.density_joint_cont u m
  have hm : Integrable (fun t : ℝ => ‖weight g t‖*|t|) := by
    simpa using weight_moment g 0
  have hi : Integrable (fun t : ℝ => (weight g t*((t:ℂ)*Complex.I)) •
    M12SmoothCompressions.D u t m x) := by
    apply (hm.const_mul (2*‖x‖)).mono'
    · exact (((weight_continuous g).mul (Complex.continuous_ofReal.mul continuous_const)).smul
        ((ContinuousLinearMap.apply ℂ H x).continuous.comp hC)).aestronglyMeasurable
    · filter_upwards [] with t
      rw [norm_smul,norm_mul,norm_mul,Complex.norm_real,Complex.norm_I,mul_one,Real.norm_eq_abs]
      have h := ((M12SmoothCompressions.D u t m).le_opNorm x).trans
        (mul_le_mul_of_nonneg_right (M12SmoothCompressions.integrated_density_norm u t m) (norm_nonneg _))
      calc
        _ ≤ (‖weight g t‖*|t|)*(2*‖x‖) :=
          mul_le_mul_of_nonneg_left h (mul_nonneg (norm_nonneg (weight g t)) (abs_nonneg t))
        _ = _ := by ring
  unfold actualKernel complexEntry
  change (ev (∫ t : ℝ, (weight g t*((t:ℂ)*Complex.I)) •
    M12SmoothCompressions.D u t m x)).re = _
  rw [← ev.integral_comp_comm hi]
  rfl

theorem actual_finite_expansion (g : 𝓢(ℝ,ℂ)) (u : Bonds) (N : ℕ)
    (k kp m mp : sites N) (hkp : (kp:ℤ)=(k:ℤ)-1) (hmp : (mp:ℤ)=(m:ℤ)-1)
    (f fp : ℝ → ℝ) (hf : ∀ x, g x = (f x:ℂ))
    (hfp : ∀ x, deriv (fun y : ℝ => g y) x = (fp x:ℂ)) :
    actualKernel g (cut u N) k m =
    ∑ r : sites N, ∑ q : sites N, coeff u N k kp m mp r q *
      dd f fp (eigenvalues u N r) (eigenvalues u N q) := by
  rw [actual_complex_entry]
  have h : complexEntry g (cut u N) k m =
      ∑ r : sites N, ∑ q : sites N, (coeff u N k kp m mp r q:ℂ) *
        scalarDK g (eigenvalues u N r) (eigenvalues u N q) := by
    unfold complexEntry
    rw [← hkp]
    simp_rw [duhamel_entry_expansion u N _ k kp m mp hmp,Finset.mul_sum]
    have hi (r q : sites N) : Integrable (fun t : ℝ =>
      weight g t*((t:ℂ)*Complex.I)*((coeff u N k kp m mp r q:ℂ) *
        scalarInner t (eigenvalues u N r) (eigenvalues u N q))) := by
      convert (scalar_integrable g (eigenvalues u N r) (eigenvalues u N q)).const_mul
        (coeff u N k kp m mp r q:ℂ) using 1
      funext t
      ring
    rw [integral_finsetSum _ (fun r _ => integrable_finsetSum _ (fun q _ => hi r q))]
    apply Finset.sum_congr rfl
    intro r _
    rw [integral_finsetSum _ (fun q _ => hi r q)]
    apply Finset.sum_congr rfl
    intro q _
    unfold scalarDK
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t
    unfold scalarInner
    ring
  rw [h]
  simp_rw [scalar_DK g f fp hf hfp]
  push_cast
  simp

theorem gram_symmetrization (u : Bonds) (N : ℕ) (k kp m mp : sites N)
    (f fp : ℝ → ℝ) :
    (∑ r : sites N, ∑ q : sites N, coeff u N k kp m mp r q *
      dd f fp (eigenvalues u N r) (eigenvalues u N q)) =
    ∑ r : sites N, ∑ q : sites N, (1/2:ℝ)*dd f fp (eigenvalues u N r) (eigenvalues u N q)*
      pairAmp u N k kp r q * pairAmp u N m mp r q := by
  classical
  let F := fun r q : sites N => coeff u N k kp m mp r q *
    dd f fp (eigenvalues u N r) (eigenvalues u N q)
  have hsym : (∑ r, ∑ q, F r q) = ∑ r, ∑ q, F q r := Finset.sum_comm
  change (∑ r, ∑ q, F r q) = _
  calc
    _ = (1/2:ℝ)*((∑ r, ∑ q, F r q)+(∑ r, ∑ q, F q r)) := by rw [← hsym]; ring
    _ = ∑ r : sites N, ∑ q : sites N, (1/2:ℝ)*(F r q+F q r) := by
      simp_rw [Finset.sum_add_distrib,← Finset.mul_sum]
      ring
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro q _
      dsimp [F]
      rw [dd_symmetric f fp (eigenvalues u N q) (eigenvalues u N r)]
      unfold coeff pairAmp
      ring

theorem actual_gram (g : 𝓢(ℝ,ℂ)) (u : Bonds) (N : ℕ) (k kp m mp : sites N)
    (hkp : (kp:ℤ)=(k:ℤ)-1) (hmp : (mp:ℤ)=(m:ℤ)-1)
    (f fp : ℝ → ℝ) (hf : ∀ x, g x = (f x:ℂ))
    (hfp : ∀ x, deriv (fun y : ℝ => g y) x = (fp x:ℂ)) :
    actualKernel g (cut u N) k m =
    ∑ r : sites N, ∑ q : sites N, (1/2:ℝ)*dd f fp (eigenvalues u N r) (eigenvalues u N q)*
      pairAmp u N k kp r q * pairAmp u N m mp r q := by
  rw [actual_finite_expansion g u N k kp m mp hkp hmp f fp hf hfp,gram_symmetrization]

theorem eventual_window (W : Finset ℤ) :
    ∀ᶠ N : ℕ in atTop, ∀ k ∈ W,
      k ∈ Finset.Icc (-(N:ℤ)-1) (N:ℤ) ∧
      k-1 ∈ Finset.Icc (-(N:ℤ)-1) (N:ℤ) := by
  classical
  let L := ∑ k ∈ W, k.natAbs
  apply eventually_atTop.2
  refine ⟨L,?_⟩
  intro N hN k hk
  have h := Finset.single_le_sum (f := fun k : ℤ => k.natAbs) (fun i _ => Nat.zero_le _) hk
  have hkN : k.natAbs ≤ N := h.trans hN
  have hh : (k.natAbs:ℤ) ≤ (N:ℤ) := by exact_mod_cast hkN
  simp only [Finset.mem_Icc]
  omega

/-- Finite spectral equality is derived rather than assumed. -/
theorem actual_bilateral_psd (g : 𝓢(ℝ,ℂ)) (u : Bonds) (f fp : ℝ → ℝ)
    (hf : ∀ x, g x = (f x:ℂ)) (hder : ∀ x, deriv (fun y : ℝ => g y) x = (fp x:ℂ))
    (hmono : MonotoneOn f (Icc (-1:ℝ) 1))
    (hfp : ∀ a ∈ Icc (-1:ℝ) 1, 0 ≤ fp a)
    (W : Finset ℤ) (x : ℤ → ℝ) :
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
  filter_upwards [eventual_window W] with N hN
  let v : ℤ → (sites N × sites N) → ℝ := fun k z =>
    if hk : k ∈ W then pairAmp u N ⟨k,(hN k hk).1⟩ ⟨k-1,(hN k hk).2⟩ z.1 z.2 else 0
  let c : sites N × sites N → ℝ := fun z =>
    (1/2:ℝ)*dd f fp (eigenvalues u N z.1) (eigenvalues u N z.2)
  have hp := gram_psd c v (fun z => mul_nonneg (by norm_num)
    (dividedDifference_nonneg f fp hmono hfp (eigenvalue_interval u N z.1) (eigenvalue_interval u N z.2))) W x
  convert hp using 1
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro m hm
  rw [actual_gram g u N ⟨k,(hN k hk).1⟩ ⟨k-1,(hN k hk).2⟩
    ⟨m,(hN m hm).1⟩ ⟨m-1,(hN m hm).2⟩ rfl rfl f fp hf hder]
  unfold gram c v
  simp only [dif_pos hk,dif_pos hm,Finset.sum_product]

theorem actual_bilateral_symmetric (g : 𝓢(ℝ,ℂ)) (u : Bonds) (f fp : ℝ → ℝ)
    (hf : ∀ x, g x = (f x:ℂ)) (hder : ∀ x, deriv (fun y : ℝ => g y) x = (fp x:ℂ))
    (k m : ℤ) : actualKernel g u k m = actualKernel g u m k := by
  apply bilateral_symmetric
  filter_upwards [eventual_window ({k,m}:Finset ℤ)] with N hN
  have hk := hN k (by simp)
  have hm := hN m (by simp)
  rw [actual_gram g u N ⟨k,hk.1⟩ ⟨k-1,hk.2⟩ ⟨m,hm.1⟩ ⟨m-1,hm.2⟩ rfl rfl f fp hf hder,
      actual_gram g u N ⟨m,hm.1⟩ ⟨m-1,hm.2⟩ ⟨k,hk.1⟩ ⟨k-1,hk.2⟩ rfl rfl f fp hf hder]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro q _
  ring

end M12DKActualGram
#print axioms M12DKActualGram.dd_symmetric
#print axioms M12DKActualGram.phase_continuous
#print axioms M12DKActualGram.phase_affine_add
#print axioms M12DKActualGram.scalar_inner_norm
#print axioms M12DKActualGram.scalar_inner_continuous
#print axioms M12DKActualGram.scalar_integrable
#print axioms M12DKActualGram.density_entry_expansion
#print axioms M12DKActualGram.duhamel_entry_expansion
#print axioms M12DKActualGram.actual_complex_entry
#print axioms M12DKActualGram.actual_finite_expansion
#print axioms M12DKActualGram.gram_symmetrization
#print axioms M12DKActualGram.actual_gram
#print axioms M12DKActualGram.eventual_window
#print axioms M12DKActualGram.actual_bilateral_psd
#print axioms M12DKActualGram.actual_bilateral_symmetric
