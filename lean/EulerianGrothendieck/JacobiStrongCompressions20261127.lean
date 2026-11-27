import EulerianGrothendieck.JacobiDKBilateral20261127

/-! M12 Lemma 5.12: strong convergence of literal finite bond compressions
on every vector, of all their powers and of differentiated powers. Uses
density of finite coordinate sums, not convergence in operator norm. -/
set_option maxHeartbeats 2000000
noncomputable section
open Filter Set
open scoped Topology ENNReal
namespace M12StrongCompressions
open M12BilateralJacobi M12JacobiFrechet M12DKBilateral

theorem cutoff_single_eventually (u : Bonds) (l : ℤ) (z : ℂ) :
    ∀ᶠ N : ℕ in atTop, J (cut u N) (lp.single 2 l z) = J u (lp.single 2 l z) := by
  have he : ∀ᶠ N : ℕ in atTop, (l.natAbs+2) ≤ N :=
    eventually_ge_atTop _
  filter_upwards [he] with N hN
  have hl : -(N:ℤ) ≤ l ∧ l+1 ≤ (N:ℤ) := by
    have hN' : (l.natAbs:ℤ)+2 ≤ (N:ℤ) := by exact_mod_cast hN
    have h₁ : -(l.natAbs:ℤ) ≤ l := by omega
    have h₂ : l ≤ (l.natAbs:ℤ) := by omega
    omega
  ext k
  rw [J_apply,J_apply]
  by_cases h₁ : k-1=l
  · have hk : k=l+1 := by omega
    rw [hk,cut_eq u N (l+1) (by omega) hl.2]
    have hn : l+1+1 ≠ l := by omega
    simp [lp.single_apply,hn,Ne.symm hn]
  · by_cases h₂ : k+1=l
    · rw [h₂,cut_eq u N l hl.1 (by omega)]
      simp [lp.single_apply,h₁,Ne.symm h₁]
    · simp [lp.single_apply,h₁,h₂,Ne.symm h₁,Ne.symm h₂]

theorem cutoff_sum_eventually (u : Bonds) (S : Finset ℤ) (x : H) :
    ∀ᶠ N : ℕ in atTop,
      J (cut u N) (∑ l ∈ S, lp.single 2 l (x l)) =
        J u (∑ l ∈ S, lp.single 2 l (x l)) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert l S hl ih =>
    filter_upwards [cutoff_single_eventually u l (x l),ih] with N h₁ h₂
    rw [Finset.sum_insert hl,map_add,map_add,h₁,h₂]

/-- Genuine strong operator convergence on the entire bilateral Hilbert space. -/
theorem cutoff_strong (u : Bonds) (x : H) :
    Tendsto (fun N : ℕ => J (cut u N) x) atTop (𝓝 (J u x)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have h := lp.hasSum_single (p := (2:ℝ≥0∞)) (by norm_num) x
  rw [HasSum, Metric.tendsto_nhds] at h
  obtain ⟨S,hS⟩ := (h (ε/3) (by linarith)).exists
  let y : H := ∑ l ∈ S, lp.single 2 l (x l)
  have hy : ‖x-y‖ < ε/3 := by
    have h' : dist y x < ε/3 := hS
    rw [dist_comm,dist_eq_norm] at h'
    exact h'
  filter_upwards [cutoff_sum_eventually u S x] with N hN
  have hNy : J (cut u N) y = J u y := hN
  rw [dist_eq_norm]
  have h₁ : ‖J (cut u N) (x-y)‖ ≤ ‖x-y‖ :=
    ((J (cut u N)).le_opNorm (x-y)).trans
      (by simpa using mul_le_mul_of_nonneg_right (J_norm_le (cut u N)) (norm_nonneg (x-y)))
  have h₂ : ‖J u (x-y)‖ ≤ ‖x-y‖ :=
    ((J u).le_opNorm (x-y)).trans
      (by simpa using mul_le_mul_of_nonneg_right (J_norm_le u) (norm_nonneg (x-y)))
  have he : J (cut u N) x-J u x =
      J (cut u N) (x-y)-J u (x-y) := by
    rw [map_sub,map_sub,hNy]
    abel
  rw [he]
  exact (norm_sub_le _ _).trans_lt (by linarith)

/-- Strong convergence is stable under applying a uniformly bounded varying
operator to a norm-convergent varying vector. -/
theorem strong_apply (T : ℕ → Op) (A : Op) (x : ℕ → H) (y : H)
    (hT : ∀ z : H, Tendsto (fun N => T N z) atTop (𝓝 (A z)))
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ N, ‖T N‖ ≤ C)
    (hx : Tendsto x atTop (𝓝 y)) :
    Tendsto (fun N => T N (x N)) atTop (𝓝 (A y)) := by
  have h₁ : Tendsto (fun N => ‖x N-y‖) atTop (𝓝 0) := by
    simpa using (hx.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => y) atTop (𝓝 y))).norm
  have h₂ : Tendsto (fun N => ‖T N y-A y‖) atTop (𝓝 0) := by
    simpa using ((hT y).sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => A y) atTop (𝓝 (A y)))).norm
  have hg : Tendsto (fun N => C*‖x N-y‖+‖T N y-A y‖) atTop (𝓝 0) := by
    simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℕ => C) atTop (𝓝 C)).mul h₁).add h₂
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ hg
  filter_upwards [] with N
  calc
    ‖T N (x N)-A y‖ = ‖T N (x N-y)+(T N y-A y)‖ := by
      rw [map_sub]; congr 1; abel
    _ ≤ ‖T N (x N-y)‖+‖T N y-A y‖ := norm_add_le _ _
    _ ≤ C*‖x N-y‖+‖T N y-A y‖ := add_le_add (((T N).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hb N) (norm_nonneg _))) le_rfl

theorem cutoff_power_strong (u : Bonds) (n : ℕ) (x : H) :
    Tendsto (fun N : ℕ => ((J (cut u N))^n) x) atTop (𝓝 (((J u)^n) x)) := by
  induction n with
  | zero => simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (𝓝 x))
  | succ n ih =>
    simpa only [pow_succ',ContinuousLinearMap.mul_apply] using
      strong_apply (fun N => J (cut u N)) (J u)
        (fun N => ((J (cut u N))^n) x) (((J u)^n) x)
        (cutoff_strong u) 1 zero_le_one (fun N => J_norm_le _) ih

theorem cutoff_derivative_strong (u : Bonds) (n : ℕ) (m : ℤ) (x : H) :
    Tendsto (fun N : ℕ => powerD (J (cut u N)) n (bond m) x) atTop
      (𝓝 (powerD (J u) n (bond m) x)) := by
  induction n with
  | zero => simpa only [powerD_zero,ContinuousLinearMap.zero_apply] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:H)) atTop (𝓝 0))
  | succ n ih =>
    have h₁ := strong_apply (fun N => J (cut u N)) (J u)
      (fun N => powerD (J (cut u N)) n (bond m) x) (powerD (J u) n (bond m) x)
      (cutoff_strong u) 1 zero_le_one (fun N => J_norm_le _) ih
    have h₂ := (bond m).continuous.continuousAt.tendsto.comp (cutoff_power_strong u n x)
    simpa only [powerD_succ,ContinuousLinearMap.add_apply,ContinuousLinearMap.mul_apply,Function.comp_def] using h₁.add h₂

end M12StrongCompressions
#print axioms M12StrongCompressions.cutoff_single_eventually
#print axioms M12StrongCompressions.cutoff_sum_eventually
#print axioms M12StrongCompressions.cutoff_strong
#print axioms M12StrongCompressions.strong_apply
#print axioms M12StrongCompressions.cutoff_power_strong
#print axioms M12StrongCompressions.cutoff_derivative_strong
