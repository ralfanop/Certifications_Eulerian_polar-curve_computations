import Mathlib
import SharedCore.Det4Zeros

/-! Meromorphic logarithmic derivative and exact simple-pole residues of
the entire diagonal regularized determinant.
The residue is certified both as the local Laurent principal-part coefficient
and as the punctured limit of (z-c) times the logarithmic derivative. -/
namespace SharedCore.Det4LogDeriv
open SharedCore.Det4Complex SharedCore.Det4Entire SharedCore.Det4Zeros
open Filter
open scoped Topology

noncomputable def determinantLogDeriv : ℂ → ℂ :=
  logDeriv regularizedProduct

theorem determinant_log_deriv_eq (z : ℂ) :
    determinantLogDeriv z = deriv regularizedProduct z / regularizedProduct z := rfl

theorem determinant_meromorphic (z : ℂ) : MeromorphicAt regularizedProduct z :=
  (determinant_entire z).meromorphicAt

theorem log_deriv_meromorphic_at (z : ℂ) : MeromorphicAt determinantLogDeriv z :=
  (determinant_meromorphic z).logDeriv

theorem log_deriv_meromorphic : Meromorphic determinantLogDeriv :=
  fun z => log_deriv_meromorphic_at z

theorem log_deriv_meromorphic_on_univ : MeromorphicOn determinantLogDeriv Set.univ :=
  log_deriv_meromorphic.meromorphicOn

theorem log_deriv_analytic_off_roots (z : ℂ) (hz : ∀ n : ℕ, z ≠ root n) :
    AnalyticAt ℂ determinantLogDeriv z := by
  have h := determinant_entire z
  exact h.deriv.div h ((determinant_ne_zero_iff z).mpr hz)

theorem shifted_power_log_deriv (c z : ℂ) (k : ℕ) :
    logDeriv (fun w : ℂ => (w-c)^k) z = (k:ℂ)/(z-c) := by
  rw [logDeriv_fun_pow (f := fun w : ℂ => w-c) (by fun_prop)]
  have hd : deriv (fun w : ℂ => w-c) z = 1 := by
    simpa using ((hasDerivAt_id z).sub_const c).deriv
  rw [logDeriv_apply, hd]
  ring

/-- Generic local log derivative of a zero times an analytic nonvanishing unit. -/
theorem local_log_deriv_factor (f g : ℂ → ℂ) (c : ℂ) (k : ℕ)
    (hg : AnalyticAt ℂ g c) (hg0 : g c ≠ 0)
    (hf : ∀ᶠ z in 𝓝 c, f z = (z-c)^k * g z) :
    ∀ᶠ z in 𝓝[≠] c, logDeriv f z = (k:ℂ)/(z-c) + logDeriv g z := by
  have hf' : f =ᶠ[𝓝 c] ((fun z : ℂ => (z-c)^k) * g) := hf
  have he := (logDeriv_congr_nhds hf').filter_mono
    (nhdsWithin_le_nhds : 𝓝[≠] c ≤ 𝓝 c)
  have hgn := (hg.continuousAt.eventually_ne hg0).filter_mono
    (nhdsWithin_le_nhds : 𝓝[≠] c ≤ 𝓝 c)
  have hga := hg.eventually_analyticAt.filter_mono
    (nhdsWithin_le_nhds : 𝓝[≠] c ≤ 𝓝 c)
  filter_upwards [he, hgn, hga, self_mem_nhdsWithin] with z hz hne ha hzc
  have hzc' : z ≠ c := by simpa using hzc
  rw [hz, logDeriv_mul z (pow_ne_zero k (sub_ne_zero.mpr hzc')) hne
    (by fun_prop) ha.differentiableAt, shifted_power_log_deriv]

noncomputable def analyticRemainder (n : ℕ) : ℂ → ℂ :=
  logDeriv (zeroUnit n)

theorem remainder_analytic (n : ℕ) :
    AnalyticAt ℂ (analyticRemainder n) (root n) := by
  exact (zero_unit_analytic n).deriv.div (zero_unit_analytic n) (zero_unit_ne_zero n)

theorem log_deriv_principal_part (n : ℕ) :
    ∀ᶠ z in 𝓝[≠] (root n),
      determinantLogDeriv z =
        (Det4Complex.multiplicity n : ℂ)/(z-root n) + analyticRemainder n z :=
  local_log_deriv_factor regularizedProduct (zeroUnit n) (root n)
    (Det4Complex.multiplicity n) (zero_unit_analytic n) (zero_unit_ne_zero n)
    (determinant_local_factor n)

theorem pole_removed_analytic (n : ℕ) :
    AnalyticAt ℂ (fun z => (Det4Complex.multiplicity n : ℂ) +
      (z-root n) * analyticRemainder n z) (root n) := by
  exact analyticAt_const.add ((show AnalyticAt ℂ (fun z : ℂ => z-root n) (root n)
    by fun_prop).mul (remainder_analytic n))

theorem pole_removed_eventually_eq (n : ℕ) :
    ∀ᶠ z in 𝓝[≠] (root n),
      (z-root n) * determinantLogDeriv z =
        (Det4Complex.multiplicity n : ℂ) + (z-root n) * analyticRemainder n z := by
  filter_upwards [log_deriv_principal_part n, self_mem_nhdsWithin] with z hz hzc
  have hn : z-root n ≠ 0 := sub_ne_zero.mpr (by simpa using hzc)
  rw [hz]
  field_simp [hn] <;> ring

theorem residue_limit (n : ℕ) :
    Tendsto (fun z => (z-root n) * determinantLogDeriv z)
      (𝓝[≠] (root n)) (𝓝 (Det4Complex.multiplicity n : ℂ)) := by
  have h := (pole_removed_analytic n).continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[≠] (root n) ≤ 𝓝 (root n))
  have he : (fun z => (z-root n) * determinantLogDeriv z) =ᶠ[𝓝[≠] (root n)]
      (fun z => (Det4Complex.multiplicity n : ℂ) + (z-root n)*analyticRemainder n z) :=
    pole_removed_eventually_eq n
  rw [tendsto_congr' he]
  simpa using h

/-- Residue of a function at a pole of order at most one, expressed by
the limit of (z-c) times the function. Only used at proved simple poles. -/
noncomputable def simplePoleResidue (f : ℂ → ℂ) (c : ℂ) : ℂ :=
  limUnder (𝓝[≠] c) (fun z => (z-c)*f z)

theorem residue_at_root (n : ℕ) :
    simplePoleResidue determinantLogDeriv (root n) = (Det4Complex.multiplicity n : ℂ) :=
  (residue_limit n).limUnder_eq

theorem residue_nonzero (n : ℕ) : simplePoleResidue determinantLogDeriv (root n) ≠ 0 := by
  rw [residue_at_root]
  exact_mod_cast (ne_of_gt (multiplicity_positive n))

theorem determinant_meromorphic_order_at_root (n : ℕ) :
    meromorphicOrderAt regularizedProduct (root n) =
      ((Det4Complex.multiplicity n : ℤ) : WithTop ℤ) := by
  rw [(determinant_entire (root n)).meromorphicOrderAt_eq, determinant_order_at_root,
    ENat.map_natCast]

theorem log_deriv_simple_pole (n : ℕ) :
    meromorphicOrderAt determinantLogDeriv (root n) = -1 := by
  unfold determinantLogDeriv
  apply meromorphicOrderAt_logDeriv_eq_neg_one (determinant_meromorphic (root n))
  · rw [determinant_meromorphic_order_at_root]
    exact_mod_cast (ne_of_gt (multiplicity_positive n))
  · rw [determinant_meromorphic_order_at_root]
    simp

theorem log_deriv_pole_iff (z : ℂ) :
    meromorphicOrderAt determinantLogDeriv z < 0 ↔ ∃ n : ℕ, z = root n := by
  constructor
  · intro h
    by_contra hn
    have ha := log_deriv_analytic_off_roots z (fun n hn' => hn ⟨n, hn'⟩)
    exact (not_lt_of_ge ha.meromorphicOrderAt_nonneg) h
  · rintro ⟨n,rfl⟩
    rw [log_deriv_simple_pole]
    change ((-1 : ℤ) : WithTop ℤ) < ((0 : ℤ) : WithTop ℤ)
    exact WithTop.coe_lt_coe.mpr (by norm_num)

theorem root_index_of_integer (m : ℕ) (hm : 2 ≤ m) : root (m-2) = -(m:ℂ) := by
  have he : m-2+2 = m := by omega
  calc
    _ = -(((m-2+2:ℕ):ℂ)) := by unfold root; push_cast; rfl
    _ = _ := by rw [he]

theorem multiplicity_index_of_integer (m : ℕ) (hm : 2 ≤ m) :
    Det4Complex.multiplicity (m-2) = m*(m-1) := by
  have he : m-2+1 = m-1 := by omega
  have he' : m-2+2 = m := by omega
  unfold Det4Complex.multiplicity
  rw [he, he', Nat.mul_comm]

theorem residue_at_negative_integer (m : ℕ) (hm : 2 ≤ m) :
    simplePoleResidue determinantLogDeriv (-(m:ℂ)) = ((m*(m-1):ℕ):ℂ) := by
  rw [← root_index_of_integer m hm, residue_at_root, multiplicity_index_of_integer m hm]

theorem simple_pole_at_negative_integer (m : ℕ) (hm : 2 ≤ m) :
    meromorphicOrderAt determinantLogDeriv (-(m:ℂ)) = -1 := by
  rw [← root_index_of_integer m hm, log_deriv_simple_pole]

end SharedCore.Det4LogDeriv

#print axioms SharedCore.Det4LogDeriv.determinant_log_deriv_eq
#print axioms SharedCore.Det4LogDeriv.determinant_meromorphic
#print axioms SharedCore.Det4LogDeriv.log_deriv_meromorphic_at
#print axioms SharedCore.Det4LogDeriv.log_deriv_meromorphic
#print axioms SharedCore.Det4LogDeriv.log_deriv_meromorphic_on_univ
#print axioms SharedCore.Det4LogDeriv.log_deriv_analytic_off_roots
#print axioms SharedCore.Det4LogDeriv.shifted_power_log_deriv
#print axioms SharedCore.Det4LogDeriv.local_log_deriv_factor
#print axioms SharedCore.Det4LogDeriv.remainder_analytic
#print axioms SharedCore.Det4LogDeriv.log_deriv_principal_part
#print axioms SharedCore.Det4LogDeriv.pole_removed_analytic
#print axioms SharedCore.Det4LogDeriv.pole_removed_eventually_eq
#print axioms SharedCore.Det4LogDeriv.residue_limit
#print axioms SharedCore.Det4LogDeriv.residue_at_root
#print axioms SharedCore.Det4LogDeriv.residue_nonzero
#print axioms SharedCore.Det4LogDeriv.determinant_meromorphic_order_at_root
#print axioms SharedCore.Det4LogDeriv.log_deriv_simple_pole
#print axioms SharedCore.Det4LogDeriv.log_deriv_pole_iff
#print axioms SharedCore.Det4LogDeriv.root_index_of_integer
#print axioms SharedCore.Det4LogDeriv.multiplicity_index_of_integer
#print axioms SharedCore.Det4LogDeriv.residue_at_negative_integer
#print axioms SharedCore.Det4LogDeriv.simple_pole_at_negative_integer
