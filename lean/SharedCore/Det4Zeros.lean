import Mathlib
import SharedCore.Det4Entire

/-! Exact zero divisor of the entire diagonal regularized determinant.
Zero order is Mathlib's analyticOrderAt, not a formal Det4Complex.multiplicity label. -/
namespace SharedCore.Det4Zeros
open SharedCore.Det4Complex SharedCore.Det4Entire
open Filter
open scoped Topology

noncomputable def root (n : ℕ) : ℂ := -((n : ℂ)+2)

theorem denominator_ne_zero (n : ℕ) : (n:ℂ)+2 ≠ 0 := by
  exact_mod_cast (show (n:ℝ)+2 ≠ 0 by positivity)

theorem multiplicity_positive (n : ℕ) : 0 < Det4Complex.multiplicity n := by
  unfold Det4Complex.multiplicity
  positivity

theorem root_injective : Function.Injective root := by
  intro a b h
  have he : (a:ℂ) = (b:ℂ) := by
    unfold root at h
    linear_combination -h
  exact_mod_cast he

theorem root_norm (n : ℕ) : ‖root n‖ = (n:ℝ)+2 := by
  unfold root
  rw [norm_neg, show (n:ℂ)+2 = ((n+2:ℕ):ℂ) by push_cast; rfl,
    Complex.norm_natCast]
  push_cast
  rfl

noncomputable def shellUnit (n : ℕ) (z : ℂ) : ℂ :=
  (Complex.exp (-shellArgument z n + shellArgument z n ^ 2/2 -
      shellArgument z n ^ 3/3) / ((n:ℂ)+2)) ^ Det4Complex.multiplicity n

theorem shell_unit_ne_zero (n : ℕ) (z : ℂ) : shellUnit n z ≠ 0 := by
  unfold shellUnit
  exact pow_ne_zero _ (div_ne_zero (Complex.exp_ne_zero _) (denominator_ne_zero n))

theorem shell_unit_analytic (n : ℕ) (z : ℂ) : AnalyticAt ℂ (shellUnit n) z := by
  unfold shellUnit shellArgument
  fun_prop

theorem shell_factor (z : ℂ) (n : ℕ) :
    regularizedShell z n = (z-root n)^Det4Complex.multiplicity n * shellUnit n z := by
  unfold regularizedShell shellUnit
  dsimp only
  rw [← mul_pow]
  apply congrArg (fun x : ℂ => x ^ Det4Complex.multiplicity n)
  have h : 1 + shellArgument z n = (z-root n) / ((n:ℂ)+2) := by
    unfold root shellArgument
    field_simp [denominator_ne_zero n] <;> ring
  rw [h]
  ring

theorem shell_eq_zero_iff (z : ℂ) (n : ℕ) :
    regularizedShell z n = 0 ↔ z = root n := by
  rw [shell_factor, mul_eq_zero, pow_eq_zero_iff (ne_of_gt (multiplicity_positive n))]
  simp [shell_unit_ne_zero, sub_eq_zero]

theorem determinant_eq_zero_iff (z : ℂ) :
    regularizedProduct z = 0 ↔ ∃ n : ℕ, z = root n := by
  constructor
  · intro hz
    obtain ⟨N, hN⟩ := exists_nat_gt ‖z‖
    rw [product_factorization N z (by linarith), mul_eq_zero] at hz
    rcases hz with hp | he
    · obtain ⟨n, _, hn⟩ := Finset.prod_eq_zero_iff.mp hp
      exact ⟨n, (shell_eq_zero_iff z n).mp hn⟩
    · exact (Complex.exp_ne_zero _ he).elim
  · rintro ⟨n, hn⟩
    unfold regularizedProduct
    exact tprod_of_exists_eq_zero ⟨n, (shell_eq_zero_iff z n).mpr hn⟩

theorem determinant_root_zero (n : ℕ) : regularizedProduct (root n) = 0 :=
  (determinant_eq_zero_iff _).mpr ⟨n, rfl⟩

theorem determinant_ne_zero_iff (z : ℂ) :
    regularizedProduct z ≠ 0 ↔ ∀ n : ℕ, z ≠ root n := by
  rw [ne_eq, determinant_eq_zero_iff]
  push_neg
  rfl

theorem root_inside_tail_disk (n : ℕ) : ‖root n‖ < ((n+1:ℕ):ℝ)+2 := by
  rw [root_norm]
  push_cast
  linarith

noncomputable def zeroUnit (n : ℕ) (z : ℂ) : ℂ :=
  (∏ j ∈ Finset.range n, regularizedShell z j) *
    shellUnit n z * Complex.exp (tailLog (n+1) z)

theorem zero_unit_analytic (n : ℕ) : AnalyticAt ℂ (zeroUnit n) (root n) := by
  have ht := tail_log_analytic (n+1) (root n) (root_inside_tail_disk n)
  have he : AnalyticAt ℂ Complex.exp (tailLog (n+1) (root n)) := by fun_prop
  unfold zeroUnit
  exact ((finite_head_analytic n (root n)).mul (shell_unit_analytic n (root n))).mul
    (he.comp ht)

theorem zero_unit_ne_zero (n : ℕ) : zeroUnit n (root n) ≠ 0 := by
  have hp : (∏ j ∈ Finset.range n, regularizedShell (root n) j) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    intro he
    have hnj := root_injective ((shell_eq_zero_iff _ j).mp he)
    have hj' := Finset.mem_range.mp hj
    omega
  unfold zeroUnit
  exact mul_ne_zero (mul_ne_zero hp (shell_unit_ne_zero n _)) (Complex.exp_ne_zero _)

theorem determinant_local_factor (n : ℕ) :
    ∀ᶠ z in 𝓝 (root n),
      regularizedProduct z = (z-root n)^Det4Complex.multiplicity n * zeroUnit n z := by
  have hopen : IsOpen {z : ℂ | ‖z‖ < ((n+1:ℕ):ℝ)+2} :=
    isOpen_lt continuous_norm continuous_const
  filter_upwards [hopen.mem_nhds (root_inside_tail_disk n)] with z hz
  rw [product_factorization (n+1) z hz, Finset.prod_range_succ, shell_factor z n]
  unfold zeroUnit
  ring

theorem determinant_order_at_root (n : ℕ) :
    analyticOrderAt regularizedProduct (root n) = (Det4Complex.multiplicity n : ℕ∞) := by
  apply (determinant_entire (root n)).analyticOrderAt_eq_natCast.mpr
  refine ⟨zeroUnit n, zero_unit_analytic n, zero_unit_ne_zero n, ?_⟩
  simpa only [smul_eq_mul] using determinant_local_factor n

theorem determinant_order_nat_at_root (n : ℕ) :
    analyticOrderNatAt regularizedProduct (root n) = (n+1)*(n+2) := by
  rw [analyticOrderNatAt, determinant_order_at_root, ENat.toNat_natCast] <;> rfl

theorem determinant_order_off_roots (z : ℂ) (hz : ∀ n : ℕ, z ≠ root n) :
    analyticOrderAt regularizedProduct z = 0 :=
  (determinant_entire z).analyticOrderAt_eq_zero.mpr ((determinant_ne_zero_iff z).mpr hz)

theorem determinant_order_finite (z : ℂ) : analyticOrderAt regularizedProduct z ≠ ⊤ := by
  by_cases h : ∃ n : ℕ, z = root n
  · obtain ⟨n, rfl⟩ := h
    rw [determinant_order_at_root]
    simp
  · rw [determinant_order_off_roots z (fun n hn => h ⟨n, hn⟩)]
    simp

end SharedCore.Det4Zeros

#print axioms SharedCore.Det4Zeros.denominator_ne_zero
#print axioms SharedCore.Det4Zeros.multiplicity_positive
#print axioms SharedCore.Det4Zeros.root_injective
#print axioms SharedCore.Det4Zeros.root_norm
#print axioms SharedCore.Det4Zeros.shell_unit_ne_zero
#print axioms SharedCore.Det4Zeros.shell_unit_analytic
#print axioms SharedCore.Det4Zeros.shell_factor
#print axioms SharedCore.Det4Zeros.shell_eq_zero_iff
#print axioms SharedCore.Det4Zeros.determinant_eq_zero_iff
#print axioms SharedCore.Det4Zeros.determinant_root_zero
#print axioms SharedCore.Det4Zeros.determinant_ne_zero_iff
#print axioms SharedCore.Det4Zeros.root_inside_tail_disk
#print axioms SharedCore.Det4Zeros.zero_unit_analytic
#print axioms SharedCore.Det4Zeros.zero_unit_ne_zero
#print axioms SharedCore.Det4Zeros.determinant_local_factor
#print axioms SharedCore.Det4Zeros.determinant_order_at_root
#print axioms SharedCore.Det4Zeros.determinant_order_nat_at_root
#print axioms SharedCore.Det4Zeros.determinant_order_off_roots
#print axioms SharedCore.Det4Zeros.determinant_order_finite
