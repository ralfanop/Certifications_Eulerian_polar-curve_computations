import GegenbauerFock.Section7Closed
import GegenbauerFock.GegenbauerIntrinsicEntireCompactQuasiaffinity
import GegenbauerFock.GegenbauerIntrinsicEntireHSKummer
import GegenbauerFock.UltrasphericalKummerBridge
import GegenbauerFock.MomentEnergyIntegral
import GegenbauerFock.GaussianAreaCoefficientRecovery
import GegenbauerFock.GaussianAreaTrueL2OrthonormalFamily
import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Manuscript 13, Sections 8 and 9

* **Theorem 8.1** (`thm:tail`). With `e_n` the normalized Fock monomials, `Π_{N-1}` the projection
  `F ↦ ∑_{n<N} ⟨e_n, F⟩ e_n` onto `span{e_0,…,e_{N-1}}`, `C_N = Π_{N-1} C` and `c = 1/(4α)`:
  `theorem_8_1_hs_tail` (the HS identity on every source Hilbert basis),
  `theorem_8_1_tail_le` (the two inequalities), `theorem_8_1_rank` (rank `≤ N`),
  `theorem_8_1_opNorm` (`‖C − C_N‖ ≤ ‖C − C_N‖_HS ≤ e^{c/2} √(cᴺ/N!)`),
  `theorem_8_1_approximation_number` (the bound for the `(N+1)`st approximation number),
  `theorem_8_1_schatten` (the Schatten-class statement, in approximation-number form:
  `∑_N (e^{c/2} √(cᴺ/N!))^p < ∞` and `∑_N ‖C − C_N‖^p < ∞` for every `p > 0`).
  Mathlib has no singular values or Schatten classes; none is defined here.
* **Proposition 8.2** (`prop:range`): `proposition_8_2`.
* **Proposition 9.1** (`prop:kernel-balance`): `proposition_9_1`.
* **Lemma 9.2** (`lem:core-extension`): `lemma_9_2` (Mathlib's `LinearPMap.HasCore`) and
  `lemma_9_2_graph` (graph-closure form).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace GegenbauerFock.Section8Section9

open GegenbauerFock.GeneralUltrasphericalFock

/-- The source Hilbert space `L²(ν_λ; ℂ)`. -/
abbrev H (lam : ℝ) : Type := Lp ℂ 2 (Ultraspherical.measure lam)

/-- The Bargmann–Fock space (entire Gaussian-L² classes). -/
abbrev Fock (alpha : ℝ) : Type := Section7Closed.Fock alpha

/-- The normalized Fock monomials `e_n = √(αⁿ/n!) zⁿ`. -/
abbrev e (alpha : ℝ) (ha : 0 < alpha) (n : ℕ) : Fock alpha :=
  GaussianArea.normalizedMonomialIntrinsicVector alpha ha n

/-- The unitary coefficient identification `ℓ² ≅ Fock`. -/
abbrev U (alpha : ℝ) (ha : 0 < alpha) : lp (fun _ : ℕ => ℂ) 2 ≃ₗᵢ[ℂ] Fock alpha :=
  GaussianArea.coefficientIntrinsicEntireEquiv alpha ha

/-- The transform `C_{λ,α} : L²(ν_λ) → Fock`. -/
abbrev Cf (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) : H lam →L[ℂ] Fock alpha :=
  C_intrinsicEntire lam alpha hlam ha

/-! ## The basis `e_n` and the projection `Π_{N-1}` -/

theorem inner_e_U (alpha : ℝ) (ha : 0 < alpha) (a : lp (fun _ : ℕ => ℂ) 2) (n : ℕ) :
    inner ℂ (e alpha ha n) (U alpha ha a) = a n := by
  change inner ℂ (GaussianArea.normalizedMonomialL2Vector alpha ha n)
      (GaussianArea.coefficientSynthesisL2 alpha ha a) = a n
  exact GaussianArea.coefficientSynthesisL2_coefficient alpha ha a n

theorem U_single_one (alpha : ℝ) (ha : 0 < alpha) (n : ℕ) :
    U alpha ha (lp.single 2 n (1 : ℂ)) = e alpha ha n := by
  apply Subtype.ext
  change GaussianArea.coefficientSynthesisL2 alpha ha (lp.single 2 n (1 : ℂ)) =
    GaussianArea.normalizedMonomialL2Vector alpha ha n
  exact GaussianArea.coefficientSynthesisL2_single alpha ha n

theorem U_single (alpha : ℝ) (ha : 0 < alpha) (n : ℕ) (x : ℂ) :
    U alpha ha (lp.single 2 n x) = x • e alpha ha n := by
  have hx : (lp.single 2 n x : lp (fun _ : ℕ => ℂ) 2) =
      x • (lp.single 2 n (1 : ℂ) : lp (fun _ : ℕ => ℂ) 2) := by
    have h := lp.single_smul (E := fun _ : ℕ => ℂ) (𝕜 := ℂ) (2 : ℝ≥0∞) n x (1 : ℂ)
    rw [smul_eq_mul, mul_one] at h
    exact h
  rw [hx, map_smul, U_single_one]

/-- The family `e_n` is orthonormal in the Fock space. -/
theorem e_orthonormal (alpha : ℝ) (ha : 0 < alpha) : Orthonormal ℂ (e alpha ha) := by
  have h := GaussianArea.orthonormal_normalizedMonomialL2Vector alpha ha
  rw [orthonormal_iff_ite] at h ⊢
  intro m n
  exact h m n

/-- `Π_{N-1} F = ∑_{n<N} ⟨e_n, F⟩ e_n`. -/
def proj (alpha : ℝ) (ha : 0 < alpha) (N : ℕ) : Fock alpha →L[ℂ] Fock alpha :=
  ∑ n ∈ Finset.range N, (innerSL ℂ (e alpha ha n)).smulRight (e alpha ha n)

theorem proj_apply (alpha : ℝ) (ha : 0 < alpha) (N : ℕ) (F : Fock alpha) :
    proj alpha ha N F = ∑ n ∈ Finset.range N, inner ℂ (e alpha ha n) F • e alpha ha n := by
  unfold proj
  rw [ContinuousLinearMap.sum_apply]
  exact Finset.sum_congr rfl fun n _ => rfl

/-- `Π_{N-1}` fixes `e_k` for `k < N` and kills `e_k` for `k ≥ N`: it is the orthogonal
projection onto `span{e_0,…,e_{N-1}}`. -/
theorem proj_e (alpha : ℝ) (ha : 0 < alpha) (N k : ℕ) :
    proj alpha ha N (e alpha ha k) = if k < N then e alpha ha k else 0 := by
  classical
  rw [proj_apply]
  have h : ∀ n ∈ Finset.range N, inner ℂ (e alpha ha n) (e alpha ha k) • e alpha ha n =
      if k = n then e alpha ha k else 0 := by
    intro n _
    rw [orthonormal_iff_ite.mp (e_orthonormal alpha ha) n k]
    by_cases hkn : k = n
    · rw [if_pos hkn.symm, if_pos hkn, one_smul, hkn]
    · rw [if_neg (Ne.symm hkn), if_neg hkn, zero_smul]
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq (Finset.range N) k (fun _ => e alpha ha k)]
  by_cases hk : k < N
  · rw [if_pos (Finset.mem_range.mpr hk), if_pos hk]
  · rw [if_neg (fun h' => hk (Finset.mem_range.mp h')), if_neg hk]

theorem proj_mem_span (alpha : ℝ) (ha : 0 < alpha) (N : ℕ) (F : Fock alpha) :
    proj alpha ha N F ∈
      Submodule.span ℂ (Set.range (fun k : Fin N => e alpha ha (k : ℕ))) := by
  rw [proj_apply]
  apply Submodule.sum_mem
  intro n hn
  apply Submodule.smul_mem
  apply Submodule.subset_span
  exact ⟨⟨n, Finset.mem_range.mp hn⟩, rfl⟩

/-- The finite-rank approximant `C_N = Π_{N-1} C`. -/
def CN (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) (N : ℕ) : H lam →L[ℂ] Fock alpha :=
  (proj alpha ha N).comp (Cf lam alpha hlam ha)

/-- `C f − C_N f` is the image under the coefficient unitary of the coefficient-space tail. -/
theorem sub_CN_eq (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) (N : ℕ) (f : H lam) :
    (Cf lam alpha hlam ha - CN lam alpha hlam ha N) f =
      U alpha ha (C lam alpha hlam ha f -
        SummableRowsCompact.truncation (C lam alpha hlam ha) N f) := by
  rw [map_sub, ContinuousLinearMap.sub_apply, SummableRowsCompact.truncation_apply]
  have h1 : Cf lam alpha hlam ha f = U alpha ha (C lam alpha hlam ha f) := rfl
  have h2 : CN lam alpha hlam ha N f =
      U alpha ha (∑ n ∈ Finset.range N, lp.single 2 n ((C lam alpha hlam ha f) n)) := by
    change proj alpha ha N (Cf lam alpha hlam ha f) = _
    rw [proj_apply, map_sum, h1]
    apply Finset.sum_congr rfl
    intro n _
    rw [U_single, inner_e_U]
  rw [h1, h2]

theorem norm_sub_CN (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) (N : ℕ) (f : H lam) :
    ‖(Cf lam alpha hlam ha - CN lam alpha hlam ha N) f‖ =
      ‖C lam alpha hlam ha f - SummableRowsCompact.truncation (C lam alpha hlam ha) N f‖ := by
  rw [sub_CN_eq]
  exact LinearIsometryEquiv.norm_map _ _

/-! ## Row energies -/

/-- `‖row_n C‖² = cⁿ/n! · m_{2n}(λ)` with `m_{2n}(λ) = ∫ u^{2n} dν_λ`. -/
theorem row_norm_sq_eq (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) (n : ℕ) :
    ‖SummableRowsCompact.row (C lam alpha hlam ha) n‖ ^ 2 =
      (1 / (4 * alpha)) ^ n / (n.factorial : ℝ) * Ultraspherical.evenMoment lam n := by
  letI : IsProbabilityMeasure (Ultraspherical.measure lam) :=
    Ultraspherical.probability lam hlam
  rw [row_norm_sq_formula lam alpha hlam ha n,
    MomentEnergyIntegral.monomial_norm_sq_integral (Ultraspherical.measure lam)
      (ae_abs_le_one lam) n]
  have hint : (∫ u : ℝ, ‖(u : ℂ) ^ n‖ ^ 2 ∂(Ultraspherical.measure lam)) =
      Ultraspherical.evenMoment lam n := by
    unfold Ultraspherical.evenMoment
    apply integral_congr_ae
    filter_upwards [] with u
    rw [FockExponentialSeries.norm_monomial_sq, ← pow_mul]
  rw [hint]
  rfl

theorem sum_basis_coord_sq (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    {ι : Type*} (b : HilbertBasis ι ℂ (H lam)) (n : ℕ) :
    (∑' i : ι, ‖(C lam alpha hlam ha (b i)) n‖ ^ 2) =
      ‖SummableRowsCompact.row (C lam alpha hlam ha) n‖ ^ 2 := by
  letI : IsProbabilityMeasure (Ultraspherical.measure lam) :=
    Ultraspherical.probability lam hlam
  rw [C_row_eq lam alpha hlam ha n]
  rw [← FockEnergy.weightedMoment_row_basis_energy (Ultraspherical.measure lam)
    (ae_abs_le_one lam) alpha ha b n]
  apply tsum_congr
  intro i
  rw [C_coefficient lam alpha hlam ha (b i) n]

theorem evenMoment_nonneg_le_one (lam : ℝ) (hlam : 0 < lam) (n : ℕ) :
    0 ≤ Ultraspherical.evenMoment lam n ∧ Ultraspherical.evenMoment lam n ≤ 1 := by
  rw [Ultraspherical.evenMoment_eq_ratio lam hlam n]
  exact KummerCoefficients.ratio_bounds lam hlam n

/-! ## Theorem 8.1 -/

/-- **Theorem 8.1**, equality in (8.1): for every Hilbert basis `b` of `L²(ν_λ)`,
`‖C − C_N‖²_HS = ∑_{n ≥ N} cⁿ/n! · m_{2n}(λ)`, `c = 1/(4α)`. -/
theorem theorem_8_1_hs_tail (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) (N : ℕ)
    {ι : Type*} (b : HilbertBasis ι ℂ (H lam)) :
    (∑' i : ι, ‖(Cf lam alpha hlam ha - CN lam alpha hlam ha N) (b i)‖ ^ 2) =
      ∑' m : ℕ, (1 / (4 * alpha)) ^ (m + N) / ((m + N).factorial : ℝ) *
        Ultraspherical.evenMoment lam (m + N) := by
  set T := C lam alpha hlam ha
  have hk := C_rows_summable lam alpha hlam ha
  let w : ℕ → ι → ℝ := fun m i => ‖(T (b i)) (m + N)‖ ^ 2
  have hin (i : ι) : ‖(Cf lam alpha hlam ha - CN lam alpha hlam ha N) (b i)‖ ^ 2 =
      ∑' m : ℕ, w m i := by
    rw [norm_sub_CN]
    exact SummableRowsCompact.error_norm_sq_tail T hk (b i) N
  have hHS : Summable (fun i : ι => ‖T (b i)‖ ^ 2) := by
    have h := C_intrinsicEntire_HS_basis_summable lam alpha hlam ha b
    refine h.congr ?_
    intro i
    rw [C_intrinsicEntire_norm]
  have hs_row (m : ℕ) : Summable (w m) := by
    refine Summable.of_nonneg_of_le (fun i => sq_nonneg _) ?_ hHS
    intro i
    have h1 : ‖(T (b i)) (m + N)‖ ≤ ‖T (b i)‖ :=
      lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) (T (b i)) (m + N)
    have h0 : 0 ≤ ‖(T (b i)) (m + N)‖ := norm_nonneg _
    change ‖(T (b i)) (m + N)‖ ^ 2 ≤ ‖T (b i)‖ ^ 2
    nlinarith
  have hrow (m : ℕ) : (∑' i : ι, w m i) = ‖SummableRowsCompact.row T (m + N)‖ ^ 2 :=
    sum_basis_coord_sq lam alpha hlam ha b (m + N)
  have hs_outer : Summable (fun m : ℕ => ∑' i : ι, w m i) := by
    have h := (summable_nat_add_iff N).mpr hk
    refine h.congr ?_
    intro m
    exact (hrow m).symm
  have hdouble : Summable (Function.uncurry w) := by
    apply (summable_prod_of_nonneg (f := Function.uncurry w) (fun p => sq_nonneg _)).2
    exact ⟨hs_row, hs_outer⟩
  calc
    (∑' i : ι, ‖(Cf lam alpha hlam ha - CN lam alpha hlam ha N) (b i)‖ ^ 2) =
        ∑' i : ι, ∑' m : ℕ, w m i := tsum_congr hin
    _ = ∑' m : ℕ, ∑' i : ι, w m i := hdouble.tsum_comm
    _ = ∑' m : ℕ, ‖SummableRowsCompact.row T (m + N)‖ ^ 2 := tsum_congr hrow
    _ = _ := by
      apply tsum_congr
      intro m
      exact row_norm_sq_eq lam alpha hlam ha (m + N)

/-- The coefficient-space tail `∑_{m} ‖row_{m+N}‖²` equals the same series. -/
theorem tail_eq (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) (N : ℕ) :
    SummableRowsCompact.tail (C lam alpha hlam ha) N =
      ∑' m : ℕ, (1 / (4 * alpha)) ^ (m + N) / ((m + N).factorial : ℝ) *
        Ultraspherical.evenMoment lam (m + N) := by
  unfold SummableRowsCompact.tail
  apply tsum_congr
  intro m
  exact row_norm_sq_eq lam alpha hlam ha (m + N)

theorem exp_tsum_le (c : ℝ) (hc : 0 ≤ c) :
    (∑' m : ℕ, c ^ m / (m.factorial : ℝ)) ≤ Real.exp c := by
  apply Real.tsum_le_of_sum_range_le
  · intro n
    positivity
  · intro n
    exact Real.sum_le_exp_of_nonneg hc n

theorem shifted_term_le (c : ℝ) (hc : 0 ≤ c) (N m : ℕ) :
    c ^ (m + N) / ((m + N).factorial : ℝ) ≤
      c ^ N / (N.factorial : ℝ) * (c ^ m / (m.factorial : ℝ)) := by
  have hfac : ((m.factorial : ℝ) * (N.factorial : ℝ)) ≤ ((m + N).factorial : ℝ) := by
    have h := Nat.le_of_dvd (Nat.factorial_pos (m + N))
      (Nat.factorial_mul_factorial_dvd_factorial_add m N)
    exact_mod_cast h
  have hpos : 0 < (m.factorial : ℝ) * (N.factorial : ℝ) := by positivity
  have hnum : 0 ≤ c ^ (m + N) := pow_nonneg hc _
  calc
    c ^ (m + N) / ((m + N).factorial : ℝ) ≤
        c ^ (m + N) / ((m.factorial : ℝ) * (N.factorial : ℝ)) :=
      by first
        | exact div_le_div_of_nonneg_left hnum hpos hfac
        | exact div_le_div_of_le_left hnum hpos hfac
    _ = c ^ N / (N.factorial : ℝ) * (c ^ m / (m.factorial : ℝ)) := by
      rw [pow_add]
      ring

/-- **Theorem 8.1**, the inequalities in (8.1):
`∑_{n≥N} cⁿ/n! m_{2n}(λ) ≤ ∑_{n≥N} cⁿ/n! ≤ e^c cᴺ/N!`. -/
theorem theorem_8_1_tail_le (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) (N : ℕ) :
    (∑' m : ℕ, (1 / (4 * alpha)) ^ (m + N) / ((m + N).factorial : ℝ) *
        Ultraspherical.evenMoment lam (m + N)) ≤
      ∑' m : ℕ, (1 / (4 * alpha)) ^ (m + N) / ((m + N).factorial : ℝ) ∧
    (∑' m : ℕ, (1 / (4 * alpha)) ^ (m + N) / ((m + N).factorial : ℝ)) ≤
      Real.exp (1 / (4 * alpha)) * ((1 / (4 * alpha)) ^ N / (N.factorial : ℝ)) := by
  set c : ℝ := 1 / (4 * alpha) with hcdef
  have hc : 0 ≤ c := by positivity
  have hsum : Summable (fun m : ℕ => c ^ (m + N) / ((m + N).factorial : ℝ)) :=
    (summable_nat_add_iff N).mpr (Real.summable_pow_div_factorial c)
  constructor
  · have hle : ∀ m : ℕ, c ^ (m + N) / ((m + N).factorial : ℝ) *
        Ultraspherical.evenMoment lam (m + N) ≤ c ^ (m + N) / ((m + N).factorial : ℝ) := by
      intro m
      have hm := evenMoment_nonneg_le_one lam hlam (m + N)
      have ht : 0 ≤ c ^ (m + N) / ((m + N).factorial : ℝ) := by positivity
      nlinarith [hm.1, hm.2]
    have hs1 : Summable (fun m : ℕ => c ^ (m + N) / ((m + N).factorial : ℝ) *
        Ultraspherical.evenMoment lam (m + N)) := by
      refine Summable.of_nonneg_of_le ?_ hle hsum
      intro m
      have hm := evenMoment_nonneg_le_one lam hlam (m + N)
      have ht : 0 ≤ c ^ (m + N) / ((m + N).factorial : ℝ) := by positivity
      exact mul_nonneg ht hm.1
    exact hs1.tsum_le_tsum hle hsum
  · have he : Summable (fun m : ℕ => c ^ N / (N.factorial : ℝ) * (c ^ m / (m.factorial : ℝ))) :=
      (Real.summable_pow_div_factorial c).mul_left _
    calc
      (∑' m : ℕ, c ^ (m + N) / ((m + N).factorial : ℝ)) ≤
          ∑' m : ℕ, c ^ N / (N.factorial : ℝ) * (c ^ m / (m.factorial : ℝ)) :=
        hsum.tsum_le_tsum (shifted_term_le c hc N) he
      _ = c ^ N / (N.factorial : ℝ) * ∑' m : ℕ, c ^ m / (m.factorial : ℝ) := tsum_mul_left
      _ ≤ c ^ N / (N.factorial : ℝ) * Real.exp c :=
        mul_le_mul_of_nonneg_left (exp_tsum_le c hc) (by positivity)
      _ = Real.exp c * (c ^ N / (N.factorial : ℝ)) := mul_comm _ _

/-- `√(e^c · x) = e^{c/2} √x`. -/
theorem sqrt_exp_mul (c x : ℝ) :
    Real.sqrt (Real.exp c * x) = Real.exp (c / 2) * Real.sqrt x := by
  have h : Real.exp c = Real.exp (c / 2) * Real.exp (c / 2) := by
    rw [← Real.exp_add, add_halves]
  rw [Real.sqrt_mul (Real.exp_pos c).le, h, Real.sqrt_mul_self (Real.exp_pos _).le]

/-- The squared HS norm of `C − C_N` (on any Hilbert basis) is at most `e^c cᴺ/N!`. -/
theorem hs_sq_le (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) (N : ℕ)
    {ι : Type*} (b : HilbertBasis ι ℂ (H lam)) :
    (∑' i : ι, ‖(Cf lam alpha hlam ha - CN lam alpha hlam ha N) (b i)‖ ^ 2) ≤
      Real.exp (1 / (4 * alpha)) * ((1 / (4 * alpha)) ^ N / (N.factorial : ℝ)) := by
  rw [theorem_8_1_hs_tail lam alpha hlam ha N b]
  obtain ⟨h1, h2⟩ := theorem_8_1_tail_le lam alpha hlam ha N
  exact h1.trans h2

/-- **Theorem 8.1**, operator-norm form of (8.2):
`‖C − C_N‖_op ≤ ‖C − C_N‖_HS ≤ e^{c/2} √(cᴺ/N!)`, the HS norm taken on any Hilbert basis. -/
theorem theorem_8_1_opNorm (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) (N : ℕ)
    {ι : Type*} (b : HilbertBasis ι ℂ (H lam)) :
    ‖Cf lam alpha hlam ha - CN lam alpha hlam ha N‖ ≤
        Real.sqrt (∑' i : ι, ‖(Cf lam alpha hlam ha - CN lam alpha hlam ha N) (b i)‖ ^ 2) ∧
      Real.sqrt (∑' i : ι, ‖(Cf lam alpha hlam ha - CN lam alpha hlam ha N) (b i)‖ ^ 2) ≤
        Real.exp (1 / (4 * alpha) / 2) *
          Real.sqrt ((1 / (4 * alpha)) ^ N / (N.factorial : ℝ)) := by
  constructor
  · rw [theorem_8_1_hs_tail lam alpha hlam ha N b, ← tail_eq lam alpha hlam ha N]
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro f
    rw [norm_sub_CN]
    have hop := SummableRowsCompact.operator_error_norm_bound (C lam alpha hlam ha)
      (C_rows_summable lam alpha hlam ha) N
    calc
      ‖C lam alpha hlam ha f - SummableRowsCompact.truncation (C lam alpha hlam ha) N f‖ =
          ‖(C lam alpha hlam ha - SummableRowsCompact.truncation (C lam alpha hlam ha) N) f‖ :=
        rfl
      _ ≤ ‖C lam alpha hlam ha - SummableRowsCompact.truncation (C lam alpha hlam ha) N‖ *
          ‖f‖ := ContinuousLinearMap.le_opNorm _ f
      _ ≤ Real.sqrt (SummableRowsCompact.tail (C lam alpha hlam ha) N) * ‖f‖ :=
        mul_le_mul_of_nonneg_right hop (norm_nonneg f)
  · rw [← sqrt_exp_mul]
    exact Real.sqrt_le_sqrt (hs_sq_le lam alpha hlam ha N b)

/-- **Theorem 8.1**: `C_N` has rank at most `N`. -/
theorem theorem_8_1_rank (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) (N : ℕ) :
    FiniteDimensional ℂ (LinearMap.range (CN lam alpha hlam ha N).toLinearMap) ∧
      Module.finrank ℂ (LinearMap.range (CN lam alpha hlam ha N).toLinearMap) ≤ N := by
  set V := Submodule.span ℂ (Set.range (fun k : Fin N => e alpha ha (k : ℕ)))
  have hle : LinearMap.range (CN lam alpha hlam ha N).toLinearMap ≤ V := by
    rintro _ ⟨f, rfl⟩
    exact proj_mem_span alpha ha N _
  haveI hV : FiniteDimensional ℂ V :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  refine ⟨Submodule.finiteDimensional_of_le hle, ?_⟩
  calc
    Module.finrank ℂ (LinearMap.range (CN lam alpha hlam ha N).toLinearMap) ≤ Module.finrank ℂ V :=
      Submodule.finrank_mono hle
    _ ≤ Fintype.card (Fin N) := finrank_range_le_card _
    _ = N := Fintype.card_fin N

/-- The bound `e^{c/2} √(cᴺ/N!)` of (8.2). -/
def tailBound (alpha : ℝ) (N : ℕ) : ℝ :=
  Real.exp (1 / (4 * alpha) / 2) * Real.sqrt ((1 / (4 * alpha)) ^ N / (N.factorial : ℝ))

theorem opNorm_sub_CN_le (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) (N : ℕ) :
    ‖Cf lam alpha hlam ha - CN lam alpha hlam ha N‖ ≤ tailBound alpha N := by
  letI : IsProbabilityMeasure (Ultraspherical.measure lam) :=
    Ultraspherical.probability lam hlam
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ (H lam)
  obtain ⟨h1, h2⟩ := theorem_8_1_opNorm lam alpha hlam ha N b
  exact h1.trans h2

/-- **Theorem 8.1**, (8.2) in approximation-number form: there is an operator of rank `≤ N`
(namely `C_N`) at operator-norm distance `≤ e^{c/2} √(cᴺ/N!)` from `C`; hence the `(N+1)`st
approximation number `a_{N+1}(C) = inf{‖C − T‖ : rank T ≤ N}` (equal to `s_{N+1}(C)` in Hilbert
spaces) obeys the bound. -/
theorem theorem_8_1_approximation_number (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (N : ℕ) :
    ∃ T : H lam →L[ℂ] Fock alpha,
      FiniteDimensional ℂ (LinearMap.range T.toLinearMap) ∧ Module.finrank ℂ (LinearMap.range T.toLinearMap) ≤ N ∧
      ‖Cf lam alpha hlam ha - T‖ ≤
        Real.exp (1 / (4 * alpha) / 2) * Real.sqrt ((1 / (4 * alpha)) ^ N / (N.factorial : ℝ)) :=
  ⟨CN lam alpha hlam ha N, (theorem_8_1_rank lam alpha hlam ha N).1,
    (theorem_8_1_rank lam alpha hlam ha N).2, opNorm_sub_CN_le lam alpha hlam ha N⟩

theorem pow_div_factorial_le_geom (c : ℝ) (hc : 0 ≤ c) (N : ℕ) :
    c ^ N / (N.factorial : ℝ) ≤
      (∑' n : ℕ, (4 * c) ^ n / (n.factorial : ℝ)) * ((1 / 2) ^ N) ^ 2 := by
  have hs := Real.summable_pow_div_factorial (4 * c)
  have hle : (4 * c) ^ N / (N.factorial : ℝ) ≤ ∑' n : ℕ, (4 * c) ^ n / (n.factorial : ℝ) :=
    hs.le_tsum N (fun j _ => by positivity)
  have heq : c ^ N / (N.factorial : ℝ) = (4 * c) ^ N / (N.factorial : ℝ) * ((1 / 2) ^ N) ^ 2 := by
    have h4 : ((1 / 2 : ℝ) ^ N) ^ 2 = (1 / 4 : ℝ) ^ N := by
      rw [← pow_mul, mul_comm N 2, pow_mul]
      norm_num
    have h41 : (4 : ℝ) ^ N * (1 / 4 : ℝ) ^ N = 1 := by
      rw [← mul_pow]
      norm_num
    rw [h4, mul_pow,
      show (4 : ℝ) ^ N * c ^ N / (N.factorial : ℝ) * (1 / 4 : ℝ) ^ N =
        ((4 : ℝ) ^ N * (1 / 4 : ℝ) ^ N) * (c ^ N / (N.factorial : ℝ)) by ring,
      h41, one_mul]
  rw [heq]
  exact mul_le_mul_of_nonneg_right hle (by positivity)

/-- **Theorem 8.1**, Schatten statement in approximation-number form: for every `p > 0`,
`∑_N (e^{c/2} √(cᴺ/N!))^p < ∞`, hence `∑_N ‖C − C_N‖^p < ∞` with `rank C_N ≤ N`. -/
theorem theorem_8_1_schatten (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (p : ℝ) (hp : 0 < p) :
    Summable (fun N : ℕ => (tailBound alpha N) ^ p) ∧
      Summable (fun N : ℕ => ‖Cf lam alpha hlam ha - CN lam alpha hlam ha N‖ ^ p) := by
  set c : ℝ := 1 / (4 * alpha) with hcdef
  have hc : 0 ≤ c := by positivity
  set M : ℝ := ∑' n : ℕ, (4 * c) ^ n / (n.factorial : ℝ)
  have hM : 0 ≤ M := tsum_nonneg (fun n => by positivity)
  set K : ℝ := Real.exp (c / 2) * Real.sqrt M
  have hK : 0 ≤ K := mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _)
  have hbound : ∀ N : ℕ, tailBound alpha N ≤ K * (1 / 2) ^ N := by
    intro N
    unfold tailBound
    rw [← hcdef]
    have h1 := Real.sqrt_le_sqrt (pow_div_factorial_le_geom c hc N)
    rw [Real.sqrt_mul hM, Real.sqrt_sq (by positivity)] at h1
    calc
      Real.exp (c / 2) * Real.sqrt (c ^ N / (N.factorial : ℝ)) ≤
          Real.exp (c / 2) * (Real.sqrt M * (1 / 2) ^ N) :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = K * (1 / 2) ^ N := by ring
  have hnn : ∀ N : ℕ, 0 ≤ tailBound alpha N := fun N =>
    mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _)
  have hgeom : Summable (fun N : ℕ => K ^ p * ((1 / 2 : ℝ) ^ p) ^ N) :=
    (summable_geometric_of_lt_one (Real.rpow_nonneg (by norm_num) p)
      (Real.rpow_lt_one (by norm_num) (by norm_num) hp)).mul_left _
  have hcomp : ∀ N : ℕ, (K * (1 / 2 : ℝ) ^ N) ^ p = K ^ p * ((1 / 2 : ℝ) ^ p) ^ N := by
    intro N
    rw [Real.mul_rpow hK (by positivity)]
    congr 1
    rw [← Real.rpow_natCast (1 / 2 : ℝ) N, ← Real.rpow_mul (by norm_num), mul_comm,
      Real.rpow_mul (by norm_num), Real.rpow_natCast]
  have hS : Summable (fun N : ℕ => (tailBound alpha N) ^ p) := by
    refine Summable.of_nonneg_of_le (fun N => Real.rpow_nonneg (hnn N) p) ?_ hgeom
    intro N
    rw [← hcomp N]
    exact Real.rpow_le_rpow (hnn N) (hbound N) hp.le
  refine ⟨hS, ?_⟩
  refine Summable.of_nonneg_of_le
    (fun N => Real.rpow_nonneg (norm_nonneg (Cf lam alpha hlam ha - CN lam alpha hlam ha N)) p)
    ?_ hS
  intro N
  exact Real.rpow_le_rpow (norm_nonneg (Cf lam alpha hlam ha - CN lam alpha hlam ha N))
    (opNorm_sub_CN_le lam alpha hlam ha N) hp.le

/-! ## Proposition 8.2 -/

/-- A compact injective operator from an infinite-dimensional Banach space into a Banach space
has nonclosed range: with closed range it would be invertible onto its range (bounded inverse
theorem), making the identity of the source compact. -/
theorem range_not_closed_of_compact_injective {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (T : E →L[ℂ] F) (hc : IsCompactOperator T) (hi : Function.Injective T)
    (hE : ¬ FiniteDimensional ℂ E) :
    ¬ IsClosed (LinearMap.range T.toLinearMap : Set F) := by
  intro hcl
  set R := LinearMap.range T.toLinearMap
  haveI : CompleteSpace R := hcl.completeSpace_coe
  have hmem : ∀ x, T x ∈ R := fun x => LinearMap.mem_range_self T.toLinearMap x
  let T' : E →L[ℂ] R := T.codRestrict R hmem
  have hT'inj : LinearMap.ker T' = ⊥ := by
    apply LinearMap.ker_eq_bot.mpr
    intro x y hxy
    apply hi
    have := congrArg Subtype.val hxy
    exact this
  have hT'surj : LinearMap.range T' = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    rintro ⟨_, ⟨x, rfl⟩⟩
    exact ⟨x, rfl⟩
  let eq : E ≃L[ℂ] R := ContinuousLinearEquiv.ofBijective T' hT'inj hT'surj
  have hcT' : IsCompactOperator (T' : E → R) := hc.codRestrict hmem hcl
  have hid : IsCompactOperator ((eq.symm : R →L[ℂ] E) ∘ (T' : E → R)) :=
    hcT'.clm_comp (eq.symm : R →L[ℂ] E)
  have hfun : ((eq.symm : R →L[ℂ] E) ∘ (T' : E → R)) = (id : E → E) := by
    funext x
    exact eq.symm_apply_apply x
  rw [hfun] at hid
  have hK := (show IsCompactOperator (LinearMap.id : E →ₗ[ℂ] E) from hid).isCompact_closure_image_closedBall 1
  rw [LinearMap.id_coe, Set.image_id, Metric.isClosed_closedBall.closure_eq] at hK
  exact hE (FiniteDimensional.of_isCompact_closedBall₀ ℂ one_pos hK)

/-- The Fock space is infinite-dimensional. -/
theorem fock_not_finiteDimensional (alpha : ℝ) (ha : 0 < alpha) :
    ¬ FiniteDimensional ℂ (Fock alpha) := by
  intro h
  haveI := h
  apply fockCoefficients_not_finiteDimensional
  exact LinearEquiv.finiteDimensional (U alpha ha).symm.toLinearEquiv

theorem Cf_denseRange (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    DenseRange (Cf lam alpha hlam ha) :=
  Section7Closed.C_intrinsicEntire_denseRange lam alpha hlam ha

/-- The source `L²(ν_λ)` is infinite-dimensional (else the dense range of `C` would be
finite-dimensional, hence closed, hence everything, against non-surjectivity). -/
theorem source_not_finiteDimensional (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ¬ FiniteDimensional ℂ (H lam) := by
  intro h
  haveI := h
  have hcl : IsClosed (LinearMap.range (Cf lam alpha hlam ha).toLinearMap : Set (Fock alpha)) :=
    Submodule.closed_of_finiteDimensional _
  have hcl' : IsClosed (Set.range (Cf lam alpha hlam ha)) := by
    have h2 := hcl
    rw [LinearMap.coe_range] at h2
    exact h2
  have huniv : Set.range (Cf lam alpha hlam ha) = Set.univ := by
    rw [← hcl'.closure_eq]
    exact (Cf_denseRange lam alpha hlam ha).closure_range
  apply C_intrinsicEntire_not_surjective lam alpha hlam ha
  intro F
  have hF : F ∈ Set.range (Cf lam alpha hlam ha) := by
    rw [huniv]
    exact Set.mem_univ F
  exact hF

/-- The manuscript's Gram operator `S_{λ,c} = C*C` (library `C_intrinsicEntire_gram`). -/
abbrev S (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) : H lam →L[ℂ] H lam :=
  C_intrinsicEntire_gram lam alpha hlam ha

/-- `S` coincides with the coefficient-space Gram `gram = C*C` of the library. -/
theorem S_eq_gram (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    S lam alpha hlam ha = gram lam alpha hlam ha := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_right ℂ
  intro g
  exact C_intrinsicEntire_gram_pairing lam alpha hlam ha f g

theorem S_norm_sq (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) (f : H lam) :
    ‖Cf lam alpha hlam ha f‖ ^ 2 = RCLike.re (inner ℂ (S lam alpha hlam ha f) f) := by
  letI : CompleteSpace (GaussianArea.entireGaussianL2Submodule alpha) :=
    (GaussianArea.intrinsicEntire_isClosed alpha ha).completeSpace_coe
  exact HilbertGram.gram_norm_sq (C_intrinsicEntire lam alpha hlam ha) f

theorem S_adjoint (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (S lam alpha hlam ha).adjoint = S lam alpha hlam ha := by
  letI : CompleteSpace (GaussianArea.entireGaussianL2Submodule alpha) :=
    (GaussianArea.intrinsicEntire_isClosed alpha ha).completeSpace_coe
  exact HilbertGram.gram_adjoint (C_intrinsicEntire lam alpha hlam ha)

theorem S_compact (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    IsCompactOperator (S lam alpha hlam ha) := by
  letI : CompleteSpace (GaussianArea.entireGaussianL2Submodule alpha) :=
    (GaussianArea.intrinsicEntire_isClosed alpha ha).completeSpace_coe
  exact HilbertGram.gram_compact (C_intrinsicEntire lam alpha hlam ha)
    (C_intrinsicEntire_compact lam alpha hlam ha)

theorem S_eq_zero (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) (f : H lam)
    (hf : S lam alpha hlam ha f = 0) : f = 0 := by
  have h := S_norm_sq lam alpha hlam ha f
  rw [hf, inner_zero_left, map_zero] at h
  have h0 : Cf lam alpha hlam ha f = 0 := by
    have := pow_eq_zero_iff (n := 2) (two_ne_zero) |>.mp h
    exact norm_eq_zero.mp this
  apply C_intrinsicEntire_injective lam alpha hlam ha
  rw [h0, map_zero]

theorem S_injective (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    Function.Injective (S lam alpha hlam ha) := by
  intro f g hfg
  have h := S_eq_zero lam alpha hlam ha (f - g) (by rw [map_sub, hfg, sub_self])
  exact sub_eq_zero.mp h

theorem S_ker_eq_bot (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    LinearMap.ker (S lam alpha hlam ha).toLinearMap = ⊥ :=
  (Submodule.eq_bot_iff _).mpr fun x hx => S_eq_zero lam alpha hlam ha x (LinearMap.mem_ker.mp hx)

theorem S_dense_range (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (LinearMap.range (S lam alpha hlam ha).toLinearMap).topologicalClosure = ⊤ := by
  have h0 := ContinuousLinearMap.orthogonal_ker (S lam alpha hlam ha)
  rw [S_adjoint] at h0
  have h : (LinearMap.ker (S lam alpha hlam ha).toLinearMap)ᗮ =
      (LinearMap.range (S lam alpha hlam ha).toLinearMap).topologicalClosure := h0
  rw [← h, S_ker_eq_bot lam alpha hlam ha, Submodule.bot_orthogonal_eq_top]

theorem isUnit_surjective {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {T : X →L[ℂ] X} (hT : IsUnit T) : Function.Surjective T := by
  obtain ⟨u, rfl⟩ := hT
  intro y
  refine ⟨(↑u⁻¹ : X →L[ℂ] X) y, ?_⟩
  show ((↑u : X →L[ℂ] X) * ↑u⁻¹) y = y
  rw [Units.mul_inv]
  rfl

/-- **Proposition 8.2** (13). `C` is injective with dense, proper, nonclosed range in the
infinite-dimensional Fock space; the Gram operator `S = C*C` is injective with dense range,
`ker S = {0}` and `0 ∈ spec S`; zero is not an eigenvalue and `S` is not onto
(zero lies in the continuous spectrum). -/
theorem proposition_8_2 (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ¬ FiniteDimensional ℂ (Fock alpha) ∧
    Function.Injective (Cf lam alpha hlam ha) ∧
    DenseRange (Cf lam alpha hlam ha) ∧
    ¬ Function.Surjective (Cf lam alpha hlam ha) ∧
    ¬ IsClosed (LinearMap.range (Cf lam alpha hlam ha).toLinearMap : Set (Fock alpha)) ∧
    Function.Injective (S lam alpha hlam ha) ∧
    (LinearMap.range (S lam alpha hlam ha).toLinearMap).topologicalClosure = ⊤ ∧
    (0 : ℂ) ∈ spectrum ℂ (S lam alpha hlam ha) ∧
    LinearMap.ker (S lam alpha hlam ha).toLinearMap = ⊥ ∧
    ¬ Function.Surjective (S lam alpha hlam ha) := by
  letI : CompleteSpace (GaussianArea.entireGaussianL2Submodule alpha) :=
    (GaussianArea.intrinsicEntire_isClosed alpha ha).completeSpace_coe
  have hsrc := source_not_finiteDimensional lam alpha hlam ha
  have hSnc : ¬ IsClosed (LinearMap.range (S lam alpha hlam ha).toLinearMap : Set (H lam)) :=
    range_not_closed_of_compact_injective (S lam alpha hlam ha) (S_compact lam alpha hlam ha)
      (S_injective lam alpha hlam ha) hsrc
  have hSns : ¬ Function.Surjective (S lam alpha hlam ha) := by
    intro hs
    apply hSnc
    have htop : LinearMap.range (S lam alpha hlam ha).toLinearMap = ⊤ :=
      LinearMap.range_eq_top.mpr hs
    rw [htop, Submodule.top_coe]
    exact isClosed_univ
  refine ⟨fock_not_finiteDimensional alpha ha, C_intrinsicEntire_injective lam alpha hlam ha,
    Cf_denseRange lam alpha hlam ha, C_intrinsicEntire_not_surjective lam alpha hlam ha,
    range_not_closed_of_compact_injective (Cf lam alpha hlam ha)
      (C_intrinsicEntire_compact lam alpha hlam ha)
      (C_intrinsicEntire_injective lam alpha hlam ha) hsrc,
    S_injective lam alpha hlam ha, S_dense_range lam alpha hlam ha, ?_,
    S_ker_eq_bot lam alpha hlam ha, hSns⟩
  apply spectrum.zero_mem ℂ
  intro hu
  exact hSns (isUnit_surjective hu)

/-! ## Proposition 9.1 -/

/-- The differential expression `A_{λ,c} f = −(1−u²) f'' + (2λ+1) u f' − c² u² f`. -/
def Aexpr (lam c : ℝ) (f : ℝ → ℝ) (u : ℝ) : ℝ :=
  -(1 - u ^ 2) * iteratedDeriv 2 f u + (2 * lam + 1) * u * deriv f u - c ^ 2 * u ^ 2 * f u

/-- The exponential Gram kernel `K_c(u,v) = e^{cuv}`. -/
def K (c u v : ℝ) : ℝ := Real.exp (c * u * v)

theorem deriv_exp_lin (a : ℝ) : deriv (fun x : ℝ => Real.exp (a * x)) =
    fun x => a * Real.exp (a * x) := by
  funext x
  have h : HasDerivAt (fun x : ℝ => Real.exp (a * x)) (Real.exp (a * x) * (a * 1)) x :=
    ((hasDerivAt_id x).const_mul a).exp
  rw [h.deriv, mul_one, mul_comm]

theorem iteratedDeriv_two_exp_lin (a : ℝ) : iteratedDeriv 2 (fun x : ℝ => Real.exp (a * x)) =
    fun x => a ^ 2 * Real.exp (a * x) := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, deriv_exp_lin]
  funext x
  have h : HasDerivAt (fun x : ℝ => a * Real.exp (a * x)) (a * (Real.exp (a * x) * (a * 1))) x :=
    (((hasDerivAt_id x).const_mul a).exp).const_mul a
  rw [h.deriv]
  ring

theorem Aexpr_exp_lin (lam c a u : ℝ) :
    Aexpr lam c (fun x : ℝ => Real.exp (a * x)) u =
      (-(1 - u ^ 2) * a ^ 2 + (2 * lam + 1) * u * a - c ^ 2 * u ^ 2) * Real.exp (a * u) := by
  unfold Aexpr
  rw [iteratedDeriv_two_exp_lin, deriv_exp_lin]
  ring

/-- **Proposition 9.1** (13). For all real `u, v`,
`(A^{(u)}_{λ,c} K_c)(u,v) = (A^{(v)}_{λ,c} K_c)(u,v)`, the differential expression applied in
the first, respectively second, variable. -/
theorem proposition_9_1 (lam c u v : ℝ) :
    Aexpr lam c (fun x => K c x v) u = Aexpr lam c (fun y => K c u y) v := by
  have hu : (fun x => K c x v) = fun x : ℝ => Real.exp ((c * v) * x) := by
    funext x
    unfold K
    ring_nf
  have hv : (fun y => K c u y) = fun y : ℝ => Real.exp ((c * u) * y) := by
    funext y
    unfold K
    ring_nf
  rw [hu, hv, Aexpr_exp_lin, Aexpr_exp_lin]
  have he : (c * v) * u = (c * u) * v := by ring
  rw [he]
  ring

/-! ## Lemma 9.2 -/

/-- **Lemma 9.2** (graph-closure form). `A` closed, `S` bounded, `P ⊆ Dom A` with
`closure(graph(A|_P)) = graph A`, `S P ⊆ Dom A` and `A S p = S A p` on `P`. Then
`S Dom A ⊆ Dom A` and `A S f = S A f` on `Dom A`. -/
theorem lemma_9_2_graph {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : E →ₗ.[ℂ] E) (hA : A.IsClosed) (T : E →L[ℂ] E) (P : Submodule ℂ E)
    (hP : P ≤ A.domain)
    (hcore : (A.domRestrict P).graph.topologicalClosure = A.graph)
    (hTP : ∀ p ∈ P, T p ∈ A.domain)
    (hcomm : ∀ (p : E) (hp : p ∈ P), A ⟨T p, hTP p hp⟩ = T (A ⟨p, hP hp⟩)) :
    (∀ f ∈ A.domain, T f ∈ A.domain) ∧
      ∀ (f : E) (hf : f ∈ A.domain) (hTf : T f ∈ A.domain),
        A ⟨T f, hTf⟩ = T (A ⟨f, hf⟩) := by
  let Φ : E × E →L[ℂ] E × E := T.prodMap T
  have hΦ : ∀ x : E × E, Φ x = (T x.1, T x.2) := fun x => rfl
  have hmaps : Set.MapsTo Φ ((A.domRestrict P).graph : Set (E × E)) (A.graph : Set (E × E)) := by
    rintro ⟨x, y⟩ hxy
    rw [SetLike.mem_coe, LinearPMap.mem_graph_iff] at hxy
    obtain ⟨z, hz1, hz2⟩ := hxy
    have hzP : (z : E) ∈ P := (Submodule.mem_inf.mp z.2).1
    have hzD : (z : E) ∈ A.domain := (Submodule.mem_inf.mp z.2).2
    have hz2y : (A.domRestrict P) z = y := hz2
    have hz2' : A ⟨z, hzD⟩ = y := by
      rw [← hz2y]
      exact (LinearPMap.domRestrict_apply rfl).symm
    rw [SetLike.mem_coe, hΦ, LinearPMap.mem_graph_iff]
    have hx : x = (z : E) := hz1.symm
    subst hx
    refine ⟨⟨T z, hTP z hzP⟩, rfl, ?_⟩
    change A ⟨T z, hTP z hzP⟩ = T y
    rw [hcomm z hzP, ← hz2']
  have hcl := hmaps.closure Φ.continuous
  rw [← Submodule.topologicalClosure_coe, hcore] at hcl
  have hAc : closure (A.graph : Set (E × E)) = A.graph := hA.closure_eq
  rw [hAc] at hcl
  have key : ∀ (f : E) (hf : f ∈ A.domain), ∃ y : A.domain, (y : E) = T f ∧
      A y = T (A ⟨f, hf⟩) := by
    intro f hf
    have hm : ((f, A ⟨f, hf⟩) : E × E) ∈ (A.graph : Set (E × E)) := A.mem_graph ⟨f, hf⟩
    have h := hcl hm
    rw [SetLike.mem_coe, hΦ, LinearPMap.mem_graph_iff] at h
    exact h
  refine ⟨fun f hf => ?_, fun f hf hTf => ?_⟩
  · obtain ⟨y, hy1, _⟩ := key f hf
    rw [← hy1]
    exact y.2
  · obtain ⟨y, hy1, hy2⟩ := key f hf
    have hyeq : (⟨T f, hTf⟩ : A.domain) = y := Subtype.ext hy1.symm
    rw [hyeq, hy2]

/-- **Lemma 9.2** (13), with Mathlib's notion of core: `A` closed on a Hilbert space, `S`
bounded, `P` a core of `A` (`P ⊆ Dom A`, closure of `A|_P` equal to `A`), `S P ⊆ Dom A` and
`A S p = S A p` on `P`. Then `S Dom A ⊆ Dom A` and `A S f = S A f` for every `f ∈ Dom A`. -/
theorem lemma_9_2 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (A : E →ₗ.[ℂ] E) (hA : A.IsClosed) (T : E →L[ℂ] E) (P : Submodule ℂ E)
    (hcore : A.HasCore P)
    (hTP : ∀ p ∈ P, T p ∈ A.domain)
    (hcomm : ∀ (p : E) (hp : p ∈ P), A ⟨T p, hTP p hp⟩ = T (A ⟨p, hcore.le_domain hp⟩)) :
    (∀ f ∈ A.domain, T f ∈ A.domain) ∧
      ∀ (f : E) (hf : f ∈ A.domain) (hTf : T f ∈ A.domain),
        A ⟨T f, hTf⟩ = T (A ⟨f, hf⟩) := by
  have hcl : (A.domRestrict P).IsClosable :=
    hA.isClosable.leIsClosable LinearPMap.domRestrict_le
  have hg : (A.domRestrict P).graph.topologicalClosure = A.graph := by
    rw [hcl.graph_closure_eq_closure_graph, hcore.closure_eq]
  exact lemma_9_2_graph A hA T P hcore.le_domain hg hTP hcomm

#print axioms GegenbauerFock.Section8Section9.theorem_8_1_hs_tail
#print axioms GegenbauerFock.Section8Section9.theorem_8_1_tail_le
#print axioms GegenbauerFock.Section8Section9.theorem_8_1_opNorm
#print axioms GegenbauerFock.Section8Section9.theorem_8_1_rank
#print axioms GegenbauerFock.Section8Section9.theorem_8_1_approximation_number
#print axioms GegenbauerFock.Section8Section9.theorem_8_1_schatten
#print axioms GegenbauerFock.Section8Section9.proj_e
#print axioms GegenbauerFock.Section8Section9.proposition_8_2
#print axioms GegenbauerFock.Section8Section9.range_not_closed_of_compact_injective
#print axioms GegenbauerFock.Section8Section9.S_eq_gram
#print axioms GegenbauerFock.Section8Section9.proposition_9_1
#print axioms GegenbauerFock.Section8Section9.lemma_9_2_graph
#print axioms GegenbauerFock.Section8Section9.lemma_9_2

end GegenbauerFock.Section8Section9
