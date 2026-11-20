import UniformLanczos.Lemma58Uniform
import UniformLanczos.Arcsine
import UniformLanczos.Diagonal
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Manuscript 12, Theorem 5.9: the proportional-regime Jacobi–Lanczos limit

Source: frozen `12.tex`, the paragraph *Levin and Lubinsky* of Subsection 5.1 with (101)–(106),
Lemma 5.8 (`lem:ul-classQ`, (135)–(140)) and Theorem 5.9 (`thm:ul-main`, (141)) with its proof
(scaling (142), sequences, uniformity).

The theorem of Levin and Lubinsky is not proved here.  It enters as the single explicit
hypothesis `LL_13_4`, the part of Theorem 13.4 of D. S. Lubinsky and E. Levin, *Bounds and
Asymptotics for Orthogonal Polynomials for Varying Weights* (2018), p. 124, that the manuscript
uses, eq. (105): if `{Q_n} ∈ 𝒬` and `ε ∈ (0, 1/3)`, then `A_{n,m} = 1/2 + O(n^{-τ₁})` uniformly for
`|m - n| ≤ n^{1/3-ε}`.  Everything else is proved.

* `ClassQ r I Q`: Definition 1.1 of that monograph (p. 6) for weights `e^{-2nQ_n}` on open
  intervals `I_n ⊇ [-r, r]`, `r > 1`, with conditions (i)–(iv) as stated there and condition (v)
  in the equivalent form (101)–(102) of Remark (b) after the definition (Lebesgue integrals over
  `(-1, 1)`).
* `LLA I Q n m`: the recurrence coefficient `A_{n,m} = γ_{n,m}/γ_{n,m+1}` of (103)–(104), written
  through the Hankel determinants `D_k` of the moments of `e^{-2nQ_n}` on `I_n`:
  `A_{n,m}² = h_{m+1}/h_m = D_{m+2} D_m / D_{m+1}²`.  `recSq_eq_norm_ratio` proves that this
  quotient is `‖P_{m+1}‖²/‖P_m‖²` for every monic orthogonal family `P` of a positive moment
  functional, i.e. `γ_{n,m}²/γ_{n,m+1}²` for the orthonormal polynomials `p_{n,m} = P_m/‖P_m‖`.
* `betaM M j = β_j^{[M]} = h_j/h_{j-1}` for the law of `S_M`, whose density is the cardinal
  B-spline `w_M` of `Bridge.Saddle`, through the same Hankel quotient of its moments.
* `scaling_142`: (142), `β_j^{[M]} = (Mξ)² A_{j,j-1}²` for the weight `e^{-2jQ_{j,M}}` of (135).
* `classQ_seq`: the sequences of the proof (`Q_n = Q_{n,ν(n)}`, and `Q_n(x) = x²` on `ℝ` otherwise)
  belong to `𝒬`, from `Lemma58.lemma_5_8_uniform` and `Lemma58.lemma_5_8_i`.
* `seq_limit`: `ℰ_{n,ν(n)} → 0` along every admissible `ν`, with Lemma 5.7(b)
  (`Joined.endpoint_actual`).
* `theorem_5_9`, `theorem_5_9_sup`: Theorem 5.9, in the `ε`–`L` form and in the form (141) with
  the supremum, for every compact `𝒦 ⊂ (0, ∞)`, assuming `LL_13_4` only.
-/

open Set Filter Topology MeasureTheory Real
open EulerianBridge.Saddle
open UniformLanczos.Lemma56 UniformLanczos.Lemma58

namespace UniformLanczos.Theorem59

/-! ### Open intervals with possibly infinite endpoints -/

/-- An open interval `(c, d)` with `-∞ ≤ c < d ≤ ∞`; `none` stands for an infinite endpoint. -/
structure OpenInt where
  lo : Option ℝ
  hi : Option ℝ

namespace OpenInt

/-- `c < x`, and no condition when `c = -∞`. -/
def loOK : Option ℝ → ℝ → Prop
  | none, _ => True
  | some c, x => c < x

/-- `x < d`, and no condition when `d = ∞`. -/
def hiOK : Option ℝ → ℝ → Prop
  | none, _ => True
  | some d, x => x < d

/-- The points of the interval. -/
def set (I : OpenInt) : Set ℝ := {x | loOK I.lo x ∧ hiOK I.hi x}

/-- Approach to the left endpoint: `c+`, or `-∞`. -/
noncomputable def loFilter (I : OpenInt) : Filter ℝ :=
  match I.lo with
  | none => atBot
  | some c => 𝓝[>] c

/-- Approach to the right endpoint: `d-`, or `∞`. -/
noncomputable def hiFilter (I : OpenInt) : Filter ℝ :=
  match I.hi with
  | none => atTop
  | some d => 𝓝[<] d

/-- The bounded interval `(c, d)`. -/
def finite (c d : ℝ) : OpenInt := ⟨some c, some d⟩

/-- The whole line `(-∞, ∞)`. -/
def line : OpenInt := ⟨none, none⟩

theorem set_finite (c d : ℝ) : (finite c d).set = Ioo c d := by
  ext x
  exact Iff.rfl

theorem mem_line (x : ℝ) : x ∈ line.set := by
  show loOK none x ∧ hiOK none x
  exact ⟨trivial, trivial⟩

theorem loFilter_finite (c d : ℝ) : (finite c d).loFilter = 𝓝[>] c := rfl

theorem hiFilter_finite (c d : ℝ) : (finite c d).hiFilter = 𝓝[<] d := rfl

theorem loFilter_line : line.loFilter = atBot := rfl

theorem hiFilter_line : line.hiFilter = atTop := rfl

end OpenInt

/-! ### Moments, Hankel determinants and recurrence coefficients -/

/-- The moments `∫_I x^k W(x) dx` of a weight `W` on `I`. -/
noncomputable def moment (I : OpenInt) (W : ℝ → ℝ) (k : ℕ) : ℝ := ∫ x in I.set, x ^ k * W x

/-- The Hankel matrix `(μ_{i+j})_{0 ≤ i,j < n}`. -/
noncomputable def hankelMat (μ : ℕ → ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ := fun i j => μ (i.val + j.val)

/-- The Hankel determinant `D_n`. -/
noncomputable def hankel (μ : ℕ → ℝ) (n : ℕ) : ℝ := (hankelMat μ n).det

/-- `h_{m+1}/h_m = D_{m+2} D_m / D_{m+1}²`, the squared recurrence coefficient. -/
noncomputable def recSq (μ : ℕ → ℝ) (m : ℕ) : ℝ :=
  hankel μ (m + 1 + 1) * hankel μ m / hankel μ (m + 1) ^ 2

/-- The weight `e^{-2nQ_n}`. -/
noncomputable def weight (Q : ℕ → ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ := Real.exp (-2 * (n:ℝ) * Q n x)

/-- `A_{n,m}` of (103)–(104) for the weights `e^{-2nQ_n}` on `I_n`. -/
noncomputable def LLA (I : ℕ → OpenInt) (Q : ℕ → ℝ → ℝ) (n m : ℕ) : ℝ :=
  Real.sqrt (recSq (moment (I n) (weight Q n)) m)

/-! ### The Hankel quotient is the ratio of squared norms of monic orthogonal polynomials

The Gram-determinant lemmas below are those of `lean/FixedDegreeLanczos/lean/V033GramBasis.lean`
(same toolchain and Mathlib revision), restated here because that project is a separate Lake
package. -/

section Gram

open Polynomial

variable {R : Type*} [CommRing R] [Algebra ℝ R]

noncomputable def gramHankel (L : ℝ[X] →ₗ[ℝ] R) (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  fun i j => L (Polynomial.X ^ (i.val + j.val))

noncomputable def gramFamily (L : ℝ[X] →ₗ[ℝ] R) {n : ℕ} (p : Fin n → ℝ[X]) :
    Matrix (Fin n) (Fin n) R :=
  fun i j => L (p i * p j)

noncomputable def gramCoefficients {n : ℕ} (p : Fin n → ℝ[X]) : Matrix (Fin n) (Fin n) R :=
  fun i j => algebraMap ℝ R ((p j).coeff i.val)

theorem gram_polynomial_sum {n : ℕ} (p : ℝ[X]) (hp : p.natDegree < n) :
    p = ∑ i : Fin n, Polynomial.C (p.coeff i.val) * Polynomial.X ^ i.val := by
  rw [Fin.sum_univ_eq_sum_range (fun i => Polynomial.C (p.coeff i) * Polynomial.X ^ i) n]
  exact p.as_sum_range_C_mul_X_pow' hp

theorem gram_pairing_expansion (L : ℝ[X] →ₗ[ℝ] R) {n : ℕ} (p q : ℝ[X])
    (hp : p.natDegree < n) (hq : q.natDegree < n) :
    L (p * q) = ∑ i : Fin n, ∑ j : Fin n,
      algebraMap ℝ R (p.coeff i.val) * L (Polynomial.X ^ (i.val + j.val)) *
        algebraMap ℝ R (q.coeff j.val) := by
  conv_lhs => rw [gram_polynomial_sum p hp, gram_polynomial_sum q hq]
  simp only [Finset.sum_mul, Finset.mul_sum, map_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [show Polynomial.C (p.coeff i.val) * Polynomial.X ^ i.val *
        (Polynomial.C (q.coeff j.val) * Polynomial.X ^ j.val) =
      Polynomial.C (p.coeff i.val * q.coeff j.val) * Polynomial.X ^ (i.val + j.val) by
        rw [map_mul, pow_add]; ring,
    ← Polynomial.smul_eq_C_mul, map_smul]
  simp only [Algebra.smul_def, map_mul]
  ring

theorem gram_change_basis (L : ℝ[X] →ₗ[ℝ] R) {n : ℕ} (p : Fin n → ℝ[X])
    (hp : ∀ i, (p i).natDegree < n) :
    gramFamily L p = (gramCoefficients p)ᵀ * gramHankel L n * gramCoefficients p := by
  ext i j
  rw [gramFamily, gram_pairing_expansion L _ _ (hp i) (hp j)]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, gramCoefficients, gramHankel,
    Finset.sum_mul]
  rw [Finset.sum_comm]

theorem gram_coefficients_det_one {n : ℕ} (p : Fin n → ℝ[X])
    (hd : ∀ i, (p i).natDegree = i.val) (hm : ∀ i, (p i).Monic) :
    (gramCoefficients (R := R) p).det = 1 := by
  have ht := Matrix.det_matrixOfPolynomials p hd hm
  have h := congrArg (algebraMap ℝ R) ht
  rw [RingHom.map_det, map_one] at h
  exact h

theorem gram_monic_det (L : ℝ[X] →ₗ[ℝ] R) {n : ℕ} (p : Fin n → ℝ[X])
    (hd : ∀ i, (p i).natDegree = i.val) (hm : ∀ i, (p i).Monic) :
    (gramFamily L p).det = (gramHankel L n).det := by
  rw [gram_change_basis L p (fun i => by rw [hd]; exact i.isLt), Matrix.det_mul,
    Matrix.det_mul, Matrix.det_transpose, gram_coefficients_det_one p hd hm, one_mul, mul_one]

theorem gram_orthogonal_det (L : ℝ[X] →ₗ[ℝ] R) {n : ℕ} (p : Fin n → ℝ[X])
    (hd : ∀ i, (p i).natDegree = i.val) (hm : ∀ i, (p i).Monic)
    (ho : ∀ i j, i ≠ j → L (p i * p j) = 0) :
    (gramHankel L n).det = ∏ i : Fin n, L (p i * p i) := by
  rw [← gram_monic_det L p hd hm]
  have he : gramFamily L p = Matrix.diagonal (fun i => L (p i * p i)) := by
    ext i j
    by_cases hij : i = j
    · subst j; simp [gramFamily]
    · simp [gramFamily, Matrix.diagonal_apply, hij, ho i j hij]
  rw [he, Matrix.det_diagonal]

end Gram

open Polynomial in
/-- For a monic orthogonal family `P` (`deg P_i = i`) of a moment functional `L`, the Hankel
determinant of the moments `L(X^k)` is `D_n = ∏_{i<n} ‖P_i‖²`. -/
theorem hankel_eq_prod_norms (L : ℝ[X] →ₗ[ℝ] ℝ) (P : ℕ → ℝ[X])
    (hd : ∀ i, (P i).natDegree = i) (hm : ∀ i, (P i).Monic)
    (ho : ∀ i j, i ≠ j → L (P i * P j) = 0) (n : ℕ) :
    hankel (fun k => L (Polynomial.X ^ k)) n = ∏ i ∈ Finset.range n, L (P i * P i) := by
  have h := gram_orthogonal_det L (fun i : Fin n => P i.val) (fun i => hd i.val) (fun i => hm i.val)
    (fun i j hij => ho i.val j.val (fun h => hij (Fin.ext h)))
  have h2 : (∏ i : Fin n, L (P i.val * P i.val)) = ∏ i ∈ Finset.range n, L (P i * P i) :=
    Fin.prod_univ_eq_prod_range (fun i => L (P i * P i)) n
  rw [← h2]
  exact h

open Polynomial in
/-- `A_{n,m}² = γ_{n,m}²/γ_{n,m+1}² = ‖P_{m+1}‖²/‖P_m‖²`: the Hankel quotient `recSq` is the
ratio of the squared norms of consecutive monic orthogonal polynomials. -/
theorem recSq_eq_norm_ratio (L : ℝ[X] →ₗ[ℝ] ℝ) (P : ℕ → ℝ[X])
    (hd : ∀ i, (P i).natDegree = i) (hm : ∀ i, (P i).Monic)
    (ho : ∀ i j, i ≠ j → L (P i * P j) = 0) (hpos : ∀ i, 0 < L (P i * P i)) (m : ℕ) :
    recSq (fun k => L (Polynomial.X ^ k)) m = L (P (m + 1) * P (m + 1)) / L (P m * P m) := by
  unfold recSq
  rw [hankel_eq_prod_norms L P hd hm ho, hankel_eq_prod_norms L P hd hm ho,
    hankel_eq_prod_norms L P hd hm ho]
  simp only [Finset.prod_range_succ]
  have hp : 0 < ∏ i ∈ Finset.range m, L (P i * P i) := Finset.prod_pos fun i _ => hpos i
  have h0 := hpos m
  have h1 := hpos (m + 1)
  first | (field_simp; ring) | field_simp

/-! ### Scaling of Hankel quotients -/

theorem hankel_scale (u : ℝ) (μ : ℕ → ℝ) (n : ℕ) :
    hankel (fun k => u ^ k * μ k) n = (∏ i ∈ Finset.range n, u ^ i) ^ 2 * hankel μ n := by
  have h : hankelMat (fun k => u ^ k * μ k) n =
      Matrix.diagonal (fun i : Fin n => u ^ i.val) * hankelMat μ n *
        Matrix.diagonal (fun i : Fin n => u ^ i.val) := by
    ext i j
    simp only [hankelMat, Matrix.mul_diagonal, Matrix.diagonal_mul, pow_add]
    ring
  have hp : (∏ i : Fin n, u ^ i.val) = ∏ i ∈ Finset.range n, u ^ i :=
    Fin.prod_univ_eq_prod_range (fun i => u ^ i) n
  unfold hankel
  rw [h, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, hp]
  ring

theorem prodPow_succ (u : ℝ) (n : ℕ) :
    ∏ i ∈ Finset.range (n + 1), u ^ i = (∏ i ∈ Finset.range n, u ^ i) * u ^ n :=
  Finset.prod_range_succ _ _

/-- Moments `μ_k ↦ u^k μ_k` (the variable multiplied by `u`) multiply `recSq` by `u²`. -/
theorem recSq_scale {u : ℝ} (hu : u ≠ 0) (μ : ℕ → ℝ) (m : ℕ) :
    recSq (fun k => u ^ k * μ k) m = u ^ 2 * recSq μ m := by
  unfold recSq
  rw [hankel_scale, hankel_scale, hankel_scale, prodPow_succ u (m + 1), prodPow_succ u m]
  have hp : (∏ i ∈ Finset.range m, u ^ i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ hu
  by_cases hD : hankel μ (m + 1) = 0
  · simp [hD]
  · first | (field_simp; ring) | field_simp

/-! ### Definition 1.1 of Levin and Lubinsky and the hypothesis (105) -/

/-- Definition 1.1 of Levin–Lubinsky (2018), p. 6: `{Q_n} ∈ 𝒬` for the weights `e^{-2nQ_n}` on
`I_n ⊇ [-r, r]`, `r > 1`; condition (v) in the form (101)–(102) of Remark (b). -/
structure ClassQ (r : ℝ) (I : ℕ → OpenInt) (Q : ℕ → ℝ → ℝ) : Prop where
  one_lt : 1 < r
  sub : ∀ n, 1 ≤ n → Icc (-r) r ⊆ (I n).set
  cond_i : ∀ n, 1 ≤ n →
    Tendsto (fun x => Q n x / Real.log (2 + |x|)) (I n).loFilter atTop ∧
      Tendsto (fun x => Q n x / Real.log (2 + |x|)) (I n).hiFilter atTop
  cond_ii : ∀ n, 1 ≤ n → (∀ x ∈ (I n).set, DifferentiableAt ℝ (Q n) x) ∧
    StrictMonoOn (deriv (Q n)) (I n).set ∧ ContinuousOn (deriv (Q n)) (I n).set
  cond_iii : ∃ γ₀ C : ℝ, 0 < γ₀ ∧ γ₀ < 1 ∧ 0 < C ∧ ∀ n, 1 ≤ n →
    ∀ x ∈ Icc (-r) r, ∀ y ∈ Icc (-r) r, |deriv (Q n) x - deriv (Q n) y| ≤ C * |x - y| ^ γ₀
  cond_iv : ∃ γ₁ C₁ : ℝ, ∃ I₀ : Set ℝ, 1 / 2 < γ₁ ∧ γ₁ < 1 ∧ 0 < C₁ ∧ IsOpen I₀ ∧
    (1:ℝ) ∈ I₀ ∧ (-1:ℝ) ∈ I₀ ∧ ∀ n, 1 ≤ n →
      ∀ x ∈ (I n).set ∩ I₀, ∀ y ∈ (I n).set ∩ I₀,
        |deriv (Q n) x - deriv (Q n) y| ≤ C₁ * |x - y| ^ γ₁
  cond_v : ∀ n, 1 ≤ n →
    (1 / π) * ∫ x in Ioo (-1:ℝ) 1, x * deriv (Q n) x / √(1 - x ^ 2) = 1 ∧
      (1 / π) * ∫ x in Ioo (-1:ℝ) 1, deriv (Q n) x / √(1 - x ^ 2) = 0

/-- Theorem 13.4 of Levin–Lubinsky (2018), p. 124, eq. (105): for `{Q_n} ∈ 𝒬` and
`ε ∈ (0, 1/3)` there is `τ₁ > 0` with `A_{n,m} = 1/2 + O(n^{-τ₁})` uniformly for
`|m - n| ≤ n^{1/3-ε}`.  This is the only hypothesis of Theorem 5.9 below. -/
def LL_13_4 : Prop :=
  ∀ (r : ℝ) (I : ℕ → OpenInt) (Q : ℕ → ℝ → ℝ), ClassQ r I Q →
    ∀ ε : ℝ, 0 < ε → ε < 1 / 3 → ∃ τ₁ : ℝ, 0 < τ₁ ∧ ∃ C : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ m : ℕ, |(m:ℝ) - n| ≤ (n:ℝ) ^ (1 / 3 - ε) → |LLA I Q n m - 1 / 2| ≤ C / (n:ℝ) ^ τ₁

/-- (105) with `m = n - 1`: `A_{n,n-1} → 1/2`. -/
theorem LLA_tendsto (hLL : LL_13_4) {r : ℝ} {I : ℕ → OpenInt} {Q : ℕ → ℝ → ℝ}
    (hQ : ClassQ r I Q) : Tendsto (fun n => LLA I Q n (n - 1)) atTop (𝓝 (1 / 2)) := by
  obtain ⟨τ, hτ, C, n₀, hb⟩ := hLL r I Q hQ (1 / 6) (by norm_num) (by norm_num)
  have hlim : Tendsto (fun n : ℕ => C / (n:ℝ) ^ τ) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_rpow_atTop hτ).comp tendsto_natCast_atTop_atTop)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun n => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop (max n₀ 1)] with n hn
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  rw [Real.norm_eq_abs]
  apply hb n (le_trans (le_max_left _ _) hn) (n - 1)
  have e : ((n - 1 : ℕ) : ℝ) - n = -1 := by
    rw [Nat.cast_sub hn1, Nat.cast_one]
    ring
  rw [e, abs_neg, abs_one]
  exact Real.one_le_rpow (by exact_mod_cast hn1) (by norm_num)

/-! ### The weights of Lemma 5.8 and the scaling (142) -/

/-- The moments `∫ s^k w_M(s) ds` of `S_M`. -/
noncomputable def wMoment (M : ℕ) (k : ℕ) : ℝ := ∫ s, s ^ k * w M s

/-- `β_j^{[M]} = h_j/h_{j-1} = D_{j+1} D_{j-1}/D_j²` for the law of `S_M` (density `w_M`). -/
noncomputable def betaM (M j : ℕ) : ℝ := recSq (wMoment M) (j - 1)

/-- (135): `e^{-2jQ_{j,M}(y)} = ξ g_M(ξ y)` on `(-1/(2ξ), 1/(2ξ))`. -/
theorem weight_QjM {M j : ℕ} (hM : 2 ≤ M) (hj : 1 ≤ j) {a y : ℝ} (ha : 0 < a)
    (hy : y ∈ Ioo (-(1 / (2 * a))) (1 / (2 * a))) :
    Real.exp (-2 * (j:ℝ) * QjM M j a y) = a * gM M (a * y) := by
  have hMpos : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hjpos : (0:ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hM0 : (M:ℝ) ≠ 0 := hMpos.ne'
  have hj0 : (j:ℝ) ≠ 0 := hjpos.ne'
  have hg : 0 < gM M (a * y) := by
    have hw := w_scaled_pos hM (mem_half_of_mem ha hy)
    show 0 < (M:ℝ) * w M ((M:ℝ) * (a * y))
    exact mul_pos hMpos hw
  have e : -2 * (j:ℝ) * QjM M j a y = Real.log (gM M (a * y)) + Real.log a := by
    unfold QjM φM
    first | (field_simp; ring) | field_simp
  rw [e, Real.exp_add, Real.exp_log hg, Real.exp_log ha]
  ring

/-- The moments of `e^{-2jQ_{j,M}}` on `(-1/(2ξ), 1/(2ξ))` are `(Mξ)^{-k}` times those of `S_M`. -/
theorem moment_QjM {M j : ℕ} (hM : 2 ≤ M) (hj : 1 ≤ j) {a : ℝ} (ha : 0 < a) (k : ℕ) :
    moment (OpenInt.finite (-(1 / (2 * a))) (1 / (2 * a)))
        (fun x => Real.exp (-2 * (j:ℝ) * QjM M j a x)) k =
      ((M:ℝ) * a)⁻¹ ^ k * wMoment M k := by
  have hMpos : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hM0 : (M:ℝ) ≠ 0 := hMpos.ne'
  have ha0 : a ≠ 0 := ha.ne'
  have hc : 0 < (M:ℝ) * a := mul_pos hMpos ha
  unfold moment
  rw [OpenInt.set_finite]
  have h1 : ∫ x in Ioo (-(1 / (2 * a))) (1 / (2 * a)), x ^ k * Real.exp (-2 * (j:ℝ) * QjM M j a x) =
      ∫ x in Ioo (-(1 / (2 * a))) (1 / (2 * a)), x ^ k * (a * gM M (a * x)) := by
    refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    simp only [weight_QjM hM hj ha hx]
  have hout : ∀ x, x ∉ Icc (-(1 / (2 * a))) (1 / (2 * a)) → x ^ k * (a * gM M (a * x)) = 0 := by
    intro x hx
    have hx' : 1 / (2 * a) < |x| := by
      rw [mem_Icc, not_and_or, not_le, not_le] at hx
      rcases hx with h | h
      · rw [lt_abs]; right; linarith
      · rw [lt_abs]; left; exact h
    have hax : 1 / 2 < a * |x| := by
      have := mul_lt_mul_of_pos_left hx' ha
      rwa [show a * (1 / (2 * a)) = 1 / 2 by field_simp] at this
    have hbig : (M:ℝ) / 2 < |(M:ℝ) * (a * x)| := by
      rw [abs_mul, abs_mul, abs_of_pos hMpos, abs_of_pos ha]
      nlinarith
    have hw : w M ((M:ℝ) * (a * x)) = 0 := w_support M (by omega) _ hbig
    show x ^ k * (a * ((M:ℝ) * w M ((M:ℝ) * (a * x)))) = 0
    rw [hw]
    ring
  have hpt : ∀ x : ℝ, x ^ k * (a * gM M (a * x)) =
      (((M:ℝ) * a)⁻¹ ^ k * ((M:ℝ) * a)) * ((((M:ℝ) * a) * x) ^ k * w M (((M:ℝ) * a) * x)) := by
    intro x
    have harg : (M:ℝ) * (a * x) = (M:ℝ) * a * x := (mul_assoc _ _ _).symm
    show x ^ k * (a * ((M:ℝ) * w M ((M:ℝ) * (a * x)))) = _
    rw [harg]
    first | (field_simp; ring) | field_simp
  have hsub := MeasureTheory.Measure.integral_comp_mul_left (fun s : ℝ => s ^ k * w M s)
    ((M:ℝ) * a)
  simp only at hsub
  rw [h1, ← integral_Icc_eq_integral_Ioo, setIntegral_eq_integral_of_forall_compl_eq_zero hout]
  simp_rw [hpt]
  rw [MeasureTheory.integral_const_mul, hsub, smul_eq_mul, abs_of_pos (inv_pos.mpr hc)]
  unfold wMoment
  rw [mul_assoc, ← mul_assoc ((M:ℝ) * a), mul_inv_cancel₀ hc.ne', one_mul]

/-- (142): `β_j^{[M]} = (Mξ)² A_{j,j-1}²`, with `A_{j,j-1}² = recSq` for the weight
`e^{-2jQ_{j,M}}` of (135) on `(-1/(2ξ), 1/(2ξ))`. -/
theorem scaling_142 {M j : ℕ} (hM : 2 ≤ M) (hj : 1 ≤ j) {a : ℝ} (ha : 0 < a) :
    betaM M j = ((M:ℝ) * a) ^ 2 *
      recSq (moment (OpenInt.finite (-(1 / (2 * a))) (1 / (2 * a)))
        (fun x => Real.exp (-2 * (j:ℝ) * QjM M j a x))) (j - 1) := by
  have hMpos : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hc : 0 < (M:ℝ) * a := mul_pos hMpos ha
  have h : moment (OpenInt.finite (-(1 / (2 * a))) (1 / (2 * a)))
      (fun x => Real.exp (-2 * (j:ℝ) * QjM M j a x)) =
        fun k => ((M:ℝ) * a)⁻¹ ^ k * wMoment M k := funext (moment_QjM hM hj ha)
  rw [h, recSq_scale (inv_ne_zero hc.ne'), ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hc.ne',
    one_pow, one_mul]
  rfl

/-! ### The filler weight `x²` on `ℝ` -/

theorem sq_div_log_ge {x : ℝ} (hx : 1 ≤ |x|) : |x| / 2 ≤ x ^ 2 / Real.log (2 + |x|) := by
  have hl : 0 < Real.log (2 + |x|) := Real.log_pos (by linarith [abs_nonneg x])
  have hl2 : Real.log (2 + |x|) ≤ 1 + |x| := by
    have := Real.log_le_sub_one_of_pos (show 0 < 2 + |x| by linarith [abs_nonneg x])
    linarith
  rw [le_div_iff₀ hl, ← sq_abs x]
  nlinarith [mul_le_mul_of_nonneg_left hl2 (show 0 ≤ |x| / 2 by positivity),
    mul_nonneg (abs_nonneg x) (sub_nonneg.mpr hx)]

theorem sq_tendsto_atTop : Tendsto (fun x : ℝ => x ^ 2 / Real.log (2 + |x|)) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  rw [eventually_atTop]
  refine ⟨max 1 (2 * b), fun x hx => ?_⟩
  have hx1 : 1 ≤ x := le_trans (le_max_left _ _) hx
  have hxabs : |x| = x := abs_of_nonneg (by linarith)
  have h := sq_div_log_ge (x := x) (by rw [hxabs]; exact hx1)
  have hb : b ≤ |x| / 2 := by
    rw [hxabs]
    linarith [le_max_right 1 (2 * b)]
  exact le_trans hb h

theorem sq_tendsto_atBot : Tendsto (fun x : ℝ => x ^ 2 / Real.log (2 + |x|)) atBot atTop := by
  rw [tendsto_atTop]
  intro b
  rw [eventually_atBot]
  refine ⟨min (-1) (-(2 * b)), fun x hx => ?_⟩
  have hx1 : x ≤ -1 := le_trans hx (min_le_left _ _)
  have hxabs : |x| = -x := abs_of_neg (by linarith)
  have h := sq_div_log_ge (x := x) (by rw [hxabs]; linarith)
  have hb : b ≤ |x| / 2 := by
    rw [hxabs]
    linarith [min_le_right (-1) (-(2 * b))]
  exact le_trans hb h

theorem hasDerivAt_sq' (x : ℝ) : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x := by
  simpa using hasDerivAt_pow 2 x

theorem deriv_sq' : deriv (fun x : ℝ => x ^ 2) = fun x => 2 * x :=
  funext fun x => (hasDerivAt_sq' x).deriv

theorem holder_two_mul {r α : ℝ} (hα1 : α ≤ 1) :
    ∀ x ∈ Icc (-r) r, ∀ y ∈ Icc (-r) r,
      |2 * x - 2 * y| ≤ 2 * (2 * r) ^ (1 - α) * |x - y| ^ α :=
  UniformLanczos.holder_of_lipschitz (f := fun x => 2 * x) (by norm_num) hα1
    (fun x _ y _ => le_of_eq (show |2 * x - 2 * y| = 2 * |x - y| by
      rw [← mul_sub, abs_mul, abs_two]))

theorem integral_cos_two_cos : ∫ θ in (0:ℝ)..π, Real.cos θ * (2 * Real.cos θ) = π := by
  have e : (fun θ => Real.cos θ * (2 * Real.cos θ)) = fun θ => 2 * Real.cos θ ^ 2 := by
    funext θ
    ring
  rw [e, intervalIntegral.integral_const_mul, integral_cos_sq, Real.sin_pi, Real.sin_zero]
  ring

theorem integral_two_cos : ∫ θ in (0:ℝ)..π, 2 * Real.cos θ = 0 := by
  rw [intervalIntegral.integral_const_mul, integral_cos, Real.sin_pi, Real.sin_zero]
  ring

/-! ### The sequences of the proof belong to `𝒬` -/

/-- The conclusions of `Lemma58.lemma_5_8_uniform` for one pair `(j, M)` and root `a`. -/
def Spec58 (b r L : ℝ) (M j : ℕ) (a : ℝ) : Prop :=
  Hint (fun y => y * deriv (φM M) y) a = (j:ℝ) / M ∧
    (∀ a' ∈ Icc 0 b, Hint (fun y => y * deriv (φM M) y) a' = (j:ℝ) / M → a' = a) ∧
    Icc (-r) r ⊆ Ioo (-(1 / (2 * a))) (1 / (2 * a)) ∧
    StrictMonoOn (QjM' M j a) (Ioo (-(1 / (2 * a))) (1 / (2 * a))) ∧
    ContinuousOn (QjM' M j a) (Ioo (-(1 / (2 * a))) (1 / (2 * a))) ∧
    (∀ x ∈ Icc (-r) r, ∀ y ∈ Icc (-r) r,
      |QjM' M j a x - QjM' M j a y| ≤ L * |x - y|) ∧
    (∀ x ∈ Icc (-r) r, ∀ y ∈ Icc (-r) r,
      |QjM' M j a x - QjM' M j a y| ≤ L * (2 * r) ^ (1 - (1/4:ℝ)) * |x - y| ^ (1/4:ℝ)) ∧
    (∀ x ∈ Icc (-r) r, ∀ y ∈ Icc (-r) r,
      |QjM' M j a x - QjM' M j a y| ≤ L * (2 * r) ^ (1 - (3/4:ℝ)) * |x - y| ^ (3/4:ℝ)) ∧
    (1 / Real.pi) * ∫ θ in (0:ℝ)..Real.pi, Real.cos θ * QjM' M j a (Real.cos θ) = 1 ∧
    ∫ θ in (0:ℝ)..Real.pi, QjM' M j a (Real.cos θ) = 0

/-- The intervals of the proof: `(-1/(2ξ_n), 1/(2ξ_n))` where `G n`, the line otherwise. -/
noncomputable def seqI (G : ℕ → Prop) [DecidablePred G] (a : ℕ → ℝ) (n : ℕ) : OpenInt :=
  if G n then OpenInt.finite (-(1 / (2 * a n))) (1 / (2 * a n)) else OpenInt.line

/-- The fields of the proof: `Q_{n,ν(n)}` where `G n`, `x²` otherwise. -/
noncomputable def seqQ (G : ℕ → Prop) [DecidablePred G] (ν : ℕ → ℕ) (a : ℕ → ℝ) (n : ℕ) :
    ℝ → ℝ :=
  if G n then QjM (ν n) n (a n) else fun x => x ^ 2

theorem classQ_seq (G : ℕ → Prop) [DecidablePred G] (ν : ℕ → ℕ) (a : ℕ → ℝ) {b r L : ℝ}
    (hr : 1 < r) (hL : 0 ≤ L)
    (hG : ∀ n, G n → 3 ≤ ν n ∧ 1 ≤ n ∧ 0 < a n ∧ Spec58 b r L (ν n) n (a n)) :
    ClassQ r (seqI G a) (seqQ G ν a) := by
  have hr0 : 0 < 2 * r := by linarith
  have hpow : ∀ γ : ℝ, 0 < (2 * r) ^ γ := fun γ => Real.rpow_pos_of_pos hr0 γ
  -- the two cases of a single index
  have hI_pos : ∀ n, G n → seqI G a n = OpenInt.finite (-(1 / (2 * a n))) (1 / (2 * a n)) :=
    fun n h => if_pos h
  have hI_neg : ∀ n, ¬ G n → seqI G a n = OpenInt.line := fun n h => if_neg h
  have hQ_pos : ∀ n, G n → seqQ G ν a n = QjM (ν n) n (a n) := fun n h => if_pos h
  have hQ_neg : ∀ n, ¬ G n → seqQ G ν a n = fun x => x ^ 2 := fun n h => if_neg h
  -- the derivative of `Q_{n,ν(n)}` on its interval
  have hderiv : ∀ n, G n → ∀ y ∈ Ioo (-(1 / (2 * a n))) (1 / (2 * a n)),
      deriv (QjM (ν n) n (a n)) y = QjM' (ν n) n (a n) y := fun n h y hy =>
    (hasDerivAt_QjM n (hG n h).1 (hG n h).2.2.1 hy).deriv
  refine ⟨hr, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `[-r, r] ⊂ I_n`
    intro n _
    by_cases h : G n
    · rw [hI_pos n h, OpenInt.set_finite]
      exact (hG n h).2.2.2.2.2.1
    · rw [hI_neg n h]
      exact fun x _ => OpenInt.mem_line x
  · -- (i)
    intro n _
    by_cases h : G n
    · obtain ⟨h3, hn1, ha, -⟩ := hG n h
      have hi := lemma_5_8_i (M := ν n) (j := n) (by omega) hn1 ha
      rw [hI_pos n h, hQ_pos n h, OpenInt.loFilter_finite, OpenInt.hiFilter_finite]
      exact ⟨hi.2, hi.1⟩
    · rw [hI_neg n h, hQ_neg n h, OpenInt.loFilter_line, OpenInt.hiFilter_line]
      exact ⟨sq_tendsto_atBot, sq_tendsto_atTop⟩
  · -- (ii)
    intro n _
    by_cases h : G n
    · obtain ⟨h3, hn1, ha, hs⟩ := hG n h
      rw [hI_pos n h, hQ_pos n h, OpenInt.set_finite]
      refine ⟨fun y hy => (hasDerivAt_QjM n h3 ha hy).differentiableAt, ?_, ?_⟩
      · intro x hx y hy hxy
        rw [hderiv n h x hx, hderiv n h y hy]
        exact hs.2.2.2.1 hx hy hxy
      · exact hs.2.2.2.2.1.congr fun y hy => hderiv n h y hy
    · rw [hI_neg n h, hQ_neg n h, deriv_sq']
      refine ⟨fun y _ => (hasDerivAt_sq' y).differentiableAt, ?_, ?_⟩
      · intro x _ y _ hxy
        show 2 * x < 2 * y
        linarith
      · exact (continuous_const.mul continuous_id).continuousOn
  · -- (iii), `γ₀ = 1/4`
    refine ⟨1 / 4, L * (2 * r) ^ (1 - (1/4:ℝ)) + 2 * (2 * r) ^ (1 - (1/4:ℝ)),
      by norm_num, by norm_num,
      by have h1 := hpow (1 - (1/4:ℝ)); linarith [mul_nonneg hL h1.le], ?_⟩
    intro n _ x hx y hy
    have hxy : 0 ≤ |x - y| ^ (1/4:ℝ) := Real.rpow_nonneg (abs_nonneg _) _
    by_cases h : G n
    · obtain ⟨h3, hn1, ha, hs⟩ := hG n h
      have hsub := hs.2.2.1
      rw [hQ_pos n h, hderiv n h x (hsub hx), hderiv n h y (hsub hy)]
      have hb := hs.2.2.2.2.2.2.1 x hx y hy
      have : 0 ≤ 2 * (2 * r) ^ (1 - (1/4:ℝ)) * |x - y| ^ (1/4:ℝ) :=
        mul_nonneg (mul_nonneg (by norm_num) (hpow _).le) hxy
      nlinarith
    · rw [hQ_neg n h, deriv_sq']
      have hb := holder_two_mul (r := r) (α := 1/4) (by norm_num) x hx y hy
      have : 0 ≤ L * (2 * r) ^ (1 - (1/4:ℝ)) * |x - y| ^ (1/4:ℝ) :=
        mul_nonneg (mul_nonneg hL (hpow _).le) hxy
      show |2 * x - 2 * y| ≤ _
      nlinarith
  · -- (iv), `γ₁ = 3/4`, `I₀ = (-r, r)`
    refine ⟨3 / 4, L * (2 * r) ^ (1 - (3/4:ℝ)) + 2 * (2 * r) ^ (1 - (3/4:ℝ)), Ioo (-r) r,
      by norm_num, by norm_num,
      by have h1 := hpow (1 - (3/4:ℝ)); linarith [mul_nonneg hL h1.le], isOpen_Ioo,
      ⟨by linarith, hr⟩, ⟨by linarith, by linarith⟩, ?_⟩
    intro n _ x hx y hy
    have hx' : x ∈ Icc (-r) r := Ioo_subset_Icc_self hx.2
    have hy' : y ∈ Icc (-r) r := Ioo_subset_Icc_self hy.2
    have hxy : 0 ≤ |x - y| ^ (3/4:ℝ) := Real.rpow_nonneg (abs_nonneg _) _
    by_cases h : G n
    · obtain ⟨h3, hn1, ha, hs⟩ := hG n h
      have hsub := hs.2.2.1
      rw [hQ_pos n h, hderiv n h x (hsub hx'), hderiv n h y (hsub hy')]
      have hb := hs.2.2.2.2.2.2.2.1 x hx' y hy'
      have : 0 ≤ 2 * (2 * r) ^ (1 - (3/4:ℝ)) * |x - y| ^ (3/4:ℝ) :=
        mul_nonneg (mul_nonneg (by norm_num) (hpow _).le) hxy
      nlinarith
    · rw [hQ_neg n h, deriv_sq']
      have hb := holder_two_mul (r := r) (α := 3/4) (by norm_num) x hx' y hy'
      have : 0 ≤ L * (2 * r) ^ (1 - (3/4:ℝ)) * |x - y| ^ (3/4:ℝ) :=
        mul_nonneg (mul_nonneg hL (hpow _).le) hxy
      show |2 * x - 2 * y| ≤ _
      nlinarith
  · -- (v), the Mhaskar–Rakhmanov–Saff equations (101)–(102)
    intro n _
    by_cases h : G n
    · obtain ⟨h3, hn1, ha, hs⟩ := hG n h
      have hsub := hs.2.2.1
      have hmem : ∀ x ∈ Ioo (-1:ℝ) 1, x ∈ Ioo (-(1 / (2 * a n))) (1 / (2 * a n)) :=
        fun x hx => hsub ⟨by linarith [hx.1], by linarith [hx.2]⟩
      rw [hQ_pos n h]
      have e1 : ∫ x in Ioo (-1:ℝ) 1, x * deriv (QjM (ν n) n (a n)) x / √(1 - x ^ 2) =
          ∫ x in Ioo (-1:ℝ) 1, x * QjM' (ν n) n (a n) x / √(1 - x ^ 2) :=
        setIntegral_congr_fun measurableSet_Ioo fun x hx => by
          simp only [hderiv n h x (hmem x hx)]
      have e2 : ∫ x in Ioo (-1:ℝ) 1, deriv (QjM (ν n) n (a n)) x / √(1 - x ^ 2) =
          ∫ x in Ioo (-1:ℝ) 1, QjM' (ν n) n (a n) x / √(1 - x ^ 2) :=
        setIntegral_congr_fun measurableSet_Ioo fun x hx => by
          simp only [hderiv n h x (hmem x hx)]
      have s1 := UniformLanczos.arcsine_substitution (fun x => x * QjM' (ν n) n (a n) x)
      have s2 := UniformLanczos.arcsine_substitution (QjM' (ν n) n (a n))
      simp only at s1
      rw [e1, e2, s1, s2, hs.2.2.2.2.2.2.2.2.2, mul_zero]
      exact ⟨hs.2.2.2.2.2.2.2.2.1, rfl⟩
    · rw [hQ_neg n h, deriv_sq']
      have s1 := UniformLanczos.arcsine_substitution (fun x => x * (2 * x))
      have s2 := UniformLanczos.arcsine_substitution (fun x => 2 * x)
      simp only at s1
      simp only at s2
      rw [s1, s2, integral_cos_two_cos, integral_two_cos, mul_zero,
        one_div_mul_cancel Real.pi_ne_zero]
      exact ⟨rfl, rfl⟩

/-! ### Theorem 5.9 -/

/-- The admissible indices of the proof: `ν(n) ≥ M_b`, `n ≥ 1`, `n/ν(n) ∈ [t₁, t₂]`. -/
def Good (Mb : ℕ) (t₁ t₂ : ℝ) (ν : ℕ → ℕ) (n : ℕ) : Prop :=
  Mb ≤ ν n ∧ 1 ≤ n ∧ (n:ℝ) / (ν n : ℝ) ∈ Icc t₁ t₂

/-- The inequality behind `ℰ_{n,ν(n)} → 0`. -/
theorem key_bound {x ξ R : ℝ} (hx0 : 0 < x) (hx1 : x < 1 / 2) (hξ0 : 0 < ξ) (hξ1 : ξ < 1 / 2)
    (hR : |R| ≤ 1) : |x ^ 2 * R - ξ ^ 2 / 4| ≤ |x - ξ| + |R - 1 / 4| := by
  have e : x ^ 2 * R - ξ ^ 2 / 4 = (x - ξ) * ((x + ξ) * R) + ξ ^ 2 * (R - 1 / 4) := by ring
  rw [e]
  have h1 : |(x - ξ) * ((x + ξ) * R)| ≤ |x - ξ| := by
    rw [abs_mul, abs_mul]
    have hxξ : |x + ξ| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith
    have h : |x + ξ| * |R| ≤ 1 := by
      nlinarith [abs_nonneg (x + ξ), abs_nonneg R]
    exact mul_le_of_le_one_right (abs_nonneg _) h
  have h2 : |ξ ^ 2 * (R - 1 / 4)| ≤ |R - 1 / 4| := by
    rw [abs_mul]
    have h : |ξ ^ 2| ≤ 1 := by
      rw [abs_of_nonneg (by positivity)]
      nlinarith
    calc |ξ ^ 2| * |R - 1 / 4| ≤ 1 * |R - 1 / 4| :=
          mul_le_mul_of_nonneg_right h (abs_nonneg _)
      _ = |R - 1 / 4| := one_mul _
  have htri : |(x - ξ) * ((x + ξ) * R) + ξ ^ 2 * (R - 1 / 4)| ≤
      |(x - ξ) * ((x + ξ) * R)| + |ξ ^ 2 * (R - 1 / 4)| := by
    rw [abs_le]
    constructor
    · linarith [neg_abs_le ((x - ξ) * ((x + ξ) * R)), neg_abs_le (ξ ^ 2 * (R - 1 / 4))]
    · linarith [le_abs_self ((x - ξ) * ((x + ξ) * R)), le_abs_self (ξ ^ 2 * (R - 1 / 4))]
  linarith

/-- The step *Sequences* of the proof: along every `ν` with `n/ν(n) ∈ [t₁, t₂]` for large `n`,
`ℰ_{n,ν(n)} = β_n^{[ν(n)]}/ν(n)² - F(n/ν(n)) → 0`. -/
theorem seq_limit (hLL : LL_13_4) {t₁ t₂ : ℝ} (ht₁ : 0 < t₁) (ν : ℕ → ℕ)
    (hν : ∀ᶠ n in atTop, 1 ≤ ν n ∧ (n:ℝ) / (ν n : ℝ) ∈ Icc t₁ t₂) :
    Tendsto (fun n => betaM (ν n) n / (ν n : ℝ) ^ 2 - Profile.F ((n:ℝ) / (ν n : ℝ)))
      atTop (𝓝 0) := by
  classical
  obtain ⟨b, lo, r, L, M₀, hlo, hlob, hb, hr, hrb, hL, hU⟩ := lemma_5_8_uniform (t₂ := t₂) ht₁
  obtain ⟨b', lo', K, M₀', hlo', hlob', hb', hE⟩ :=
    UniformLanczos.Joined.endpoint_actual (t₂ := t₂) ht₁
  obtain ⟨Mb, hM0, hM0', hM3⟩ : ∃ Mb : ℕ, M₀ ≤ Mb ∧ M₀' ≤ Mb ∧ 3 ≤ Mb :=
    ⟨max M₀ (max M₀' 3), le_max_left _ _, le_trans (le_max_left _ _) (le_max_right _ _),
      le_trans (le_max_right _ _) (le_max_right _ _)⟩
  have hU' : ∀ M : ℕ, M₀ ≤ M → ∀ j : ℕ, 1 ≤ j → (j:ℝ) / M ∈ Icc t₁ t₂ →
      ∃ x ∈ Ioo lo b, Spec58 b r L M j x := hU
  -- eventually every index is admissible
  have hνG : ∀ᶠ n in atTop, Good Mb t₁ t₂ ν n := by
    filter_upwards [hν, eventually_ge_atTop (⌈t₂ * Mb⌉₊ + 1)] with n hn hN
    obtain ⟨hν1, ht⟩ := hn
    have hνpos : (0:ℝ) < ν n := by exact_mod_cast (show 0 < ν n by omega)
    have ht₂ : 0 < t₂ := lt_of_lt_of_le ht₁ (le_trans ht.1 ht.2)
    have hle : (n:ℝ) ≤ t₂ * ν n := (div_le_iff₀ hνpos).mp ht.2
    refine ⟨?_, by omega, ht⟩
    by_contra hlt
    push_neg at hlt
    have h1 : (ν n : ℝ) < Mb := by exact_mod_cast hlt
    have h2 : t₂ * Mb ≤ (⌈t₂ * Mb⌉₊ : ℝ) := Nat.le_ceil _
    have h3 : ((⌈t₂ * Mb⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hN
    push_cast at h3
    linarith [mul_lt_mul_of_pos_left h1 ht₂]
  -- the roots `ξ_{n,ν(n)}`
  have hch : ∀ n, ∃ x : ℝ, Good Mb t₁ t₂ ν n → x ∈ Ioo lo b ∧ Spec58 b r L (ν n) n x := by
    intro n
    by_cases h : Good Mb t₁ t₂ ν n
    · obtain ⟨x, hx, hs⟩ := hU' (ν n) (le_trans hM0 h.1) n h.2.1 h.2.2
      exact ⟨x, fun _ => ⟨hx, hs⟩⟩
    · exact ⟨1, fun h' => absurd h' h⟩
  choose a ha using hch
  have hgood : ∀ n, Good Mb t₁ t₂ ν n →
      3 ≤ ν n ∧ 1 ≤ n ∧ 0 < a n ∧ Spec58 b r L (ν n) n (a n) := fun n h =>
    ⟨le_trans hM3 h.1, h.2.1, lt_trans hlo (ha n h).1.1, (ha n h).2⟩
  -- the sequence belongs to `𝒬`, so `A_{n,n-1} → 1/2`
  have hQ := classQ_seq (Good Mb t₁ t₂ ν) ν a hr hL hgood
  have hA := LLA_tendsto hLL hQ
  obtain ⟨R, hRdef⟩ : ∃ R : ℕ → ℝ, ∀ n, R n = recSq (moment (seqI (Good Mb t₁ t₂ ν) a n)
      (weight (seqQ (Good Mb t₁ t₂ ν) ν a) n)) (n - 1) :=
    ⟨fun n => recSq (moment (seqI (Good Mb t₁ t₂ ν) a n)
      (weight (seqQ (Good Mb t₁ t₂ ν) ν a) n)) (n - 1), fun n => rfl⟩
  have hApos : ∀ᶠ n in atTop, 0 < LLA (seqI (Good Mb t₁ t₂ ν) a) (seqQ (Good Mb t₁ t₂ ν) ν a) n
      (n - 1) := hA.eventually (lt_mem_nhds (by norm_num))
  have hR : Tendsto R atTop (𝓝 (1 / 4)) := by
    have h2 := hA.pow 2
    rw [show ((1:ℝ) / 2) ^ 2 = 1 / 4 by norm_num] at h2
    refine h2.congr' ?_
    filter_upwards [hApos] with n hn
    have hpos : 0 < recSq (moment (seqI (Good Mb t₁ t₂ ν) a n)
        (weight (seqQ (Good Mb t₁ t₂ ν) ν a) n)) (n - 1) := Real.sqrt_pos.mp hn
    rw [hRdef n]
    exact Real.sq_sqrt hpos.le
  have hRbd : ∀ᶠ n in atTop, R n ∈ Ioo (0:ℝ) 1 :=
    hR.eventually (Ioo_mem_nhds (by norm_num) (by norm_num))
  have hR' : Tendsto (fun n => |R n - 1 / 4|) atTop (𝓝 0) := by
    have := tendsto_iff_norm_sub_tendsto_zero.mp hR
    simpa only [Real.norm_eq_abs] using this
  have hg : Tendsto (fun n : ℕ => |K| * t₂ / n + |R n - 1 / 4|) atTop (𝓝 0) := by
    simpa using (tendsto_const_div_atTop_nhds_zero_nat (|K| * t₂)).add hR'
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun n => norm_nonneg _) ?_ hg
  filter_upwards [hνG, hRbd] with n hn hRn
  rw [sub_zero, Real.norm_eq_abs]
  obtain ⟨h3, hn1, hapos, hs⟩ := hgood n hn
  have hax := (ha n hn).1
  have htI : (n:ℝ) / (ν n : ℝ) ∈ Icc t₁ t₂ := hn.2.2
  have ht0 : 0 < (n:ℝ) / (ν n : ℝ) := lt_of_lt_of_le ht₁ htI.1
  have hνpos : (0:ℝ) < ν n := by exact_mod_cast (show 0 < ν n by omega)
  have hnpos : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  -- (142) for this index
  have hR_eq : R n = recSq (moment (OpenInt.finite (-(1 / (2 * a n))) (1 / (2 * a n)))
      (fun x => Real.exp (-2 * (n:ℝ) * QjM (ν n) n (a n) x))) (n - 1) := by
    have hI : seqI (Good Mb t₁ t₂ ν) a n = OpenInt.finite (-(1 / (2 * a n))) (1 / (2 * a n)) :=
      if_pos hn
    have hQn : seqQ (Good Mb t₁ t₂ ν) ν a n = QjM (ν n) n (a n) := if_pos hn
    have hw : weight (seqQ (Good Mb t₁ t₂ ν) ν a) n =
        fun x => Real.exp (-2 * (n:ℝ) * QjM (ν n) n (a n) x) := by
      funext x
      simp only [weight, hQn]
    rw [hRdef n, hI, hw]
  have hβ : betaM (ν n) n / (ν n : ℝ) ^ 2 = a n ^ 2 * R n := by
    have hν0 : (ν n : ℝ) ≠ 0 := hνpos.ne'
    rw [scaling_142 (M := ν n) (by omega) hn1 hapos, ← hR_eq, div_eq_iff (pow_ne_zero 2 hν0)]
    ring
  -- `ξ_{n,ν(n)} - ξ_t`, Lemma 5.7(b)
  obtain ⟨⟨a0, ha0, hH0, -⟩, ⟨aM, haM, hΦM, -, hclose⟩⟩ := hE (ν n) (le_trans hM0' hn.1) _ htI
  have ha0ξ : a0 = Profile.ξ ((n:ℝ) / (ν n : ℝ)) :=
    Profile.ξ_unique ht0 ⟨(lt_trans hlo' ha0.1).le, lt_trans ha0.2 hb'⟩ hH0
  obtain ⟨ξM, -, -, huniqM⟩ := lemma_5_7a_actual h3 ht0
  have haM_eq : aM = a n := by
    rw [huniqM aM ⟨(lt_trans hlo' haM.1).le, lt_trans haM.2 hb'⟩ hΦM,
      huniqM (a n) ⟨hapos.le, lt_trans hax.2 hb⟩ hs.1]
  have hdiff : |a n - Profile.ξ ((n:ℝ) / (ν n : ℝ))| ≤ K / (ν n : ℝ) := by
    rw [← haM_eq, ← ha0ξ]
    exact hclose a0 ⟨ha0.1.le, ha0.2.le⟩ hH0
  have hK : K / (ν n : ℝ) ≤ |K| * t₂ / n := by
    have hle : (n:ℝ) ≤ t₂ * ν n := (div_le_iff₀ hνpos).mp htI.2
    calc K / (ν n : ℝ) ≤ |K| / (ν n : ℝ) := div_le_div_of_nonneg_right (le_abs_self K) hνpos.le
      _ ≤ |K| * t₂ / n := by
        rw [div_le_div_iff₀ hνpos hnpos]
        nlinarith [abs_nonneg K, mul_le_mul_of_nonneg_left hle (abs_nonneg K)]
  have hξ := (Profile.ξ_spec ht0).1
  have hRabs : |R n| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hRn.1, hRn.2]
  have hF : Profile.F ((n:ℝ) / (ν n : ℝ)) = Profile.ξ ((n:ℝ) / (ν n : ℝ)) ^ 2 / 4 := rfl
  rw [hβ, hF]
  have hkey := key_bound hapos (lt_trans hax.2 hb) hξ.1 hξ.2 hRabs
  linarith

/-- Theorem 5.9 for `𝒦 ⊂ [t₁, t₂]`: `ε`–`L` form. -/
theorem theorem_5_9_interval (hLL : LL_13_4) {t₁ t₂ : ℝ} (ht₁ : 0 < t₁) (ht₁₂ : t₁ < t₂) :
    ∀ ε > 0, ∃ L : ℕ, ∀ j M : ℕ, L ≤ j → 1 ≤ M ∧ (j:ℝ) / M ∈ Icc t₁ t₂ →
      |betaM M j / (M:ℝ) ^ 2 - Profile.F ((j:ℝ) / M)| < ε := by
  refine UniformLanczos.uniform_of_sequential
    (fun N M => betaM M N / (M:ℝ) ^ 2 - Profile.F ((N:ℝ) / M))
    (fun N M => 1 ≤ M ∧ (N:ℝ) / M ∈ Icc t₁ t₂) (fun N M => 1 ≤ M ∧ (N:ℝ) / M ∈ Icc t₁ t₂)
    (fun _ _ h => h) ?_ ?_
  · filter_upwards [UniformLanczos.fill_ratio ht₁ ht₁₂] with n hn
    obtain ⟨M, h1, h2, h3⟩ := hn
    exact ⟨M, h1, h2, h3⟩
  · intro m hm
    exact seq_limit hLL ht₁ m hm

/-- **Theorem 5.9** (`ε`–`L` form of (141)), assuming only (105) of Levin–Lubinsky: for every
compact `𝒦 ⊂ (0, ∞)` and `ε > 0` there is `L` with `|β_j^{[M]}/M² - F(j/M)| < ε` for all
`j ≥ L` and `j/M ∈ 𝒦`. -/
theorem theorem_5_9 (hLL : LL_13_4) {K : Set ℝ} (hK : IsCompact K) (hK0 : K ⊆ Ioi 0) :
    ∀ ε > 0, ∃ L : ℕ, ∀ j M : ℕ, L ≤ j → (j:ℝ) / M ∈ K →
      |betaM M j / (M:ℝ) ^ 2 - Profile.F ((j:ℝ) / M)| < ε := by
  intro ε hε
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · refine ⟨0, fun j M _ hjM => ?_⟩
    rw [hKe] at hjM
    simp at hjM
  obtain ⟨t₁, ht₁K, ht₁⟩ := hK.exists_isLeast hKne
  obtain ⟨t₂, ht₂K, ht₂⟩ := hK.exists_isGreatest hKne
  have ht₁pos : 0 < t₁ := hK0 ht₁K
  have hsub : K ⊆ Icc t₁ (t₂ + 1) := fun x hx => ⟨ht₁ hx, by linarith [ht₂ hx]⟩
  have hlt : t₁ < t₂ + 1 := by linarith [ht₂ ht₁K]
  obtain ⟨L, hL⟩ := theorem_5_9_interval hLL ht₁pos hlt ε hε
  refine ⟨L, fun j M hj hjM => hL j M hj ⟨?_, hsub hjM⟩⟩
  rcases Nat.eq_zero_or_pos M with h0 | hpos
  · subst h0
    simp only [Nat.cast_zero, div_zero] at hjM
    exact absurd (Set.mem_Ioi.mp (hK0 hjM)) (lt_irrefl (0:ℝ))
  · omega

/-- **Theorem 5.9**, eq. (141): `lim_{L→∞} sup_{j ≥ L, j/M ∈ 𝒦} |β_j^{[M]}/M² - F(j/M)| = 0`,
assuming only (105) of Levin–Lubinsky. -/
theorem theorem_5_9_sup (hLL : LL_13_4) {K : Set ℝ} (hK : IsCompact K) (hK0 : K ⊆ Ioi 0) :
    Tendsto (fun L : ℕ => ⨆ p : {p : ℕ × ℕ // L ≤ p.1 ∧ (p.1:ℝ) / (p.2:ℝ) ∈ K},
      |betaM p.1.2 p.1.1 / (p.1.2:ℝ) ^ 2 - Profile.F ((p.1.1:ℝ) / (p.1.2:ℝ))|) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨L, hL⟩ := theorem_5_9 hLL hK hK0 (ε / 2) (by positivity)
  refine ⟨L, fun L' hL' => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (Real.iSup_nonneg fun p => abs_nonneg _)]
  refine lt_of_le_of_lt (Real.iSup_le (fun p => (hL p.1.1 p.1.2 (le_trans hL' p.2.1) p.2.2).le)
    (by positivity)) (half_lt_self hε)

end UniformLanczos.Theorem59

#print axioms UniformLanczos.Theorem59.recSq_eq_norm_ratio
#print axioms UniformLanczos.Theorem59.recSq_scale
#print axioms UniformLanczos.Theorem59.LLA_tendsto
#print axioms UniformLanczos.Theorem59.moment_QjM
#print axioms UniformLanczos.Theorem59.scaling_142
#print axioms UniformLanczos.Theorem59.classQ_seq
#print axioms UniformLanczos.Theorem59.seq_limit
#print axioms UniformLanczos.Theorem59.theorem_5_9_interval
#print axioms UniformLanczos.Theorem59.theorem_5_9
#print axioms UniformLanczos.Theorem59.theorem_5_9_sup
