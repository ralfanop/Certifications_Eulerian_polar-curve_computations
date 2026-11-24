import Manuscript16.V166L2SpectralInverse
import Manuscript16.V166SpectralCutoffs
import Manuscript16.DiracMaxwellGraphSpace20261124

/-!
# M16 §13: coefficient-space model of `L₀ = W_R ⊕ D₃` (`eq:mixed-L0-164`, `eq:mixed-L0gap-164`)

`DiracMaxwellGraphSpace20261124.mixedBlock_isFredholm_iff_and_index_eq` (#585) proves
`thm:dirac-maxwell-obstruction-164` (i)–(ii) for an abstract closed operator `L₀` that is
bijective `dom L₀ → X`, with compact ambient inverse `R₀` and `‖R₀‖ ≤ 2/3`. This file
constructs one such `L₀` explicitly and discharges all of these premises for it.

The Hilbert space is `X = ℓ²(MixedIndex, ℂ)`, the coefficient space of the spectral list of
`W_R ⊕ D₃` already fixed in `V166L2SpectralInverse` (#422, carried over byte-identically):

* Maxwell modes `(ℓ, m) = (l + 2, l + 2 + 2k)`, `k ∈ ℤ \ {0, −ℓ}`, multiplicity
  `2(ℓ² − 1)`, eigenvalue `ℓ² − m² = −4k(ℓ + k)` (`eq:mixed-maxwell-index-164`);
* spatial Dirac modes `±(n + 3/2)`, multiplicity `(n + 1)(n + 2)` for each sign.

`L₀` is multiplication by these eigenvalues on its maximal domain
`{x ∈ ℓ² | (λᵢ xᵢ) ∈ ℓ²}` (Mathlib `LinearPMap`). Proved here:

* `multOp_isClosed`: every maximal-domain multiplication operator on `ℓ²` is closed;
* `multOp_injective`, `multOp_surjective`, `ambientResolvent_multOp`: if `λᵢ wᵢ = 1` with
  `w` bounded, the operator is bijective `dom → ℓ²` and its ambient inverse `R₀` (as built
  by the open mapping theorem in #585) is the bounded diagonal operator `diag(w)`;
* `diagonal_isCompactOperator`: `diag(w)` is compact when `{i | ε < ‖wᵢ‖}` is finite for
  every `ε > 0` (norm limit of the finite-rank cutoffs of #436);
* for the M16 spectral list: `L0_isClosed`, `L0_injective`, `L0_surjective`,
  `L0_ambientResolvent_norm : ‖R₀‖ = 2/3` (`eq:mixed-L0gap-164`, attained on the Dirac
  mode `n = 0`), `L0_ambientResolvent_compact`;
* `coefficientModel_isFredholm_iff_and_index_eq`: for every bounded `E` with `‖E‖ < 3/2`
  and bounded `A_P, B, C`, `𝒜` is Fredholm iff `A_P` is, and then `ind 𝒜 = ind A_P`.
  No premise on `L₀` or `R₀` remains.

Scope. This is the spectral (coefficient-space) realization of `L₀`. The unitary
identification of `ℓ²(MixedIndex)` with `R ⊕ L²(S³; Σ)` that diagonalizes `W_R` and `D₃`
(spectral decomposition of the Maxwell wave operator on the deck-even nonresonant space,
and the classical Dirac spectrum `±(n + 3/2)` of the round `S³`) is a published input and is
NOT formalized here; no geometric statement on `S³` is derived from this file. Also NOT
formalized: the Schatten statement `L₀⁻¹ ∈ S_p ⇔ p > 3` (`eq:mixed-schatten-164`) and every
`det₄` statement (`eq:mixed-det4-164`, `eq:mixed-det4-criterion-164`).
-/

noncomputable section

open scoped ENNReal

namespace Manuscript16.DiracMaxwellCoefficientModel20261124

open Manuscript16.V166L2SpectralInverse Manuscript16.V166SpectralCutoffs
open Manuscript16.DiracMaxwellGraphSpace20261124

section Diagonal

variable {ι : Type*}

/-! ### Compactness of a diagonal operator whose weights tend to zero -/

/-- A finite-rank cutoff (#436) is a compact operator: it factors through `Fin n → ℂ`. -/
theorem cutoff_isCompactOperator [DecidableEq ι] {n : ℕ} (d : ι → ℂ) (e : Fin n ↪ ι) :
    IsCompactOperator (cutoff d e) := by
  obtain ⟨F, G, h⟩ := cutoff_factor d e
  rw [h]
  exact (isCompactOperator_of_locallyCompactSpace_rng G).comp_clm F

/-- `diag(d)` is compact on `ℓ²` if, for every `ε > 0`, only finitely many weights have
modulus `> ε`. -/
theorem diagonal_isCompactOperator (d : ι → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hd : ∀ i, ‖d i‖ ≤ M) (hfin : ∀ ε : ℝ, 0 < ε → {i | ε < ‖d i‖}.Finite) :
    IsCompactOperator (diagonal d M hM hd) := by
  classical
  have hclosed : IsClosed {f : L2 ι →L[ℂ] L2 ι | IsCompactOperator f} :=
    isClosed_setOfPred_isCompactOperator
  have hmem : diagonal d M hM hd ∈ closure {f : L2 ι →L[ℂ] L2 ι | IsCompactOperator f} := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hSfin : {i | ε / 2 < ‖d i‖}.Finite := hfin (ε / 2) (half_pos hε)
    let s := hSfin.toFinset
    let e : Fin s.card ↪ ι := s.equivFin.symm.toEmbedding.trans (Function.Embedding.subtype _)
    have htail : ∀ i ∉ Set.range e, ‖d i‖ ≤ ε / 2 := by
      intro i hi
      by_contra h
      apply hi
      have his : i ∈ s := hSfin.mem_toFinset.2 (not_le.1 h)
      exact ⟨s.equivFin ⟨i, his⟩, by simp [e]⟩
    refine ⟨cutoff d e, cutoff_isCompactOperator d e, ?_⟩
    rw [dist_eq_norm]
    calc ‖diagonal d M hM hd - cutoff d e‖ ≤ ε / 2 :=
          diagonal_cutoff_error d e M (ε / 2) hM hd (by positivity) htail
      _ < ε := half_lt_self hε
  rw [hclosed.closure_eq] at hmem
  exact hmem

/-! ### Multiplication operators on their maximal domain -/

/-- The maximal domain `{x ∈ ℓ² | (λᵢ xᵢ) ∈ ℓ²}`. -/
def multDomain (lam : ι → ℂ) : Submodule ℂ (L2 ι) where
  carrier := {x | Memℓp (fun i => lam i * x i) 2}
  add_mem' := by
    intro x y hx hy
    have h : (fun i => lam i * (x + y : L2 ι) i) =
        (fun i => lam i * x i) + (fun i => lam i * y i) := by
      funext i
      change lam i * (x i + y i) = lam i * x i + lam i * y i
      ring
    change Memℓp (fun i => lam i * (x + y : L2 ι) i) 2
    rw [h]
    exact Memℓp.add hx hy
  zero_mem' := by
    have h : (fun i => lam i * (0 : L2 ι) i) = 0 := by
      funext i
      change lam i * 0 = 0
      ring
    change Memℓp (fun i => lam i * (0 : L2 ι) i) 2
    rw [h]
    exact zero_memℓp
  smul_mem' := by
    intro c x hx
    have h : (fun i => lam i * (c • x : L2 ι) i) = c • (fun i => lam i * x i) := by
      funext i
      change lam i * (c * x i) = c * (lam i * x i)
      ring
    change Memℓp (fun i => lam i * (c • x : L2 ι) i) 2
    rw [h]
    exact Memℓp.const_smul hx c

theorem mem_multDomain (lam : ι → ℂ) (x : L2 ι) :
    x ∈ multDomain lam ↔ Memℓp (fun i => lam i * x i) 2 :=
  Iff.rfl

/-- Multiplication by `λ` on its maximal domain, as a linear map into `ℓ²`. -/
def multMap (lam : ι → ℂ) : multDomain lam →ₗ[ℂ] L2 ι where
  toFun x := ⟨fun i => lam i * (x : L2 ι) i, x.2⟩
  map_add' x y := by
    apply lp.ext
    funext i
    change lam i * ((x : L2 ι) i + (y : L2 ι) i) = lam i * (x : L2 ι) i + lam i * (y : L2 ι) i
    ring
  map_smul' c x := by
    apply lp.ext
    funext i
    change lam i * (c * (x : L2 ι) i) = c * (lam i * (x : L2 ι) i)
    ring

/-- The unbounded multiplication operator `x ↦ (λᵢ xᵢ)` with maximal domain. -/
def multOp (lam : ι → ℂ) : L2 ι →ₗ.[ℂ] L2 ι :=
  ⟨multDomain lam, multMap lam⟩

theorem multOp_apply (lam : ι → ℂ) (x : (multOp lam).domain) (i : ι) :
    multOp lam x i = lam i * (x : L2 ι) i :=
  rfl

/-- `(x, y)` lies on the graph iff `yᵢ = λᵢ xᵢ` for every `i`; membership of `x` in the
maximal domain is then automatic. -/
theorem mem_graph_multOp_iff (lam : ι → ℂ) (p : L2 ι × L2 ι) :
    p ∈ (multOp lam).graph ↔ ∀ i, p.2 i = lam i * p.1 i := by
  obtain ⟨a, b⟩ := p
  constructor
  · intro hp i
    obtain ⟨x, hx1, hx2⟩ := ((multOp lam).mem_graph_iff).1 hp
    change (x : L2 ι) = a at hx1
    change multOp lam x = b at hx2
    rw [← hx1, ← hx2]
    rfl
  · intro h
    have hfun : (fun i => lam i * a i) = (b : ι → ℂ) := funext fun i => (h i).symm
    have hdom : a ∈ multDomain lam := by
      rw [mem_multDomain, hfun]
      exact lp.memℓp b
    refine ((multOp lam).mem_graph_iff).2 ⟨⟨a, hdom⟩, rfl, ?_⟩
    apply lp.ext
    exact hfun

/-- Every maximal-domain multiplication operator on `ℓ²` is closed. -/
theorem multOp_isClosed (lam : ι → ℂ) : (multOp lam).IsClosed := by
  have h : ((multOp lam).graph : Set (L2 ι × L2 ι)) =
      ⋂ i, {p : L2 ι × L2 ι | p.2 i = lam i * p.1 i} := by
    ext p
    simp only [SetLike.mem_coe, Set.mem_iInter, Set.mem_ofPred_eq]
    exact mem_graph_multOp_iff lam p
  change IsClosed ((multOp lam).graph : Set (L2 ι × L2 ι))
  rw [h]
  refine isClosed_iInter fun i => isClosed_eq ?_ ?_
  · exact (lp.evalCLM ℂ (fun _ : ι => ℂ) 2 i).continuous.comp continuous_snd
  · exact continuous_const.mul
      ((lp.evalCLM ℂ (fun _ : ι => ℂ) 2 i).continuous.comp continuous_fst)

/-- Injectivity when every `λᵢ` has an inverse `wᵢ`. -/
theorem multOp_injective (lam w : ι → ℂ) (hinv : ∀ i, lam i * w i = 1) :
    Function.Injective (multOp lam) := by
  intro x y h
  apply Subtype.ext
  apply lp.ext
  funext i
  have hxy : lam i * (x : L2 ι) i = lam i * (y : L2 ι) i :=
    congrArg (fun z : L2 ι => z i) h
  have hne : lam i ≠ 0 := by
    intro h0
    have := hinv i
    rw [h0, zero_mul] at this
    exact zero_ne_one this
  exact mul_left_cancel₀ hne hxy

/-- Surjectivity onto `ℓ²` when the inverse weights `w` are bounded: the preimage of `y`
is `diag(w) y`. -/
theorem multOp_surjective (lam w : ι → ℂ) (M : ℝ) (hM : 0 ≤ M) (hw : ∀ i, ‖w i‖ ≤ M)
    (hinv : ∀ i, lam i * w i = 1) : Function.Surjective (multOp lam) := by
  intro y
  have hfun : (fun i => lam i * diagonal w M hM hw y i) = (y : ι → ℂ) := by
    funext i
    rw [diagonal_apply, ← mul_assoc, hinv, one_mul]
  have hdom : diagonal w M hM hw y ∈ multDomain lam := by
    rw [mem_multDomain, hfun]
    exact lp.memℓp y
  refine ⟨⟨diagonal w M hM hw y, hdom⟩, ?_⟩
  apply lp.ext
  exact hfun

/-- The ambient inverse `R₀ = j ∘ L₀⁻¹` of #585 is the bounded diagonal operator `diag(w)`. -/
theorem ambientResolvent_multOp (lam w : ι → ℂ) (M : ℝ) (hM : 0 ≤ M) (hw : ∀ i, ‖w i‖ ≤ M)
    (hinv : ∀ i, lam i * w i = 1) (hcl : (multOp lam).IsClosed)
    (hinj : Function.Injective (multOp lam)) (hsurj : Function.Surjective (multOp lam)) :
    ambientResolvent (multOp lam) hcl hinj hsurj = diagonal w M hM hw := by
  refine ContinuousLinearMap.ext fun y => ?_
  obtain ⟨x, hx, hLx⟩ := ambientResolvent_spec (multOp lam) hcl hinj hsurj y
  rw [← hx]
  apply lp.ext
  funext i
  have h1 : lam i * (x : L2 ι) i = y i := congrArg (fun z : L2 ι => z i) hLx
  have hw0 : w i * lam i = 1 := by rw [mul_comm]; exact hinv i
  change (x : L2 ι) i = diagonal w M hM hw y i
  rw [diagonal_apply]
  calc (x : L2 ι) i = w i * (lam i * (x : L2 ι) i) := by rw [← mul_assoc, hw0, one_mul]
    _ = w i * y i := by rw [h1]

end Diagonal

/-! ### The M16 spectral list -/

/-- Maxwell eigenvalue on the mode `(ℓ, m) = (l + 2, l + 2 + 2k)`: `−4k(ℓ + k)`. -/
def maxwellEigen (i : MaxwellIndex) : ℝ :=
  (-4 : ℝ) * (i.2.1.1 : ℝ) * (((i.1 : ℤ) + 2 + i.2.1.1 : ℤ) : ℝ)

/-- `−4k(ℓ + k) = ℓ² − m²` with `ℓ = l + 2`, `m = ℓ + 2k` (`eq:mixed-maxwell-index-164`). -/
theorem maxwellEigen_eq_sq_sub_sq (i : MaxwellIndex) :
    maxwellEigen i = (((i.1 : ℤ) + 2 : ℤ) : ℝ) ^ 2 -
      ((((i.1 : ℤ) + 2 + 2 * i.2.1.1 : ℤ)) : ℝ) ^ 2 := by
  unfold maxwellEigen
  push_cast
  ring

/-- Spatial Dirac eigenvalue `±(n + 3/2)`. -/
def diracEigen (i : DiracIndex) : ℝ :=
  if i.2.1 then (i.1 : ℝ) + 3 / 2 else -((i.1 : ℝ) + 3 / 2)

/-- The eigenvalue of `L₀ = W_R ⊕ D₃` on each mode of `MixedIndex`. -/
def mixedEigen : MixedIndex → ℂ :=
  Sum.elim (fun i => (maxwellEigen i : ℂ)) (fun i => (diracEigen i : ℂ))

theorem maxwellWeight_eq_inv (i : MaxwellIndex) : maxwellWeight i = (maxwellEigen i)⁻¹ :=
  rfl

theorem diracWeight_eq_inv (i : DiracIndex) : diracWeight i = (diracEigen i)⁻¹ := by
  unfold diracWeight diracEigen
  split_ifs
  · rfl
  · rw [inv_neg]

theorem maxwellEigen_ne_zero (i : MaxwellIndex) : maxwellEigen i ≠ 0 := by
  have hk : (i.2.1.1 : ℝ) ≠ 0 := by exact_mod_cast i.2.1.2.1
  have hz : (i.1 : ℤ) + 2 + i.2.1.1 ≠ 0 := by
    intro h
    apply i.2.1.2.2
    omega
  have hz' : (((i.1 : ℤ) + 2 + i.2.1.1 : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hz
  unfold maxwellEigen
  exact mul_ne_zero (mul_ne_zero (by norm_num) hk) hz'

theorem diracEigen_ne_zero (i : DiracIndex) : diracEigen i ≠ 0 := by
  have h : (0 : ℝ) < (i.1 : ℝ) + 3 / 2 := by positivity
  unfold diracEigen
  split_ifs
  · exact h.ne'
  · exact neg_ne_zero.2 h.ne'

theorem mixedEigen_mul_weight (i : MixedIndex) : mixedEigen i * mixedWeight i = 1 := by
  cases i with
  | inl x =>
    change (maxwellEigen x : ℂ) * (maxwellWeight x : ℂ) = 1
    rw [maxwellWeight_eq_inv, ← Complex.ofReal_mul, mul_inv_cancel₀ (maxwellEigen_ne_zero x),
      Complex.ofReal_one]
  | inr x =>
    change (diracEigen x : ℂ) * (diracWeight x : ℂ) = 1
    rw [diracWeight_eq_inv, ← Complex.ofReal_mul, mul_inv_cancel₀ (diracEigen_ne_zero x),
      Complex.ofReal_one]

/-! ### Only finitely many inverse eigenvalues exceed any `ε > 0` -/

theorem maxwell_finite (ε : ℝ) (hε : 0 < ε) :
    {i : MaxwellIndex | ε < |maxwellWeight i|}.Finite := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  have hsub : {i : MaxwellIndex | ε < |maxwellWeight i|} ⊆
      {l : ℕ | l ≤ 2 * N}.sigma
        (fun _ => {p | p.1.1 ∈ Set.Icc (-(N : ℤ)) (N : ℤ)}) := by
    intro i hi
    change ε < |maxwellWeight i| at hi
    have ha : (1 : ℝ) ≤ |(i.2.1.1 : ℝ)| := by exact_mod_cast Int.one_le_abs i.2.1.2.1
    have hz : (i.1 : ℤ) + 2 + i.2.1.1 ≠ 0 := by
      intro h
      apply i.2.1.2.2
      omega
    have hc : (1 : ℝ) ≤ |(((i.1 : ℤ) + 2 + i.2.1.1 : ℤ) : ℝ)| := by
      exact_mod_cast Int.one_le_abs hz
    have hw : |maxwellWeight i| =
        (4 * (|(i.2.1.1 : ℝ)| * |(((i.1 : ℤ) + 2 + i.2.1.1 : ℤ) : ℝ)|))⁻¹ := by
      unfold maxwellWeight
      rw [abs_inv, abs_mul, abs_mul, mul_assoc]
      norm_num
    rw [hw] at hi
    set a := |(i.2.1.1 : ℝ)| with ha_def
    set c := |(((i.1 : ℤ) + 2 + i.2.1.1 : ℤ) : ℝ)| with hc_def
    have hpos : 0 < 4 * (a * c) := by positivity
    have h1 : ε * (4 * (a * c)) < 1 := by
      have := mul_lt_mul_of_pos_right hi hpos
      rwa [inv_mul_cancel₀ hpos.ne'] at this
    have hεa : a * ε < 1 := by nlinarith
    have hεc : c * ε < 1 := by nlinarith
    have hak : a < N := lt_trans ((lt_div_iff₀ hε).2 hεa) hN
    have hck : c < N := lt_trans ((lt_div_iff₀ hε).2 hεc) hN
    have hak' : |i.2.1.1| < (N : ℤ) := by
      rw [ha_def, ← Int.cast_abs] at hak
      exact_mod_cast hak
    have hck' : |(i.1 : ℤ) + 2 + i.2.1.1| < (N : ℤ) := by
      rw [hc_def, ← Int.cast_abs] at hck
      exact_mod_cast hck
    obtain ⟨hk1, hk2⟩ := abs_lt.1 hak'
    obtain ⟨hb1, hb2⟩ := abs_lt.1 hck'
    refine ⟨?_, ?_⟩
    · change i.1 ≤ 2 * N
      omega
    · exact ⟨hk1.le, hk2.le⟩
  refine Set.Finite.subset (Set.Finite.sigma (Set.finite_le_nat _) fun l _ => ?_) hsub
  have hfin : (Set.Icc (-(N : ℤ)) (N : ℤ)).Finite := Set.toFinite _
  refine ((hfin.preimage (fun _ _ _ _ h => Subtype.ext h)).prod
    (Set.finite_univ (α := Fin (2 * ((l + 2) ^ 2 - 1))))).subset ?_
  intro p hp
  exact ⟨hp, Set.mem_univ _⟩

theorem dirac_finite (ε : ℝ) (hε : 0 < ε) :
    {i : DiracIndex | ε < |diracWeight i|}.Finite := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  have hsub : {i : DiracIndex | ε < |diracWeight i|} ⊆
      {n : ℕ | n ≤ N}.sigma (fun _ => Set.univ) := by
    intro i hi
    change ε < |diracWeight i| at hi
    have hpos : (0 : ℝ) < (i.1 : ℝ) + 3 / 2 := by positivity
    have hw : |diracWeight i| = ((i.1 : ℝ) + 3 / 2)⁻¹ := by
      rw [diracWeight_eq_inv]
      unfold diracEigen
      split_ifs
      · rw [abs_inv, abs_of_pos hpos]
      · rw [abs_inv, abs_neg, abs_of_pos hpos]
    rw [hw] at hi
    have h1 : ε * ((i.1 : ℝ) + 3 / 2) < 1 := by
      have := mul_lt_mul_of_pos_right hi hpos
      rwa [inv_mul_cancel₀ hpos.ne'] at this
    have h2 : (i.1 : ℝ) * ε < 1 := by nlinarith
    have h3 : (i.1 : ℝ) < N := lt_trans ((lt_div_iff₀ hε).2 h2) hN
    have h4 : i.1 < N := by exact_mod_cast h3
    exact ⟨h4.le, Set.mem_univ _⟩
  exact Set.Finite.subset (Set.Finite.sigma (Set.finite_le_nat _)
    fun _ _ => Set.finite_univ) hsub

theorem mixedWeight_finite (ε : ℝ) (hε : 0 < ε) :
    {i : MixedIndex | ε < ‖mixedWeight i‖}.Finite := by
  refine (((maxwell_finite ε hε).image Sum.inl).union
    ((dirac_finite ε hε).image Sum.inr)).subset ?_
  rintro (i | i) hi
  · left
    refine ⟨i, ?_, rfl⟩
    change ε < ‖(maxwellWeight i : ℂ)‖ at hi
    rw [Complex.norm_real, Real.norm_eq_abs] at hi
    exact hi
  · right
    refine ⟨i, ?_, rfl⟩
    change ε < ‖(diracWeight i : ℂ)‖ at hi
    rw [Complex.norm_real, Real.norm_eq_abs] at hi
    exact hi

/-- The coefficient-space inverse `R₀ = diag(1/λ)` of #422 is a compact operator. -/
theorem mixedInverse_isCompactOperator : IsCompactOperator mixedInverse :=
  diagonal_isCompactOperator mixedWeight (2 / 3) (by norm_num) mixedWeight_bound
    mixedWeight_finite

/-! ### `L₀ = W_R ⊕ D₃` on `ℓ²(MixedIndex)` and the obstruction theorem -/

/-- `L₀ = W_R ⊕ D₃`: multiplication by the spectral list on its maximal domain. -/
def L0 : L2 MixedIndex →ₗ.[ℂ] L2 MixedIndex :=
  multOp mixedEigen

theorem L0_apply_maxwell (x : L0.domain) (i : MaxwellIndex) :
    L0 x (Sum.inl i) = (maxwellEigen i : ℂ) * (x : L2 MixedIndex) (Sum.inl i) :=
  rfl

theorem L0_apply_dirac (x : L0.domain) (i : DiracIndex) :
    L0 x (Sum.inr i) = (diracEigen i : ℂ) * (x : L2 MixedIndex) (Sum.inr i) :=
  rfl

theorem L0_isClosed : L0.IsClosed :=
  multOp_isClosed mixedEigen

theorem L0_injective : Function.Injective L0 :=
  multOp_injective mixedEigen mixedWeight mixedEigen_mul_weight

theorem L0_surjective : Function.Surjective L0 :=
  multOp_surjective mixedEigen mixedWeight (2 / 3) (by norm_num) mixedWeight_bound
    mixedEigen_mul_weight

/-- The ambient inverse of `L₀` is the coefficient-space inverse of #422. -/
theorem L0_ambientResolvent :
    ambientResolvent L0 L0_isClosed L0_injective L0_surjective = mixedInverse :=
  ambientResolvent_multOp mixedEigen mixedWeight (2 / 3) (by norm_num) mixedWeight_bound
    mixedEigen_mul_weight L0_isClosed L0_injective L0_surjective

/-- `eq:mixed-L0gap-164`: `‖R₀‖ = max(1/4, 2/3) = 2/3`. -/
theorem L0_ambientResolvent_norm :
    ‖ambientResolvent L0 L0_isClosed L0_injective L0_surjective‖ = (2 : ℝ) / 3 := by
  rw [L0_ambientResolvent]
  exact mixedInverse_norm

theorem L0_ambientResolvent_compact :
    IsCompactOperator (ambientResolvent L0 L0_isClosed L0_injective L0_surjective) := by
  rw [L0_ambientResolvent]
  exact mixedInverse_isCompactOperator

/-- `thm:dirac-maxwell-obstruction-164` (i)–(ii) for the coefficient-space `L₀ = W_R ⊕ D₃`:
for every bounded `E` with `‖E‖ < 3/2` and bounded `A_P, B, C`, the mixed block operator
`𝒜 : P × D(L₀) → P × X` is Fredholm iff `A_P` is, and then `ind 𝒜 = ind A_P`. -/
theorem coefficientModel_isFredholm_iff_and_index_eq {P : Type*} [NormedAddCommGroup P]
    [InnerProductSpace ℂ P] [CompleteSpace P]
    (E : L2 MixedIndex →L[ℂ] L2 MixedIndex) (hE : ‖E‖ < (3 : ℝ) / 2)
    (A : P →L[ℂ] P) (B : L2 MixedIndex →L[ℂ] P) (C : P →L[ℂ] L2 MixedIndex) :
    ((mixedBlock L0 L0_isClosed L0_injective L0_surjective E
        L0_ambientResolvent_norm.le hE A B C).IsFredholm ↔ A.IsFredholm) ∧
      (A.IsFredholm →
        (mixedBlock L0 L0_isClosed L0_injective L0_surjective E
          L0_ambientResolvent_norm.le hE A B C).index = A.index) :=
  mixedBlock_isFredholm_iff_and_index_eq L0 L0_isClosed L0_injective L0_surjective E
    L0_ambientResolvent_norm.le hE A B C L0_ambientResolvent_compact

end Manuscript16.DiracMaxwellCoefficientModel20261124

#print axioms Manuscript16.DiracMaxwellCoefficientModel20261124.cutoff_isCompactOperator
#print axioms Manuscript16.DiracMaxwellCoefficientModel20261124.diagonal_isCompactOperator
#print axioms Manuscript16.DiracMaxwellCoefficientModel20261124.mem_multDomain
#print axioms Manuscript16.DiracMaxwellCoefficientModel20261124.multOp_apply
#print axioms Manuscript16.DiracMaxwellCoefficientModel20261124.mem_graph_multOp_iff
#print axioms Manuscript16.DiracMaxwellCoefficientModel20261124.multOp_isClosed
#print axioms Manuscript16.DiracMaxwellCoefficientModel20261124.multOp_injective
#print axioms Manuscript16.DiracMaxwellCoefficientModel20261124.multOp_surjective
#print axioms Manuscript16.DiracMaxwellCoefficientModel20261124.ambientResolvent_multOp
#print axioms Manuscript16.DiracMaxwellCoefficientModel20261124.maxwellEigen_eq_sq_sub_sq
#print axioms Manuscript16.DiracMaxwellCoefficientModel20261124.maxwellWeight_eq_inv
#print axioms Manuscript16.DiracMaxwellCoefficientModel20261124.diracWeight_eq_inv
#print axioms Manuscript16.DiracMaxwellCoefficientModel20261124.maxwellEigen_ne_zero
#print axioms Manuscript16.DiracMaxwellCoefficientModel20261124.diracEigen_ne_zero
#print axioms Manuscript16.DiracMaxwellCoefficientModel20261124.mixedEigen_mul_weight
#print axioms Manuscript16.DiracMaxwellCoefficientModel20261124.maxwell_finite
#print axioms Manuscript16.DiracMaxwellCoefficientModel20261124.dirac_finite
#print axioms Manuscript16.DiracMaxwellCoefficientModel20261124.mixedWeight_finite
#print axioms Manuscript16.DiracMaxwellCoefficientModel20261124.mixedInverse_isCompactOperator
#print axioms Manuscript16.DiracMaxwellCoefficientModel20261124.L0_apply_maxwell
#print axioms Manuscript16.DiracMaxwellCoefficientModel20261124.L0_apply_dirac
#print axioms Manuscript16.DiracMaxwellCoefficientModel20261124.L0_isClosed
#print axioms Manuscript16.DiracMaxwellCoefficientModel20261124.L0_injective
#print axioms Manuscript16.DiracMaxwellCoefficientModel20261124.L0_surjective
#print axioms Manuscript16.DiracMaxwellCoefficientModel20261124.L0_ambientResolvent
#print axioms Manuscript16.DiracMaxwellCoefficientModel20261124.L0_ambientResolvent_norm
#print axioms Manuscript16.DiracMaxwellCoefficientModel20261124.L0_ambientResolvent_compact
#print axioms Manuscript16.DiracMaxwellCoefficientModel20261124.coefficientModel_isFredholm_iff_and_index_eq
