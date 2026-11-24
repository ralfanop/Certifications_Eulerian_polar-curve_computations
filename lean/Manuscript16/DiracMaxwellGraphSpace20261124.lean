import Manuscript16.V165GraphNeumann
import Manuscript16.V166CompactTransfer
import Manuscript16.DiracMaxwellObstructionIndex20261124

/-!
# M16 §13, `thm:dirac-maxwell-obstruction-164` (i)–(ii): graph space of a closed `L₀`

`DiracMaxwellObstructionIndex20261124` (#576) proves `ind 𝒜 = ind A_P` with the
continuous linear equivalence `L : D ≃L X` and the compactness of `B L⁻¹ C` as
premises. This file removes the first premise for an abstract closed operator and
reduces the second one to compactness of the ambient inverse of `L₀`:

* `L₀ : X →ₗ.[𝕜] X` is an unbounded operator (Mathlib `LinearPMap`) on a Banach
  space `X`; `D = GraphSpace L₀` is its graph `{(x, L₀ x)}` with the product norm
  `max ‖x‖ ‖L₀ x‖` (equivalent to the sum graph norm `‖x‖ + ‖L₀ x‖`:
  `max ≤ sum ≤ 2 max`). If `L₀` is closed, `D` is a Banach space
  (`graphSpace_completeSpace`).
* If moreover `L₀ : dom L₀ → X` is bijective, the bounded map `D → X`,
  `(x, L₀ x) ↦ L₀ x`, is a continuous linear equivalence by the open mapping
  theorem (`graphEquiv`); `R₀ = j ∘ L₀⁻¹ : X →L X` is the bounded ambient inverse,
  `R₀ y ∈ dom L₀`, `L₀ (R₀ y) = y` (`ambientResolvent_spec`).
* For `E : X →L X` with `‖R₀‖ ≤ 2/3`, `‖E‖ < 3/2`, the Neumann construction of
  `V165GraphNeumann.perturbedEquiv` (#401) gives `L = L₀ + E : D ≃L X`
  (`perturbedGraphEquiv_toGraph`); the unique solution of `L₀ x + E x = y` is
  `j (L⁻¹ y)` (`perturbed_solution_iff`) and
  `‖L⁻¹ y‖_D ≤ (1 + (1 + ‖E‖)/(3/2 - ‖E‖)) ‖y‖` (`perturbed_inverse_graph_norm_le`).
* If `R₀` is compact, `B L⁻¹ C` is compact (`V166CompactTransfer`, #404) and, for
  `𝒜 = block A_P (B ∘ j) C L : P × D →L P × X`, `𝒜` is Fredholm iff `A_P` is, with
  `ind 𝒜 = ind A_P` (`mixedBlock_isFredholm_iff_and_index_eq`).

Premises of the final theorem: `L₀` closed and bijective `dom L₀ → X`,
`‖R₀‖ ≤ 2/3`, `R₀` compact, `‖E‖ < 3/2`, `P` a complete complex inner-product
space. NOT formalized here: the concrete `L₀ = W_R ⊕ D₃` (its closedness,
invertibility, `‖R₀‖ = 2/3`, compactness or Schatten membership of `R₀` from
`eq:mixed-schatten-164`), and every `det₄` statement.
-/

noncomputable section

namespace Manuscript16.DiracMaxwellGraphSpace20261124

open Manuscript16.V165GraphNeumann Manuscript16.V166CompactTransfer
open Manuscript16.V165GraphSchur Manuscript16.DiracMaxwellObstructionIndex20261124

section GraphSpace

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- The graph space of `L₀`: the graph submodule of `X × X` with the product norm
`max ‖x‖ ‖L₀ x‖`. -/
abbrev GraphSpace (L₀ : X →ₗ.[𝕜] X) : Type _ := ↥L₀.graph

/-- The inclusion `j : D → X`, `(x, L₀ x) ↦ x`. -/
def graphIncl (L₀ : X →ₗ.[𝕜] X) : GraphSpace L₀ →L[𝕜] X :=
  (ContinuousLinearMap.fst 𝕜 X X).comp L₀.graph.subtypeL

/-- `L₀` realized as a bounded map on its graph space, `(x, L₀ x) ↦ L₀ x`. -/
def graphOp (L₀ : X →ₗ.[𝕜] X) : GraphSpace L₀ →L[𝕜] X :=
  (ContinuousLinearMap.snd 𝕜 X X).comp L₀.graph.subtypeL

/-- The point `(x, L₀ x)` of the graph space attached to `x ∈ dom L₀`. -/
def toGraph (L₀ : X →ₗ.[𝕜] X) (x : L₀.domain) : GraphSpace L₀ :=
  ⟨((x : X), L₀ x), L₀.mem_graph x⟩

theorem graphIncl_toGraph (L₀ : X →ₗ.[𝕜] X) (x : L₀.domain) :
    graphIncl L₀ (toGraph L₀ x) = x :=
  rfl

theorem graphOp_toGraph (L₀ : X →ₗ.[𝕜] X) (x : L₀.domain) :
    graphOp L₀ (toGraph L₀ x) = L₀ x :=
  rfl

/-- The graph norm: `‖(x, L₀ x)‖_D = max ‖x‖ ‖L₀ x‖`. -/
theorem graphSpace_norm (L₀ : X →ₗ.[𝕜] X) (d : GraphSpace L₀) :
    ‖d‖ = max ‖graphIncl L₀ d‖ ‖graphOp L₀ d‖ :=
  rfl

/-- Every point of the graph space is `(x, L₀ x)` for some `x ∈ dom L₀`. -/
theorem exists_toGraph (L₀ : X →ₗ.[𝕜] X) (d : GraphSpace L₀) :
    ∃ x : L₀.domain, toGraph L₀ x = d := by
  obtain ⟨x, hx1, hx2⟩ := (L₀.mem_graph_iff).1 d.2
  exact ⟨x, Subtype.ext (Prod.ext hx1 hx2)⟩

/-- The graph space of a closed operator on a Banach space is a Banach space. -/
theorem graphSpace_completeSpace [CompleteSpace X] (L₀ : X →ₗ.[𝕜] X)
    (hcl : L₀.IsClosed) : CompleteSpace (GraphSpace L₀) :=
  completeSpace_coe_iff_isComplete.2 (IsClosed.isComplete hcl)

theorem graphOp_injective (L₀ : X →ₗ.[𝕜] X) (hinj : Function.Injective L₀) :
    Function.Injective (graphOp L₀) := by
  intro d d' h
  obtain ⟨x, rfl⟩ := exists_toGraph L₀ d
  obtain ⟨x', rfl⟩ := exists_toGraph L₀ d'
  rw [graphOp_toGraph, graphOp_toGraph] at h
  rw [hinj h]

theorem graphOp_surjective (L₀ : X →ₗ.[𝕜] X) (hsurj : Function.Surjective L₀) :
    Function.Surjective (graphOp L₀) := by
  intro y
  obtain ⟨x, rfl⟩ := hsurj y
  exact ⟨toGraph L₀ x, rfl⟩

variable [CompleteSpace X]

/-- Open mapping theorem: for closed `L₀` with `L₀ : dom L₀ → X` bijective, the
realization `D → X` is a continuous linear equivalence. -/
def graphEquiv (L₀ : X →ₗ.[𝕜] X) (hcl : L₀.IsClosed)
    (hinj : Function.Injective L₀) (hsurj : Function.Surjective L₀) :
    GraphSpace L₀ ≃L[𝕜] X :=
  haveI := graphSpace_completeSpace L₀ hcl
  ContinuousLinearEquiv.ofBijective (graphOp L₀)
    (LinearMap.ker_eq_bot.mpr (graphOp_injective L₀ hinj))
    (LinearMap.range_eq_top.mpr (graphOp_surjective L₀ hsurj))

theorem graphEquiv_apply (L₀ : X →ₗ.[𝕜] X) (hcl : L₀.IsClosed)
    (hinj : Function.Injective L₀) (hsurj : Function.Surjective L₀)
    (d : GraphSpace L₀) : graphEquiv L₀ hcl hinj hsurj d = graphOp L₀ d :=
  rfl

/-- The bounded ambient inverse `R₀ = j ∘ L₀⁻¹ : X →L X`. -/
def ambientResolvent (L₀ : X →ₗ.[𝕜] X) (hcl : L₀.IsClosed)
    (hinj : Function.Injective L₀) (hsurj : Function.Surjective L₀) : X →L[𝕜] X :=
  ambientInverse (graphIncl L₀) (graphEquiv L₀ hcl hinj hsurj)

/-- `R₀ y ∈ dom L₀` and `L₀ (R₀ y) = y`. -/
theorem ambientResolvent_spec (L₀ : X →ₗ.[𝕜] X) (hcl : L₀.IsClosed)
    (hinj : Function.Injective L₀) (hsurj : Function.Surjective L₀) (y : X) :
    ∃ x : L₀.domain, (x : X) = ambientResolvent L₀ hcl hinj hsurj y ∧ L₀ x = y := by
  obtain ⟨x, hx⟩ := exists_toGraph L₀ ((graphEquiv L₀ hcl hinj hsurj).symm y)
  refine ⟨x, ?_, ?_⟩
  · change (x : X) = graphIncl L₀ ((graphEquiv L₀ hcl hinj hsurj).symm y)
    rw [← hx, graphIncl_toGraph]
  · rw [← graphOp_toGraph, hx, ← graphEquiv_apply L₀ hcl hinj hsurj,
      ContinuousLinearEquiv.apply_symm_apply]

/-- `L = L₀ + E : D ≃L X`, by the Neumann construction of #401. -/
def perturbedGraphEquiv (L₀ : X →ₗ.[𝕜] X) (hcl : L₀.IsClosed)
    (hinj : Function.Injective L₀) (hsurj : Function.Surjective L₀) (E : X →L[𝕜] X)
    (hG : ‖ambientResolvent L₀ hcl hinj hsurj‖ ≤ (2 : ℝ) / 3)
    (hE : ‖E‖ < (3 : ℝ) / 2) : GraphSpace L₀ ≃L[𝕜] X :=
  perturbedEquiv (graphIncl L₀) (graphEquiv L₀ hcl hinj hsurj) E hG hE

/-- `L (x, L₀ x) = L₀ x + E x` for every `x ∈ dom L₀`. -/
theorem perturbedGraphEquiv_toGraph (L₀ : X →ₗ.[𝕜] X) (hcl : L₀.IsClosed)
    (hinj : Function.Injective L₀) (hsurj : Function.Surjective L₀) (E : X →L[𝕜] X)
    (hG : ‖ambientResolvent L₀ hcl hinj hsurj‖ ≤ (2 : ℝ) / 3)
    (hE : ‖E‖ < (3 : ℝ) / 2) (x : L₀.domain) :
    perturbedGraphEquiv L₀ hcl hinj hsurj E hG hE (toGraph L₀ x) = L₀ x + E x :=
  perturbedEquiv_apply (graphIncl L₀) (graphEquiv L₀ hcl hinj hsurj) E hG hE (toGraph L₀ x)

/-- `x ∈ dom L₀` solves `L₀ x + E x = y` iff `(x, L₀ x) = L⁻¹ y`; in particular the
solution exists and is unique. -/
theorem perturbed_solution_iff (L₀ : X →ₗ.[𝕜] X) (hcl : L₀.IsClosed)
    (hinj : Function.Injective L₀) (hsurj : Function.Surjective L₀) (E : X →L[𝕜] X)
    (hG : ‖ambientResolvent L₀ hcl hinj hsurj‖ ≤ (2 : ℝ) / 3)
    (hE : ‖E‖ < (3 : ℝ) / 2) (x : L₀.domain) (y : X) :
    L₀ x + E x = y ↔
      toGraph L₀ x = (perturbedGraphEquiv L₀ hcl hinj hsurj E hG hE).symm y := by
  rw [← perturbedGraphEquiv_toGraph L₀ hcl hinj hsurj E hG hE x]
  exact (ContinuousLinearEquiv.eq_symm_apply _).symm

/-- Existence: `x = j (L⁻¹ y)` lies in `dom L₀` and solves `L₀ x + E x = y`. -/
theorem perturbed_solution_exists (L₀ : X →ₗ.[𝕜] X) (hcl : L₀.IsClosed)
    (hinj : Function.Injective L₀) (hsurj : Function.Surjective L₀) (E : X →L[𝕜] X)
    (hG : ‖ambientResolvent L₀ hcl hinj hsurj‖ ≤ (2 : ℝ) / 3)
    (hE : ‖E‖ < (3 : ℝ) / 2) (y : X) :
    ∃ x : L₀.domain,
      (x : X) = graphIncl L₀ ((perturbedGraphEquiv L₀ hcl hinj hsurj E hG hE).symm y) ∧
        L₀ x + E x = y := by
  obtain ⟨x, hx⟩ := exists_toGraph L₀ ((perturbedGraphEquiv L₀ hcl hinj hsurj E hG hE).symm y)
  refine ⟨x, ?_, (perturbed_solution_iff L₀ hcl hinj hsurj E hG hE x y).2 hx⟩
  rw [← hx, graphIncl_toGraph]

/-- Graph-norm bound for `L⁻¹ : X → D`:
`‖L⁻¹ y‖_D ≤ (1 + (1 + ‖E‖)/(3/2 - ‖E‖)) ‖y‖`. -/
theorem perturbed_inverse_graph_norm_le (L₀ : X →ₗ.[𝕜] X) (hcl : L₀.IsClosed)
    (hinj : Function.Injective L₀) (hsurj : Function.Surjective L₀) (E : X →L[𝕜] X)
    (hG : ‖ambientResolvent L₀ hcl hinj hsurj‖ ≤ (2 : ℝ) / 3)
    (hE : ‖E‖ < (3 : ℝ) / 2) (y : X) :
    ‖(perturbedGraphEquiv L₀ hcl hinj hsurj E hG hE).symm y‖ ≤
      (1 + (1 + ‖E‖) / ((3 : ℝ) / 2 - ‖E‖)) * ‖y‖ := by
  set L := perturbedGraphEquiv L₀ hcl hinj hsurj E hG hE with hLdef
  have hpos : 0 < (3 : ℝ) / 2 - ‖E‖ := by linarith
  obtain ⟨x, hx⟩ := exists_toGraph L₀ (L.symm y)
  have hsol : L₀ x + E x = y :=
    (perturbed_solution_iff L₀ hcl hinj hsurj E hG hE x y).2 hx
  -- ambient bound `‖x‖ ≤ ‖y‖ / (3/2 - ‖E‖)` from #401
  have hamb : ‖(x : X)‖ ≤ 1 / ((3 : ℝ) / 2 - ‖E‖) * ‖y‖ := by
    have h := (ambientInverse (graphIncl L₀) L).le_opNorm y
    have hxe : ambientInverse (graphIncl L₀) L y = x := by
      change graphIncl L₀ (L.symm y) = x
      rw [← hx, graphIncl_toGraph]
    rw [hxe] at h
    exact h.trans (mul_le_mul_of_nonneg_right
      (perturbed_inverse_norm (graphIncl L₀) (graphEquiv L₀ hcl hinj hsurj) E hG hE)
      (norm_nonneg y))
  have hL0 : ‖L₀ x‖ ≤ ‖y‖ + ‖E‖ * ‖(x : X)‖ := by
    have : L₀ x = y - E x := by rw [← hsol, add_sub_cancel_right]
    rw [this]
    have h1 := norm_sub_le y (E x)
    have h2 := E.le_opNorm (x : X)
    linarith
  have hnorm : ‖L.symm y‖ = max ‖(x : X)‖ ‖L₀ x‖ := by
    rw [← hx, graphSpace_norm, graphIncl_toGraph, graphOp_toGraph]
  rw [hnorm]
  have hx' : (1 + ‖E‖) * ‖(x : X)‖ ≤ (1 + ‖E‖) / ((3 : ℝ) / 2 - ‖E‖) * ‖y‖ := by
    have h1 : 0 ≤ 1 + ‖E‖ := by positivity
    calc (1 + ‖E‖) * ‖(x : X)‖ ≤ (1 + ‖E‖) * (1 / ((3 : ℝ) / 2 - ‖E‖) * ‖y‖) :=
          mul_le_mul_of_nonneg_left hamb h1
      _ = (1 + ‖E‖) / ((3 : ℝ) / 2 - ‖E‖) * ‖y‖ := by ring
  have hy : 0 ≤ ‖y‖ := norm_nonneg y
  have hxn : 0 ≤ ‖(x : X)‖ := norm_nonneg _
  have hEn : 0 ≤ ‖E‖ := norm_nonneg E
  apply max_le
  · nlinarith
  · nlinarith

/-- If `R₀` is compact, the ambient inverse `j ∘ L⁻¹` of `L = L₀ + E` is compact. -/
theorem perturbed_ambientInverse_compact (L₀ : X →ₗ.[𝕜] X) (hcl : L₀.IsClosed)
    (hinj : Function.Injective L₀) (hsurj : Function.Surjective L₀) (E : X →L[𝕜] X)
    (hG : ‖ambientResolvent L₀ hcl hinj hsurj‖ ≤ (2 : ℝ) / 3)
    (hE : ‖E‖ < (3 : ℝ) / 2)
    (hcpt : IsCompactOperator (ambientResolvent L₀ hcl hinj hsurj)) :
    IsCompactOperator
      (ambientInverse (graphIncl L₀) (perturbedGraphEquiv L₀ hcl hinj hsurj E hG hE)) :=
  (perturbed_inverse_compact_iff (graphIncl L₀) (graphEquiv L₀ hcl hinj hsurj) E hG hE).2
    hcpt

end GraphSpace

section Block

variable {P X : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- The mixed block operator `𝒜 = [[A_P, B], [C, L₀ + E]] : P × D(L₀) →L P × X`,
with the ambient `B : X →L P` restricted to the graph space. -/
def mixedBlock (L₀ : X →ₗ.[ℂ] X) (hcl : L₀.IsClosed)
    (hinj : Function.Injective L₀) (hsurj : Function.Surjective L₀) (E : X →L[ℂ] X)
    (hG : ‖ambientResolvent L₀ hcl hinj hsurj‖ ≤ (2 : ℝ) / 3)
    (hE : ‖E‖ < (3 : ℝ) / 2) (A : P →L[ℂ] P) (B : X →L[ℂ] P) (C : P →L[ℂ] X) :
    (P × GraphSpace L₀) →L[ℂ] (P × X) :=
  block A (B.comp (graphIncl L₀)) C (perturbedGraphEquiv L₀ hcl hinj hsurj E hG hE)

omit [CompleteSpace P] in
/-- `𝒜 (p, (x, L₀ x)) = (A_P p + B x, C p + L₀ x + E x)`. -/
theorem mixedBlock_apply (L₀ : X →ₗ.[ℂ] X) (hcl : L₀.IsClosed)
    (hinj : Function.Injective L₀) (hsurj : Function.Surjective L₀) (E : X →L[ℂ] X)
    (hG : ‖ambientResolvent L₀ hcl hinj hsurj‖ ≤ (2 : ℝ) / 3)
    (hE : ‖E‖ < (3 : ℝ) / 2) (A : P →L[ℂ] P) (B : X →L[ℂ] P) (C : P →L[ℂ] X)
    (p : P) (x : L₀.domain) :
    mixedBlock L₀ hcl hinj hsurj E hG hE A B C (p, toGraph L₀ x) =
      (A p + B x, C p + (L₀ x + E x)) := by
  change (A p + B (graphIncl L₀ (toGraph L₀ x)),
    C p + perturbedGraphEquiv L₀ hcl hinj hsurj E hG hE (toGraph L₀ x)) = _
  rw [graphIncl_toGraph, perturbedGraphEquiv_toGraph]

omit [CompleteSpace P] in
/-- If `R₀` is compact, the Schur correction `B L⁻¹ C` is compact. -/
theorem schurCorrection_compact (L₀ : X →ₗ.[ℂ] X) (hcl : L₀.IsClosed)
    (hinj : Function.Injective L₀) (hsurj : Function.Surjective L₀) (E : X →L[ℂ] X)
    (hG : ‖ambientResolvent L₀ hcl hinj hsurj‖ ≤ (2 : ℝ) / 3)
    (hE : ‖E‖ < (3 : ℝ) / 2) (B : X →L[ℂ] P) (C : P →L[ℂ] X)
    (hcpt : IsCompactOperator (ambientResolvent L₀ hcl hinj hsurj)) :
    IsCompactOperator (schurCorrection (B.comp (graphIncl L₀)) C
      (perturbedGraphEquiv L₀ hcl hinj hsurj E hG hE)) := by
  have h := correction_compact (graphIncl L₀) B C
    (perturbedGraphEquiv L₀ hcl hinj hsurj E hG hE)
    (perturbed_ambientInverse_compact L₀ hcl hinj hsurj E hG hE hcpt)
  exact h

/-- `thm:dirac-maxwell-obstruction-164` (i)–(ii) for a closed bijective `L₀` with
compact ambient inverse `R₀`, `‖R₀‖ ≤ 2/3`, `‖E‖ < 3/2`: on the graph space,
`𝒜` is Fredholm iff `A_P` is Fredholm, and then `ind 𝒜 = ind A_P`. -/
theorem mixedBlock_isFredholm_iff_and_index_eq (L₀ : X →ₗ.[ℂ] X) (hcl : L₀.IsClosed)
    (hinj : Function.Injective L₀) (hsurj : Function.Surjective L₀) (E : X →L[ℂ] X)
    (hG : ‖ambientResolvent L₀ hcl hinj hsurj‖ ≤ (2 : ℝ) / 3)
    (hE : ‖E‖ < (3 : ℝ) / 2) (A : P →L[ℂ] P) (B : X →L[ℂ] P) (C : P →L[ℂ] X)
    (hcpt : IsCompactOperator (ambientResolvent L₀ hcl hinj hsurj)) :
    ((mixedBlock L₀ hcl hinj hsurj E hG hE A B C).IsFredholm ↔ A.IsFredholm) ∧
      (A.IsFredholm →
        (mixedBlock L₀ hcl hinj hsurj E hG hE A B C).index = A.index) :=
  block_isFredholm_iff_and_index_eq A (B.comp (graphIncl L₀)) C
    (perturbedGraphEquiv L₀ hcl hinj hsurj E hG hE)
    (schurCorrection_compact L₀ hcl hinj hsurj E hG hE B C hcpt)

end Block

end Manuscript16.DiracMaxwellGraphSpace20261124

#print axioms Manuscript16.DiracMaxwellGraphSpace20261124.graphIncl_toGraph
#print axioms Manuscript16.DiracMaxwellGraphSpace20261124.graphOp_toGraph
#print axioms Manuscript16.DiracMaxwellGraphSpace20261124.graphSpace_norm
#print axioms Manuscript16.DiracMaxwellGraphSpace20261124.exists_toGraph
#print axioms Manuscript16.DiracMaxwellGraphSpace20261124.graphSpace_completeSpace
#print axioms Manuscript16.DiracMaxwellGraphSpace20261124.graphOp_injective
#print axioms Manuscript16.DiracMaxwellGraphSpace20261124.graphOp_surjective
#print axioms Manuscript16.DiracMaxwellGraphSpace20261124.graphEquiv
#print axioms Manuscript16.DiracMaxwellGraphSpace20261124.graphEquiv_apply
#print axioms Manuscript16.DiracMaxwellGraphSpace20261124.ambientResolvent_spec
#print axioms Manuscript16.DiracMaxwellGraphSpace20261124.perturbedGraphEquiv_toGraph
#print axioms Manuscript16.DiracMaxwellGraphSpace20261124.perturbed_solution_iff
#print axioms Manuscript16.DiracMaxwellGraphSpace20261124.perturbed_solution_exists
#print axioms Manuscript16.DiracMaxwellGraphSpace20261124.perturbed_inverse_graph_norm_le
#print axioms Manuscript16.DiracMaxwellGraphSpace20261124.perturbed_ambientInverse_compact
#print axioms Manuscript16.DiracMaxwellGraphSpace20261124.mixedBlock_apply
#print axioms Manuscript16.DiracMaxwellGraphSpace20261124.schurCorrection_compact
#print axioms Manuscript16.DiracMaxwellGraphSpace20261124.mixedBlock_isFredholm_iff_and_index_eq
