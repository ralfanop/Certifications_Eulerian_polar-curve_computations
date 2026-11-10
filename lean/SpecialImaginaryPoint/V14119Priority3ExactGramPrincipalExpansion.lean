import SpecialImaginaryPoint.V14119Priority3WeightedGramMinorStep
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.RingTheory.MatrixPolynomialAlgebra
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Priority 3 — exact determinant equals weighted sum of all principal minors

Close the finite-dimensional algebraic bridge:
  det(I + zG) = Σ_{S⊆Fin m} z^|S| det(G_{S,S}).

Here G is the completely unrestricted complex mixed Gram matrix of
arbitrary Hilbert rank-one vectors, and neither positive definiteness,
normality nor invertibility is imposed.

The identity is established through Mathlib's exact characteristic
polynomial coefficient-minor formula, degree bound, and a disjoint
decomposition of the finite powerset by cardinality. Combined with
PR #117 it enables applying the sharp first-order minor insertion
bound to actual finite Gram Fredholm determinants. It is NOT yet
a proof of the full trace-norm perturbation theorem on arbitrary S₁.
-/

noncomputable section

namespace Manuscript14Priority3.ExactGramPrincipalExpansion

open Matrix Polynomial
open scoped InnerProductSpace Ring
open Manuscript14Priority3.MinorExpansionIncrement
open Manuscript14Priority3.WeightedGramMinorStep

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Exact complex matrix determinant as weighted sum over ALL
principal submatrices, with arbitrary z and no structural hypotheses. -/
theorem weightedGram_full_expansion_eq_det {m : ℕ}
    (u v : Fin m → E) (z : ℂ) :
    principalExpansion (weightedGramMinor u v z) Finset.univ =
      (1 + z • Manuscript14Priority3.ComplexGramMinorBridge.mixedGram u v).det := by
  let G : Matrix (Fin m) (Fin m) ℂ :=
    Manuscript14Priority3.ComplexGramMinorBridge.mixedGram u v
  let p : ℂ[X] := Matrix.det (1 + (Polynomial.X : ℂ[X]) • G.map Polynomial.C)
  have hdegree : p.natDegree < m + 1 := by
    have h :=
      Polynomial.natDegree_det_X_add_C_le G (1 : Matrix (Fin m) (Fin m) ℂ)
    have ht : p.natDegree ≤ m := by
      simpa only [p, add_comm] using h
    exact Nat.lt_succ_of_le ht
  have hcoeff (k : ℕ) :
      p.coeff k =
        ∑ s ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
          (G.submatrix (Subtype.val : s → Fin m)
            (Subtype.val : s → Fin m)).det :=
    Matrix.coeff_det_one_add_X_smul_eq_sum_minors G k
  have hsum :
      (∑ s ∈ (Finset.univ : Finset (Fin m)).powerset,
        weightedGramMinor u v z s) =
      ∑ k ∈ Finset.range (m + 1),
        ∑ s ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
          weightedGramMinor u v z s := by
    classical
    rw [Finset.powerset_card_biUnion]
    rw [Finset.sum_biUnion]
    · simp only [Finset.card_univ, Fintype.card_fin]
    · intro i hi j hj hij
      exact Finset.disjoint_powersetCard_of_ne hij _ _
  have hterms (k : ℕ) :
      (∑ s ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
        weightedGramMinor u v z s) = p.coeff k * z ^ k := by
    rw [hcoeff]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro s hs
    have hcard : s.card = k := (Finset.mem_powersetCard.mp hs).2
    simp only [weightedGramMinor, G, hcard]
    ring
  have heval :
      p.eval z = (1 + z • G).det := by
    dsimp [p]
    rw [eval_det, matPolyEquiv_eval_eq_map]
    congr 1
    ext i j
    classical
    by_cases hij : i = j
    · subst j
      simp [Matrix.one_apply]
      ring
    · simp [Matrix.one_apply, hij]
      ring
  calc
    principalExpansion (weightedGramMinor u v z) Finset.univ =
        ∑ s ∈ (Finset.univ : Finset (Fin m)).powerset,
          weightedGramMinor u v z s := rfl
    _ = ∑ k ∈ Finset.range (m + 1),
          ∑ s ∈ (Finset.univ : Finset (Fin m)).powersetCard k,
            weightedGramMinor u v z s := hsum
    _ = ∑ k ∈ Finset.range (m + 1), p.coeff k * z ^ k := by
      apply Finset.sum_congr rfl
      intro k hk
      exact hterms k
    _ = p.eval z := (Polynomial.eval_eq_sum_range' hdegree z).symm
    _ = (1 + z • G).det := heval

#print axioms Manuscript14Priority3.ExactGramPrincipalExpansion.weightedGram_full_expansion_eq_det

end Manuscript14Priority3.ExactGramPrincipalExpansion
