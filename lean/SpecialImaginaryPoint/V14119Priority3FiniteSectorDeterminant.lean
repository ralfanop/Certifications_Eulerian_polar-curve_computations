import SpecialImaginaryPoint.V14119Priority3FiniteNuclearFredholm

/-!
# Manuscript 14.119 Priority 3 — operator-argument intrinsic finite Fredholm determinant

Following the certified representation-independent finite nuclear
determinant, package all finite sums of arbitrary complex rank-one
Hilbert maps as a genuine SUBSET of the project CFC Schatten-S₁
Banach space and define a Fredholm determinant as a FUNCTION OF
THE ACTUAL TRACE-CLASS OPERATOR, not of a chosen list of vectors.

The determinant is independent of the presentation witness, even
when different presentations have different lengths. For every
such actual finite-rank operator T, its intrinsic Fredholm
determinant is the limit, as N→∞, of determinants of its genuine
N-dimensional Hilbert-space compressions.

This is an unconditional construction on the finite-nuclear
operator sector only. The continuous universal extension to the
whole CFC Schatten S₁ space and the global dimension-independent
perturbation bound remain separate mathematical obligations.
-/

noncomputable section

namespace Manuscript14Priority3.FiniteNuclearFredholm
open Filter Topology InnerProductSpace
open scoped ComplexOrder lp
open Manuscript14Priority3.TraceClassModel

/-- A finite complex nuclear presentation. Arbitrary vectors uᵢ
and vᵢ are allowed; no positivity or orthogonality restriction. -/
structure Presentation where
  length : ℕ
  u : Fin length → H
  v : Fin length → H

/-- The actual CFC-S₁ Hilbert operator represented by P. -/
def Presentation.operator (P : Presentation) :
    ProbabilisticTheory.TraceClass H :=
  finiteNuclear P.length P.u P.v

/-- Its finite-dimensional Gram Fredholm determinant. -/
def Presentation.gramDet (P : Presentation) (z : ℂ) : ℂ :=
  Matrix.det (1 + z • gram P.length P.u P.v)

/-- Independence of the Gram determinant under two arbitrary finite
nuclear presentations of exactly the SAME genuine CFC S₁ operator,
even for different presentation lengths. -/
theorem Presentation.gramDet_eq_of_operator_eq
    (P Q : Presentation) (z : ℂ)
    (h : P.operator = Q.operator) :
    P.gramDet z = Q.gramDet z :=
  finiteNuclear_det_representation_independent
    P.length Q.length P.u P.v Q.u Q.v h z

/-- The ACTUAL finite-nuclear operator subset of genuine CFC S₁:
the domain is formed by operators, not by tagged presentations. -/
def finiteSector : Set (ProbabilisticTheory.TraceClass H) :=
  Set.range Presentation.operator

/-- Intrinsic operator-argument finite Fredholm determinant. The
presenter is chosen noncomputably but the resulting COMPLEX VALUE
is well-defined independently of that choice. -/
def determinantOnFiniteSector (T : finiteSector) (z : ℂ) : ℂ :=
  (Classical.choose T.property).gramDet z

/-- Essential well-definedness: the operator argument T determines
the value regardless of its arbitrary finite-rank presentation. -/
theorem determinantOnFiniteSector_eq
    (T : finiteSector) (P : Presentation)
    (hP : P.operator = T.val) (z : ℂ) :
    determinantOnFiniteSector T z = P.gramDet z := by
  unfold determinantOnFiniteSector
  exact Presentation.gramDet_eq_of_operator_eq
    (Classical.choose T.property) P z
    ((Classical.choose_spec T.property).trans hP.symm)

/-- The operator-level determinant evaluated at a genuine finite
nuclear operator agrees with its finite Gram Fredholm determinant. -/
theorem determinantOnFiniteSector_of_presentation
    (P : Presentation) (z : ℂ) :
    determinantOnFiniteSector
      ⟨P.operator, ⟨P, rfl⟩⟩ z = P.gramDet z :=
  determinantOnFiniteSector_eq _ P rfl z

/-- The intrinsic determinant FUNCTION ON FINITE-RANK OPERATORS
is exactly the limit of determinants of the actual Hilbert-space
compressions of that SAME trace-class operator. No formal
spectral labels or favorable coordinate presentation are used. -/
theorem determinantOnFiniteSector_compression_tendsto
    (T : finiteSector) (z : ℂ) :
    Tendsto
      (fun N : ℕ =>
        Manuscript14Priority3.FiniteRankFredholm.finiteDeterminant N T.val z)
      atTop (𝓝 (determinantOnFiniteSector T z)) := by
  let P : Presentation := Classical.choose T.property
  have hP : P.operator = T.val := Classical.choose_spec T.property
  have hlimP :
      Tendsto
        (fun N : ℕ =>
          Manuscript14Priority3.FiniteRankFredholm.finiteDeterminant N
            P.operator z)
        atTop (𝓝 (P.gramDet z)) :=
    finiteNuclear_det_tendsto P.length P.u P.v z
  have hvalue : P.gramDet z = determinantOnFiniteSector T z :=
    (determinantOnFiniteSector_eq T P hP z).symm
  rw [hP, hvalue] at hlimP
  exact hlimP

#print axioms Manuscript14Priority3.FiniteNuclearFredholm.Presentation.gramDet_eq_of_operator_eq
#print axioms Manuscript14Priority3.FiniteNuclearFredholm.determinantOnFiniteSector_eq
#print axioms Manuscript14Priority3.FiniteNuclearFredholm.determinantOnFiniteSector_of_presentation
#print axioms Manuscript14Priority3.FiniteNuclearFredholm.determinantOnFiniteSector_compression_tendsto

end Manuscript14Priority3.FiniteNuclearFredholm
