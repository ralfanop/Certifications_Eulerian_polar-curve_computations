import SpecialImaginaryPoint.V14119Priority3FiniteNuclearFredholm

/-!
# Manuscript 14.119 Priority 3 — actual intrinsic finite-rank Fredholm functional

The preceding kernel-certified sector proves:
* for ANY finite nuclear CFC-S₁ operator, the determinants of its actual
  finite-dimensional ambient Hilbert compressions converge;
* their limit is the finite Gram determinant;
* the limit is independent of the chosen finite rank-one presentation.

Here we package this into an ACTUAL ℂ-valued determinant FUNCTION defined
on the type of all CFC-S₁ maps possessing a finite nuclear presentation.
There is no requirement that the represented operator be positive,
normal, or diagonalizable.

Mathematical deliverables:
* construction of the intrinsic finite-rank Fredholm functional;
* independence of the chosen finite nuclear presentation;
* its limit from genuine ambient Hilbert-space compressions;
* normalization at z=0;
* continuity in the complex spectral parameter z.

The determinant is NOT YET defined on all S₁(H). Its extension requires
a uniform trace-norm perturbation inequality independent of rank.
Nothing in this file assumes that missing inequality.
-/

noncomputable section

namespace Manuscript14Priority3.FiniteNuclearFredholm

open Filter Topology
open scoped ComplexOrder lp
open Manuscript14Priority3.TraceClassModel

/-- A concrete finite nuclear rank-one presentation of the ACTUAL
CFC-S₁ Hilbert operator T; the number of terms is unrestricted. -/
structure Presentation (T : ProbabilisticTheory.TraceClass H) where
  length : ℕ
  leftVectors : Fin length → H
  rightVectors : Fin length → H
  represents : finiteNuclear length leftVectors rightVectors = T

/-- Domain of genuine CFC-S₁ operators with a finite nuclear
rank-one presentation. -/
abbrev HasFinitePresentation (T : ProbabilisticTheory.TraceClass H) : Prop :=
  Nonempty (Presentation T)

/-- Every explicit finite nuclear rank-one Hilbert operator belongs
to the domain of the intrinsic finite Fredholm determinant. -/
def canonicalPresentation (m : ℕ) (u v : Fin m → H) :
    Presentation (finiteNuclear m u v) where
  length := m
  leftVectors := u
  rightVectors := v
  represents := rfl

/-- Actual intrinsic Fredholm determinant for finite-rank CFC-S₁
operators, at any complex spectral parameter z. A witness
presentation may be chosen because the value is independent
of that witness, as certified below. -/
def detFinite (T : ProbabilisticTheory.TraceClass H)
    (h : HasFinitePresentation T) (z : ℂ) : ℂ :=
  let p := Classical.choice h
  Matrix.det (1 + z • gram p.length p.leftVectors p.rightVectors)

/-- The finite Fredholm determinant agrees with the intrinsic
Gram determinant of ANY other presentation of the SAME actual
CFC-S₁ Hilbert operator; neither the length nor the vectors
need agree with the witness chosen in the definition. -/
theorem detFinite_eq_of_presentation
    (T : ProbabilisticTheory.TraceClass H)
    (h : HasFinitePresentation T) (p : Presentation T) (z : ℂ) :
    detFinite T h z =
      Matrix.det (1 + z • gram p.length p.leftVectors p.rightVectors) := by
  let q : Presentation T := Classical.choice h
  have heq : finiteNuclear q.length q.leftVectors q.rightVectors =
      finiteNuclear p.length p.leftVectors p.rightVectors :=
    q.represents.trans p.represents.symm
  change Matrix.det
    (1 + z • gram q.length q.leftVectors q.rightVectors) = _
  exact finiteNuclear_det_representation_independent
    q.length p.length q.leftVectors q.rightVectors
    p.leftVectors p.rightVectors heq z

/-- The intrinsic finite Fredholm determinant of the actual
finite CFC-S₁ operator defined from u,v is precisely its
m-dimensional complex Gram determinant. -/
theorem detFinite_finiteNuclear (m : ℕ)
    (u v : Fin m → H) (z : ℂ) :
    detFinite (finiteNuclear m u v)
        ⟨canonicalPresentation m u v⟩ z =
      Matrix.det (1 + z • gram m u v) :=
  detFinite_eq_of_presentation
    (finiteNuclear m u v)
    ⟨canonicalPresentation m u v⟩
    (canonicalPresentation m u v) z

/-- The intrinsic finite-rank determinant is the EXACT limit of
determinants of real, non-diagonal, true finite ambient Hilbert
compressions, for every finite-rank CFC-S₁ operator, independent
of how the finite rank-one presentation was provided. -/
theorem detFinite_tendsto_compressions
    (T : ProbabilisticTheory.TraceClass H)
    (h : HasFinitePresentation T) (z : ℂ) :
    Tendsto
      (fun N : ℕ =>
        Manuscript14Priority3.FiniteRankFredholm.finiteDeterminant N T z)
      atTop (𝓝 (detFinite T h z)) := by
  let p : Presentation T := Classical.choice h
  have hl := finiteNuclear_det_tendsto
    p.length p.leftVectors p.rightVectors z
  rw [p.represents] at hl
  have hv := detFinite_eq_of_presentation T h p z
  rw [hv]
  exact hl

/-- Normalization: the finite Fredholm determinant is 1 at z=0
for EVERY genuine finite-rank CFC-S₁ map, irrespective of its
presentation. -/
theorem detFinite_zero
    (T : ProbabilisticTheory.TraceClass H)
    (h : HasFinitePresentation T) :
    detFinite T h 0 = 1 := by
  unfold detFinite
  simp

/-- The finite-rank operator's intrinsic Fredholm determinant is
a continuous function of ANY complex spectral parameter z.
No invertibility or positivity is required. -/
theorem detFinite_continuous_z
    (T : ProbabilisticTheory.TraceClass H)
    (h : HasFinitePresentation T) :
    Continuous (fun z : ℂ => detFinite T h z) := by
  let p : Presentation T := Classical.choice h
  change Continuous (fun z : ℂ =>
      Matrix.det ((1 : Matrix (Fin p.length) (Fin p.length) ℂ) +
        z • gram p.length p.leftVectors p.rightVectors))
  have hMat :
      Continuous (fun z : ℂ =>
        (1 : Matrix (Fin p.length) (Fin p.length) ℂ) +
        z • gram p.length p.leftVectors p.rightVectors) :=
    continuous_const.add (continuous_id.smul continuous_const)
  exact hMat.matrix_det

/-- Even the choice of the existence proof carries no numerical
information; the determinant is an actual functional on the
finite-nuclear CFC-S₁ operator, not on a chosen presentation. -/
theorem detFinite_independent_of_proof
    (T : ProbabilisticTheory.TraceClass H)
    (h₁ h₂ : HasFinitePresentation T) (z : ℂ) :
    detFinite T h₁ z = detFinite T h₂ z := by
  let p : Presentation T := Classical.choice h₂
  rw [detFinite_eq_of_presentation T h₁ p z]

#print axioms Manuscript14Priority3.FiniteNuclearFredholm.detFinite_eq_of_presentation
#print axioms Manuscript14Priority3.FiniteNuclearFredholm.detFinite_finiteNuclear
#print axioms Manuscript14Priority3.FiniteNuclearFredholm.detFinite_tendsto_compressions
#print axioms Manuscript14Priority3.FiniteNuclearFredholm.detFinite_zero
#print axioms Manuscript14Priority3.FiniteNuclearFredholm.detFinite_continuous_z
#print axioms Manuscript14Priority3.FiniteNuclearFredholm.detFinite_independent_of_proof

end Manuscript14Priority3.FiniteNuclearFredholm
