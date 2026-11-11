import SpecialImaginaryPoint.V14119Priority3IntrinsicFiniteS1MultitermBound
import SpecialImaginaryPoint.V14119Priority3FiniteNuclearConcatenation
import SpecialImaginaryPoint.V14119Priority3FinAppendTailIndex

/-!
# Priority 3 — actual intrinsic finite Fredholm perturbation, two arbitrary nuclear families

The two families may have different finite lengths and represent
arbitrary nonnormal CFC Schatten-S₁ operators T and R. Concatenate
their genuine rank-one presentations; delete exactly the R indices.

Then, for arbitrary complex z,

  |det_fin(I+z(T+R)) - det_fin(I+zT)|
    ≤ |z| mass(R) exp(|z|(mass(T)+mass(R))).

The determinant is the previously kernel-certified genuine intrinsic
finite-nuclear Fredholm functional, independent of its presentation.
No matrix dimension, invertibility, selfadjointness, or positivity
appears.

The costs mass(T),mass(R) refer to the chosen FINITE presentations:
this is NOT yet the optimal perturbation bound involving the true
‖R‖₁. The remaining task is to optimize finite nuclear presentations
or provide an equivalent full S₁-limit construction.
-/

noncomputable section
namespace Manuscript14Priority3.FiniteTwoFamilyDet

open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.FiniteNuclearFredholm
open Manuscript14Priority3.FiniteNuclearConcatenation
open Manuscript14Priority3.FinAppendTailIndex
open Manuscript14Priority3.MultiIndexGramPerturb
open Manuscript14Priority3.IntrinsicFiniteS1MultitermBound

/-- An actual finite nuclear presentation of T+R built from arbitrary
finite-rank presentations of T and R. -/
def sumPresentation (m n : ℕ)
    (u v : Fin m → H) (a b : Fin n → H) :
    Presentation (finiteNuclear m u v + finiteNuclear n a b) where
  length := m + n
  leftVectors := Fin.append u a
  rightVectors := Fin.append v b
  represents := finiteNuclear_append_eq_add m n u v a b

/-- An alternative true presentation of T, obtained by inserting
n zeroed rank-one terms in the second block. -/
def zeroJoinedPresentation (m n : ℕ)
    (u v : Fin m → H) (b : Fin n → H) :
    Presentation (finiteNuclear m u v) where
  length := m + n
  leftVectors := Fin.append u (fun _ => 0)
  rightVectors := Fin.append v b
  represents := finiteNuclear_append_zero_right m n u v b

/-- First compare the two genuine intrinsic Fredholm determinants
of the concatenated finite CFC-S₁ nuclear presentations. -/
theorem detFinite_joined_zeroed_tail_norm_le_exp (m n : ℕ)
    (u v : Fin m → H) (a b : Fin n → H) (z : ℂ) :
    ‖detFinite
        (finiteNuclear (m + n) (Fin.append u a) (Fin.append v b))
        ⟨canonicalPresentation (m + n) (Fin.append u a) (Fin.append v b)⟩ z -
      detFinite
        (finiteNuclear (m + n) (Fin.append u (fun _ => 0)) (Fin.append v b))
        ⟨canonicalPresentation (m + n)
          (Fin.append u (fun _ => 0)) (Fin.append v b)⟩ z‖ ≤
      (‖z‖ * (∑ j : Fin n, ‖a j‖ * ‖b j‖)) *
        Real.exp (‖z‖ * ((∑ i : Fin m, ‖u i‖ * ‖v i‖) +
          (∑ j : Fin n, ‖a j‖ * ‖b j‖))) := by
  have hzero :
      zeroOut (Fin.append u a) (tailSet m n) =
        Fin.append u (fun _ : Fin n => 0) := by
    change zeroTail m n (Fin.append u a) = _
    exact zeroTail_append m n u a
  have h :=
    detFinite_zeroOut_nuclear_cost_norm_le_exp
      (Fin.append u a) (Fin.append v b) z (tailSet m n)
  rw [hzero] at h
  have htail :
      (∑ i ∈ tailSet m n,
        ‖z‖ * (‖Fin.append u a i‖ * ‖Fin.append v b i‖)) =
      ‖z‖ * (∑ j : Fin n, ‖a j‖ * ‖b j‖) := by
    rw [← Finset.mul_sum]
    exact congrArg (fun x : ℝ => ‖z‖ * x)
      (nuclear_cost_tailSet m n u v a b)
  have htotal :
      (∑ i : Fin (m + n),
        ‖z‖ * (‖Fin.append u a i‖ * ‖Fin.append v b i‖)) =
      ‖z‖ * ((∑ i : Fin m, ‖u i‖ * ‖v i‖) +
        (∑ j : Fin n, ‖a j‖ * ‖b j‖)) := by
    rw [← Finset.mul_sum]
    exact congrArg (fun x : ℝ => ‖z‖ * x)
      (nuclear_mass_append_eq_add m n u v a b)
  rw [htail, htotal] at h
  exact h

/-- GENERAL FINITE NUCLEAR TWO-OPERATOR PERTURBATION:
the actual presentation-independent CFC S₁ Fredholm determinant
of T+R versus that of T, with arbitrary different presentation
lengths and no dimension-dependent factor. -/
theorem detFinite_add_nuclear_cost_norm_le_exp (m n : ℕ)
    (u v : Fin m → H) (a b : Fin n → H) (z : ℂ) :
    ‖detFinite
        (finiteNuclear m u v + finiteNuclear n a b)
        ⟨sumPresentation m n u v a b⟩ z -
      detFinite (finiteNuclear m u v)
        ⟨canonicalPresentation m u v⟩ z‖ ≤
      (‖z‖ * (∑ j : Fin n, ‖a j‖ * ‖b j‖)) *
        Real.exp (‖z‖ * ((∑ i : Fin m, ‖u i‖ * ‖v i‖) +
          (∑ j : Fin n, ‖a j‖ * ‖b j‖))) := by
  have hleft :
      detFinite
        (finiteNuclear m u v + finiteNuclear n a b)
        ⟨sumPresentation m n u v a b⟩ z =
      detFinite
        (finiteNuclear (m + n) (Fin.append u a) (Fin.append v b))
        ⟨canonicalPresentation (m + n) (Fin.append u a) (Fin.append v b)⟩ z := by
    rw [detFinite_eq_of_presentation
        (finiteNuclear m u v + finiteNuclear n a b)
        ⟨sumPresentation m n u v a b⟩
        (sumPresentation m n u v a b) z]
    rw [detFinite_finiteNuclear]
    rfl
  have hright :
      detFinite (finiteNuclear m u v)
        ⟨canonicalPresentation m u v⟩ z =
      detFinite
        (finiteNuclear (m + n) (Fin.append u (fun _ => 0)) (Fin.append v b))
        ⟨canonicalPresentation (m + n)
          (Fin.append u (fun _ => 0)) (Fin.append v b)⟩ z := by
    rw [detFinite_eq_of_presentation
        (finiteNuclear m u v)
        ⟨canonicalPresentation m u v⟩
        (zeroJoinedPresentation m n u v b) z]
    rw [detFinite_finiteNuclear]
    rfl
  rw [hleft, hright]
  exact detFinite_joined_zeroed_tail_norm_le_exp m n u v a b z

#print axioms Manuscript14Priority3.FiniteTwoFamilyDet.detFinite_joined_zeroed_tail_norm_le_exp
#print axioms Manuscript14Priority3.FiniteTwoFamilyDet.detFinite_add_nuclear_cost_norm_le_exp

end Manuscript14Priority3.FiniteTwoFamilyDet
