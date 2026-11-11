import SpecialImaginaryPoint.V14119Priority3TrueFiniteCompressionGram
import SpecialImaginaryPoint.V14119Priority3FiniteTwoFamilyDet

/-!
# Priority 3 — finite Hilbert compression Fredholm determinant perturbation

The previous sharp arbitrary mixed-Gram determinant theorem, together
with Bessel's inequality for genuine Hilbert compression coordinates,
gives a perturbation estimate for the *actual* N-dimensional
Hilbert-compression determinants of any TWO finite-nuclear CFC-S₁
operators T and R, without constants depending on N.

  |D_N(T+R,z)-D_N(T,z)|
     ≤ |z| mass(R) exp(|z|(mass(T)+mass(R))).

These are chosen finite nuclear PRESENTATION masses, not yet the true
trace norm. The subsequent step can use the *already-certified
optimal infinite nuclear expansions* of arbitrary S₁ operators:
finite truncations have total mass ≤ ‖T‖₁, and for each FIXED N the
compression determinant is continuous. Passing to those truncation
limits will yield the genuine trace-norm perturbation bound for
D_N with a constant UNIFORM in N, without needing finite exact
optimal nuclear representations.
-/

noncomputable section
namespace Manuscript14Priority3.FiniteCompressionTwoFamilyBound

open Matrix InnerProductSpace
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.FiniteRankFredholm
open Manuscript14Priority3.FiniteNuclearFredholm
open Manuscript14Priority3.FiniteNuclearConcatenation
open Manuscript14Priority3.FinAppendTailIndex
open Manuscript14Priority3.MultiIndexGramPerturb
open Manuscript14Priority3.CompressedEuclideanCoordinates
open Manuscript14Priority3.TrueFiniteCompressionGram

/-- Nuclear costs of ANY finite index subset decrease under
Hilbert coordinate compression, not just full-universe sums. -/
theorem coordinate_nuclear_mass_subsum_le
    (N m : ℕ) (u v : Fin m → H) (s : Finset (Fin m)) :
    (∑ i ∈ s,
      ‖coefficients b N (u i)‖ *
        ‖coefficients b N (v i)‖) ≤
      ∑ i ∈ s, ‖u i‖ * ‖v i‖ := by
  apply Finset.sum_le_sum
  intro i hi
  calc
    ‖coefficients b N (u i)‖ *
        ‖coefficients b N (v i)‖ ≤
      ‖u i‖ * ‖coefficients b N (v i)‖ :=
        mul_le_mul_of_nonneg_right
          (coefficients_norm_le b b.orthonormal N (u i))
          (norm_nonneg _)
    _ ≤ ‖u i‖ * ‖v i‖ :=
      mul_le_mul_of_nonneg_left
        (coefficients_norm_le b b.orthonormal N (v i))
        (norm_nonneg _)

/-- Zeroing a subset of Hilbert nuclear vectors commutes
exactly with taking finite Euclidean coordinate vectors. -/
theorem coordinate_zeroOut
    (N m : ℕ) (u : Fin m → H) (s : Finset (Fin m)) :
    zeroOut (fun i : Fin m => coefficients b N (u i)) s =
      (fun i => coefficients b N (zeroOut u s i)) := by
  funext i
  by_cases hi : i ∈ s
  · simp [zeroOut, hi, coefficients_zero]
  · simp [zeroOut, hi]

/-- Uniform-in-N, dimension-free nuclear-cost perturbation bound
for TRUE finite Hilbert compression determinants, before rewriting
the joined finite operator as T+R. -/
theorem finiteDeterminant_joined_zeroOut_norm_le_exp
    (N m n : ℕ) (u v : Fin m → H) (a d : Fin n → H) (z : ℂ) :
    ‖finiteDeterminant N
        (finiteNuclear (m + n) (Fin.append u a) (Fin.append v d)) z -
      finiteDeterminant N
        (finiteNuclear (m + n)
          (zeroOut (Fin.append u a) (tailSet m n))
          (Fin.append v d)) z‖ ≤
      (‖z‖ * (∑ j : Fin n, ‖a j‖ * ‖d j‖)) *
        Real.exp (‖z‖ *
          ((∑ i : Fin m, ‖u i‖ * ‖v i‖) +
            (∑ j : Fin n, ‖a j‖ * ‖d j‖))) := by
  let uu : Fin (m + n) → H := Fin.append u a
  let vv : Fin (m + n) → H := Fin.append v d
  let ss : Finset (Fin (m + n)) := tailSet m n
  have hzero :
      zeroOut (fun i => coefficients b N (uu i)) ss =
        (fun i => coefficients b N (zeroOut uu ss i)) :=
    coordinate_zeroOut N (m + n) uu ss
  have h :=
    det_sub_det_zeroOut_norm_le_exp
      (fun i => coefficients b N (uu i))
      (fun i => coefficients b N (vv i)) z ss
  rw [hzero] at h
  have hcostTail :
      (∑ i ∈ ss,
        ‖z‖ * (‖coefficients b N (uu i)‖ *
          ‖coefficients b N (vv i)‖)) ≤
      ‖z‖ * (∑ j : Fin n, ‖a j‖ * ‖d j‖) := by
    calc
      (∑ i ∈ ss,
        ‖z‖ * (‖coefficients b N (uu i)‖ *
          ‖coefficients b N (vv i)‖)) =
          ‖z‖ * (∑ i ∈ ss,
            ‖coefficients b N (uu i)‖ *
              ‖coefficients b N (vv i)‖) := by rw [Finset.mul_sum]
      _ ≤ ‖z‖ * (∑ i ∈ ss, ‖uu i‖ * ‖vv i‖) :=
        mul_le_mul_of_nonneg_left
          (coordinate_nuclear_mass_subsum_le N (m + n) uu vv ss)
          (norm_nonneg z)
      _ = ‖z‖ * (∑ j : Fin n, ‖a j‖ * ‖d j‖) := by
        dsimp [ss, uu, vv]
        rw [nuclear_cost_tailSet m n u v a d]
  have hcostTotal :
      (∑ i : Fin (m + n),
        ‖z‖ * (‖coefficients b N (uu i)‖ *
          ‖coefficients b N (vv i)‖)) ≤
      ‖z‖ *
        ((∑ i : Fin m, ‖u i‖ * ‖v i‖) +
          (∑ j : Fin n, ‖a j‖ * ‖d j‖)) := by
    calc
      (∑ i : Fin (m + n),
        ‖z‖ * (‖coefficients b N (uu i)‖ *
          ‖coefficients b N (vv i)‖)) =
          ‖z‖ * (∑ i : Fin (m + n),
            ‖coefficients b N (uu i)‖ *
              ‖coefficients b N (vv i)‖) := by rw [Finset.mul_sum]
      _ ≤ ‖z‖ * (∑ i : Fin (m + n), ‖uu i‖ * ‖vv i‖) :=
        mul_le_mul_of_nonneg_left
          (coordinate_nuclear_mass_le N (m + n) uu vv)
          (norm_nonneg z)
      _ = ‖z‖ *
        ((∑ i : Fin m, ‖u i‖ * ‖v i‖) +
          (∑ j : Fin n, ‖a j‖ * ‖d j‖)) := by
        dsimp [uu, vv]
        rw [nuclear_mass_append_eq_add m n u v a d]
  have hrNonneg :
      0 ≤ ‖z‖ * (∑ j : Fin n, ‖a j‖ * ‖d j‖) := by positivity
  change
      ‖finiteDeterminant N (finiteNuclear (m + n) uu vv) z -
        finiteDeterminant N (finiteNuclear (m + n) (zeroOut uu ss) vv) z‖ ≤ _
  rw [finiteDeterminant_eq_coordinate_mixedGram N (m + n) uu vv z,
    finiteDeterminant_eq_coordinate_mixedGram N (m + n) (zeroOut uu ss) vv z]
  calc
    ‖(1 + z • Manuscript14Priority3.ComplexGramMinorBridge.mixedGram
        (fun i => coefficients b N (uu i))
        (fun i => coefficients b N (vv i))).det -
      (1 + z • Manuscript14Priority3.ComplexGramMinorBridge.mixedGram
        (fun i => coefficients b N (zeroOut uu ss i))
        (fun i => coefficients b N (vv i))).det‖ ≤
        (∑ i ∈ ss,
          ‖z‖ * (‖coefficients b N (uu i)‖ *
            ‖coefficients b N (vv i)‖)) *
          Real.exp (∑ i : Fin (m + n),
            ‖z‖ * (‖coefficients b N (uu i)‖ *
              ‖coefficients b N (vv i)‖)) := h
    _ ≤ (‖z‖ * (∑ j : Fin n, ‖a j‖ * ‖d j‖)) *
          Real.exp (∑ i : Fin (m + n),
            ‖z‖ * (‖coefficients b N (uu i)‖ *
              ‖coefficients b N (vv i)‖)) :=
      mul_le_mul_of_nonneg_right hcostTail (Real.exp_pos _).le
    _ ≤ (‖z‖ * (∑ j : Fin n, ‖a j‖ * ‖d j‖)) *
          Real.exp (‖z‖ *
            ((∑ i : Fin m, ‖u i‖ * ‖v i‖) +
              (∑ j : Fin n, ‖a j‖ * ‖d j‖))) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hcostTotal) hrNonneg

/-- The exact finite compression perturbation inequality for arbitrary
T and R with separately given finite nuclear presentations.
ALL constants are independent of compression dimension N. -/
theorem finiteDeterminant_two_family_norm_le_exp
    (N m n : ℕ) (u v : Fin m → H) (a d : Fin n → H) (z : ℂ) :
    ‖finiteDeterminant N
        (finiteNuclear m u v + finiteNuclear n a d) z -
      finiteDeterminant N (finiteNuclear m u v) z‖ ≤
      (‖z‖ * (∑ j : Fin n, ‖a j‖ * ‖d j‖)) *
        Real.exp (‖z‖ *
          ((∑ i : Fin m, ‖u i‖ * ‖v i‖) +
            (∑ j : Fin n, ‖a j‖ * ‖d j‖))) := by
  have h :=
    finiteDeterminant_joined_zeroOut_norm_le_exp N m n u v a d z
  have hzero :
      zeroOut (Fin.append u a) (tailSet m n) =
        Fin.append u (fun _ : Fin n => 0) := by
    change zeroTail m n (Fin.append u a) = _
    exact zeroTail_append m n u a
  rw [hzero,
    finiteNuclear_append_eq_add m n u v a d,
    finiteNuclear_append_zero_right m n u v d] at h
  exact h

#print axioms Manuscript14Priority3.FiniteCompressionTwoFamilyBound.coordinate_nuclear_mass_subsum_le
#print axioms Manuscript14Priority3.FiniteCompressionTwoFamilyBound.coordinate_zeroOut
#print axioms Manuscript14Priority3.FiniteCompressionTwoFamilyBound.finiteDeterminant_joined_zeroOut_norm_le_exp
#print axioms Manuscript14Priority3.FiniteCompressionTwoFamilyBound.finiteDeterminant_two_family_norm_le_exp

end Manuscript14Priority3.FiniteCompressionTwoFamilyBound
