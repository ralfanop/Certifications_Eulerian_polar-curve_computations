import SpecialImaginaryPoint.V14119Priority3ArbitraryNuclearRankOne
import SpecialImaginaryPoint.V14119Priority3FiniteRankFredholm
import Mathlib.Topology.Instances.Matrix

/-!
# Manuscript 14.119 Priority 3 — intrinsic finite nuclear Fredholm determinant

For a completely ARBITRARY finite family of complex Hilbert rank-one
operators T = Σ |uᵢ⟩⟨vᵢ|, construct its actual genuine CFC-S₁ element.
The concrete N-dimensional Hilbert compression of T is the matrix
product A_N B_N, with A_N and B_N rectangular matrices of the
genuine inner products. The already certified Weinstein–Aronszajn
identity then gives the exact finite determinant identity

  det(I_N + z compress_N(T)) = det(I_m + z B_N A_N).

Hilbert-basis Parseval gives B_N A_N → G, where
  G_{ij} = inner(v_i,u_j).
Continuity of finite matrix determinants proves

  lim_{N→∞} det(I_N+z compress_N(T)) = det(I_m+z G).

The last theorem establishes INTRINSIC independence of the chosen
FINITE nuclear rank-one factorization: if two finite rank-one
presentations define the same actual CFC S₁ operator, their
finite Gram Fredholm determinants coincide, EVEN IF the two
nuclear presentation lengths differ.

This result does not assume positivity, normality or diagonality.
It does not assert uniform-in-N perturbation bounds, nor
the extension to the ENTIRE S₁ ideal by continuity.
-/

noncomputable section

namespace Manuscript14Priority3.FiniteNuclearFredholm

open Filter Topology InnerProductSpace
open scoped ComplexOrder lp
open Manuscript14Priority3.TraceClassModel

/-- A genuine CFC Schatten-S₁ operator consisting of an arbitrary
finite complex family of rank-one Hilbert operators. -/
def finiteNuclear (m : ℕ) (u v : Fin m → H) :
    ProbabilisticTheory.TraceClass H :=
  ∑ k : Fin m, Manuscript14Priority3.NuclearRankOne.rankOneS1 (u k) (v k)

/-- Every finite nuclear S₁ sum is the ACTUAL finite sum of bounded
Hilbert rank-one endomorphisms. -/
theorem finiteNuclear_operator (m : ℕ) (u v : Fin m → H) :
    (finiteNuclear m u v).1 =
      ∑ k : Fin m, (rankOne ℂ (u k) (v k) : H →L[ℂ] H) := by
  let t : Finset (Fin m) := Finset.univ
  have hs (s : Finset (Fin m)) :
      ((∑ k ∈ s,
          Manuscript14Priority3.NuclearRankOne.rankOneS1 (u k) (v k)) :
            ProbabilisticTheory.TraceClass H).1 =
        ∑ k ∈ s, (rankOne ℂ (u k) (v k) : H →L[ℂ] H) := by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | @insert k s hk ih =>
        simp only [Finset.sum_insert hk,
          ProbabilisticTheory.TraceClass.add_operator, ih]
        rw [Manuscript14Priority3.NuclearRankOne.rankOneS1_operator]
  simpa only [finiteNuclear] using hs Finset.univ

/-- Coordinates of the finite family of image vectors in the
genuine ambient ℓ² Hilbert basis. -/
def leftMatrix (N m : ℕ) (u : Fin m → H) :
    Matrix (Fin N) (Fin m) ℂ :=
  fun i k => inner ℂ (b i.val) (u k)

/-- Dual finite rank-one family coordinates. -/
def rightMatrix (N m : ℕ) (v : Fin m → H) :
    Matrix (Fin m) (Fin N) ℂ :=
  fun k j => inner ℂ (v k) (b j.val)

/-- The intrinsic m×m Gram pairing of the finite nuclear presentation,
with NO reference to the ambient chosen Hilbert basis. -/
def gram (m : ℕ) (u v : Fin m → H) :
    Matrix (Fin m) (Fin m) ℂ :=
  fun i j => inner ℂ (v i) (u j)

/-- Genuine N-dimensional compression of a finite nonnormal,
nonselfadjoint CFC trace-class operator factors as A_N B_N. -/
theorem compressed_finiteNuclear_factor (N m : ℕ) (u v : Fin m → H) :
    Manuscript14Priority3.FiniteRankFredholm.compressedCFC N
      (finiteNuclear m u v) = leftMatrix N m u * rightMatrix N m v := by
  ext i j
  have hop : (finiteNuclear m u v).1 =
      ∑ k : Fin m, (rankOne ℂ (u k) (v k) : H →L[ℂ] H) :=
    finiteNuclear_operator m u v
  have happly :
      ((∑ k : Fin m, (rankOne ℂ (u k) (v k) : H →L[ℂ] H)) (b j.val)) =
      ∑ k : Fin m, (rankOne ℂ (u k) (v k)) (b j.val) := by
    change (ContinuousLinearMap.apply ℂ H (b j.val))
      (∑ k : Fin m, (rankOne ℂ (u k) (v k) : H →L[ℂ] H)) = _
    exact map_sum _ _ _
  have hinner :
      inner ℂ (b i.val)
        (∑ k : Fin m, (rankOne ℂ (u k) (v k)) (b j.val)) =
      ∑ k : Fin m, inner ℂ (b i.val)
        ((rankOne ℂ (u k) (v k)) (b j.val)) := by
    change (innerSL ℂ (b i.val))
      (∑ k : Fin m, (rankOne ℂ (u k) (v k)) (b j.val)) = _
    exact map_sum _ _ _
  change inner ℂ (b i.val) ((finiteNuclear m u v).1 (b j.val)) =
    ∑ k : Fin m, inner ℂ (b i.val) (u k) *
      inner ℂ (v k) (b j.val)
  rw [hop, happly, hinner]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [rankOne_apply, inner_smul_right]

/-- Exact determinant identity between the actual N-dimensional
Hilbert compression and the m-dimensional truncated Gram pairing. -/
theorem finiteNuclear_det_eq_truncatedGram (N m : ℕ)
    (u v : Fin m → H) (z : ℂ) :
    Manuscript14Priority3.FiniteRankFredholm.finiteDeterminant N
      (finiteNuclear m u v) z =
    Matrix.det (1 + z •
      (rightMatrix N m v * leftMatrix N m u)) := by
  change Matrix.det
      (1 + z • Manuscript14Priority3.FiniteRankFredholm.compressedCFC N
        (finiteNuclear m u v)) = _
  rw [compressed_finiteNuclear_factor]
  exact Manuscript14Priority3.FiniteRankFredholm.determinant_rectangular_comm
    (leftMatrix N m u) (rightMatrix N m v) z

/-- Each entry of the truncated nuclear Gram matrix converges
by the ACTUAL complete Hilbert-basis Parseval identity. -/
theorem truncatedGram_entry_tendsto (m : ℕ) (u v : Fin m → H)
    (i j : Fin m) :
    Tendsto
      (fun N : ℕ => (rightMatrix N m v * leftMatrix N m u) i j)
      atTop (𝓝 (gram m u v i j)) := by
  have hseries :=
    (b.hasSum_inner_mul_inner (v i) (u j)).tendsto_sum_nat
  simpa only [Matrix.mul_apply, rightMatrix, leftMatrix, gram,
    Finset.sum_fin_eq_sum_range] using hseries

/-- Matrix-level convergence of actual truncated complex Gram
pairings to the intrinsic finite nuclear Gram matrix. -/
theorem truncatedGram_tendsto (m : ℕ) (u v : Fin m → H) :
    Tendsto
      (fun N : ℕ => rightMatrix N m v * leftMatrix N m u)
      atTop (𝓝 (gram m u v)) := by
  rw [tendsto_pi_nhds]
  intro i
  rw [tendsto_pi_nhds]
  intro j
  exact truncatedGram_entry_tendsto m u v i j

/-- For EVERY finite nuclear rank-one CFC S₁ operator and arbitrary
complex z, determinants of its genuine N-dimensional Hilbert
compressions converge to the finite Gram determinant. -/
theorem finiteNuclear_det_tendsto (m : ℕ) (u v : Fin m → H) (z : ℂ) :
    Tendsto
      (fun N : ℕ =>
        Manuscript14Priority3.FiniteRankFredholm.finiteDeterminant N
          (finiteNuclear m u v) z)
      atTop (𝓝 (Matrix.det (1 + z • gram m u v))) := by
  have hmat :
      Tendsto (fun N : ℕ =>
        (1 : Matrix (Fin m) (Fin m) ℂ) +
          z • (rightMatrix N m v * leftMatrix N m u))
        atTop (𝓝 (1 + z • gram m u v)) :=
    tendsto_const_nhds.add
      (tendsto_const_nhds.smul (truncatedGram_tendsto m u v))
  have hdet :
      Continuous
        (fun M : Matrix (Fin m) (Fin m) ℂ => Matrix.det M) :=
    continuous_id.matrix_det
  have hlim := (hdet.tendsto (1 + z • gram m u v)).comp hmat
  simpa only [finiteNuclear_det_eq_truncatedGram] using hlim

/-- The finite Gram Fredholm determinant is independent of ANY
two finite rank-one Hilbert presentations of THE SAME genuine
CFC Schatten-S₁ operator, including different presentation lengths.
This is an intrinsic finite-rank determinant result. -/
theorem finiteNuclear_det_representation_independent
    (m p : ℕ) (u v : Fin m → H) (u' v' : Fin p → H)
    (h : finiteNuclear m u v = finiteNuclear p u' v')
    (z : ℂ) :
    Matrix.det (1 + z • gram m u v) =
      Matrix.det (1 + z • gram p u' v') := by
  have hleft := finiteNuclear_det_tendsto m u v z
  have hright := finiteNuclear_det_tendsto p u' v' z
  have heq :
      (fun N : ℕ =>
        Manuscript14Priority3.FiniteRankFredholm.finiteDeterminant N
          (finiteNuclear m u v) z) =
      (fun N : ℕ =>
        Manuscript14Priority3.FiniteRankFredholm.finiteDeterminant N
          (finiteNuclear p u' v') z) := by
    funext N
    rw [h]
  rw [heq] at hleft
  exact tendsto_nhds_unique hleft hright

#print axioms Manuscript14Priority3.FiniteNuclearFredholm.finiteNuclear_operator
#print axioms Manuscript14Priority3.FiniteNuclearFredholm.compressed_finiteNuclear_factor
#print axioms Manuscript14Priority3.FiniteNuclearFredholm.finiteNuclear_det_eq_truncatedGram
#print axioms Manuscript14Priority3.FiniteNuclearFredholm.truncatedGram_entry_tendsto
#print axioms Manuscript14Priority3.FiniteNuclearFredholm.truncatedGram_tendsto
#print axioms Manuscript14Priority3.FiniteNuclearFredholm.finiteNuclear_det_tendsto
#print axioms Manuscript14Priority3.FiniteNuclearFredholm.finiteNuclear_det_representation_independent

end Manuscript14Priority3.FiniteNuclearFredholm
