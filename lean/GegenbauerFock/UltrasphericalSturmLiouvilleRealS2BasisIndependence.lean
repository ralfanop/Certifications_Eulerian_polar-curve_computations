import GegenbauerFock.UltrasphericalSturmLiouvilleResolventRealSchattenBasis
import GegenbauerFock.UltrasphericalSturmLiouvilleRealFullResolventSelfAdjoint
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# V007 — genuine real Hilbert-Schmidt basis independence for self-adjoint operators

For any self-adjoint bounded operator on a complete REAL Hilbert space,
the sum of squared norms of its images over a complete Hilbert basis is
the same for every other complete Hilbert basis, including differently
indexed Hilbert bases. The proof uses real Parseval, the self-adjoint
symmetry of the operator, nonnegative double-sum summability and a
Tonelli/Fubini interchange. No spectral theorem or finite-dimensional
trace surrogate is assumed.

This yields a new intrinsic real-S₂ assertion for the ACTUAL canonical
closed Gegenbauer Sturm resolvent on its genuine weighted L² space:
every complete real Hilbert basis yields precisely the square of the
resolvent's canonical Hilbert-Schmidt norm.

No identification with complex Physlib S₂ is asserted.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Real Parseval's identity for the squared coefficients of a vector
in an arbitrary complete real Hilbert basis. -/
theorem realHilbertBasis_hasSum_inner_sq
    {ι : Type*} (b : HilbertBasis ι ℝ H) (y : H) :
    HasSum (fun i : ι => (inner ℝ (b i) y) ^ 2) (‖y‖ ^ 2) := by
  have h := b.hasSum_inner_mul_inner y y
  have heq :
      (fun i : ι => inner ℝ y (b i) * inner ℝ (b i) y) =
      (fun i : ι => (inner ℝ (b i) y) ^ 2) := by
    funext i
    rw [real_inner_comm y (b i)]
    ring
  rw [heq, real_inner_self_eq_norm_sq] at h
  exact h

/-- The real squared Hilbert-Schmidt mass of an actual bounded
SELF-ADJOINT operator is independent of the complete Hilbert basis.
Index types are arbitrary and need not coincide. -/
theorem realHilbertSelfAdjoint_hsMass_hasSum_any_basis
    (S : H →L[ℝ] H) (hS : IsSelfAdjoint S)
    {ι κ : Type*}
    (b : HilbertBasis ι ℝ H) (c : HilbertBasis κ ℝ H)
    (hb : Summable (fun i : ι => ‖S (b i)‖ ^ 2)) :
    HasSum (fun j : κ => ‖S (c j)‖ ^ 2)
      (∑' i : ι, ‖S (b i)‖ ^ 2) := by
  classical
  let F : ι → κ → ℝ := fun i j => (inner ℝ (c j) (S (b i))) ^ 2
  have hFnonneg : 0 ≤ Function.uncurry F := fun _ => sq_nonneg _
  have hrow : ∀ i : ι, HasSum (F i) (‖S (b i)‖ ^ 2) := fun i =>
    realHilbertBasis_hasSum_inner_sq c (S (b i))
  have hsym : ∀ x y : H,
      inner ℝ (S x) y = inner ℝ x (S y) :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hS
  have hcol : ∀ j : κ,
      HasSum (fun i : ι => F i j) (‖S (c j)‖ ^ 2) := by
    intro j
    have key : (fun i : ι => F i j) =
        (fun i : ι => (inner ℝ (b i) (S (c j))) ^ 2) := by
      funext i
      change (inner ℝ (c j) (S (b i))) ^ 2 = _
      congr 1
      calc
        inner ℝ (c j) (S (b i)) =
          inner ℝ (S (b i)) (c j) := real_inner_comm _ _
        _ = inner ℝ (b i) (S (c j)) := hsym (b i) (c j)
    rw [key]
    exact realHilbertBasis_hasSum_inner_sq b (S (c j))
  let G : κ → ι → ℝ := fun j i => F i j
  have hjoint : Summable (Function.uncurry F) := by
    rw [summable_prod_of_nonneg hFnonneg]
    refine ⟨fun i => (hrow i).summable, ?_⟩
    have heq : (fun i : ι => ∑' j : κ, F i j) =
        (fun i : ι => ‖S (b i)‖ ^ 2) :=
      funext fun i => (hrow i).tsum_eq
    show Summable (fun i : ι => ∑' j : κ, F i j)
    rwa [heq]
  have hswap := hjoint.tsum_comm'
    (fun i => (hrow i).summable)
    (fun j => (hcol j).summable)
  have hLHS :
      (∑' j : κ, ∑' i : ι, F i j) =
      (∑' j : κ, ‖S (c j)‖ ^ 2) :=
    tsum_congr fun j => (hcol j).tsum_eq
  have hRHS :
      (∑' i : ι, ∑' j : κ, F i j) =
      (∑' i : ι, ‖S (b i)‖ ^ 2) :=
    tsum_congr fun i => (hrow i).tsum_eq
  have hEq :
      (∑' j : κ, ‖S (c j)‖ ^ 2) =
      (∑' i : ι, ‖S (b i)‖ ^ 2) := by
    rw [← hLHS, ← hRHS]
    exact hswap
  have hGnonneg : 0 ≤ Function.uncurry G := fun _ => sq_nonneg _
  have hjointG : Summable (Function.uncurry G) := by
    have hcomp :
        Function.uncurry G =
        Function.uncurry F ∘ (Equiv.prodComm κ ι) := by
      funext p
      simp [Function.uncurry, G, Equiv.prodComm]
    rw [hcomp]
    exact (Equiv.prodComm κ ι).summable_iff.mpr hjoint
  have hc : Summable (fun j : κ => ‖S (c j)‖ ^ 2) := by
    have hpair := (summable_prod_of_nonneg hGnonneg).mp hjointG
    have hs : Summable (fun j : κ => ∑' i : ι, G j i) := by
      show Summable (fun j : κ => ∑' i : ι, Function.uncurry G (j, i))
      exact hpair.2
    have heq : (fun j : κ => ∑' i : ι, G j i) =
        (fun j : κ => ‖S (c j)‖ ^ 2) :=
      funext fun j => (hcol j).tsum_eq
    rwa [heq] at hs
  rw [← hEq]
  exact hc.hasSum

/-- The actual weighted real Sturm resolvent is Hilbert-Schmidt on
EVERY complete real Hilbert basis, with the same squared mass. -/
theorem sturmRealPositiveResolvent_hsMass_any_realHilbertBasis
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    {ι : Type*}
    (c : HilbertBasis ι ℝ (Lp ℝ 2 (measure lam))) :
    HasSum
      (fun i : ι =>
        ‖sturmRealPositiveResolventFullCLM lam t hlam ht (c i)‖ ^ 2)
      (sturmResolventSquaredSpectralTrace lam t) := by
  let b := sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam
  let R := sturmRealPositiveResolventFullCLM lam t hlam ht
  have hR : IsSelfAdjoint R :=
    sturmRealPositiveResolventFullCLM_isSelfAdjoint lam t hlam ht
  have hb : Summable (fun n : ℕ => ‖R (b n)‖ ^ 2) :=
    sturmRealPositiveResolvent_isHS_on_actual_basis lam t hlam ht
  have h := realHilbertSelfAdjoint_hsMass_hasSum_any_basis R hR b c hb
  have hmass : (∑' n : ℕ, ‖R (b n)‖ ^ 2) =
      sturmResolventSquaredSpectralTrace lam t := by
    unfold sturmResolventSquaredSpectralTrace
    exact tsum_congr (fun n =>
      sturmRealPositiveResolvent_basis_norm_sq lam t hlam ht n)
  rw [← hmass]
  exact h

/-- In particular, arbitrary complete real Hilbert bases have
summable actual resolvent-image square masses. -/
theorem sturmRealPositiveResolvent_isHS_any_realHilbertBasis
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    {ι : Type*}
    (c : HilbertBasis ι ℝ (Lp ℝ 2 (measure lam))) :
    Summable (fun i : ι =>
      ‖sturmRealPositiveResolventFullCLM lam t hlam ht (c i)‖ ^ 2) :=
  (sturmRealPositiveResolvent_hsMass_any_realHilbertBasis
    lam t hlam ht c).summable

#print axioms GegenbauerFock.Ultraspherical.realHilbertBasis_hasSum_inner_sq
#print axioms GegenbauerFock.Ultraspherical.realHilbertSelfAdjoint_hsMass_hasSum_any_basis
#print axioms GegenbauerFock.Ultraspherical.sturmRealPositiveResolvent_hsMass_any_realHilbertBasis
#print axioms GegenbauerFock.Ultraspherical.sturmRealPositiveResolvent_isHS_any_realHilbertBasis

end GegenbauerFock.Ultraspherical
