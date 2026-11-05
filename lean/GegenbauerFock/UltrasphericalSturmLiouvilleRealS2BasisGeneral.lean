import GegenbauerFock.UltrasphericalSturmLiouvilleRealS2BasisIndependence

/-!
# V007 — general real Hilbert-Schmidt S2 basis independence, no symmetry assumption

The exact S2 squared mass of an ARBITRARY bounded endomorphism of a
complete real Hilbert space is independent of its complete orthonormal
input basis. This is stronger than the self-adjoint result in the
preceding module.

The two-stage argument uses actual adjoints: a nonnegative matrix
F(i,j)=⟪c_j,T b_i⟫² has row sum ‖T b_i‖² and column sum
‖T† c_j‖² by Parseval. Tonelli/Fubini gives equality of the two
squared masses; applying the same identity a second time to T†
returns T and changes its input Hilbert basis. No singular-value
decomposition or trace-class hypothesis is needed.

Applied to the ACTUAL real Gegenbauer Sturm resolvent, this gives
the same exact S2 spectral square trace on every complete real
Hilbert basis, even with an arbitrary index type.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Real Hilbert S₂ mass of a bounded operator on a complete basis
equals the S₂ mass of its adjoint on ANY other complete basis. -/
theorem realHilbert_hsMass_adjoint_hasSum
    (T : H →L[ℝ] H)
    {ι κ : Type*}
    (b : HilbertBasis ι ℝ H) (c : HilbertBasis κ ℝ H)
    (hb : Summable (fun i : ι => ‖T (b i)‖ ^ 2)) :
    HasSum (fun j : κ => ‖T.adjoint (c j)‖ ^ 2)
      (∑' i : ι, ‖T (b i)‖ ^ 2) := by
  classical
  let F : ι → κ → ℝ := fun i j => (inner ℝ (c j) (T (b i))) ^ 2
  have hFnonneg : 0 ≤ Function.uncurry F := fun _ => sq_nonneg _
  have hrow : ∀ i : ι, HasSum (F i) (‖T (b i)‖ ^ 2) := fun i =>
    realHilbertBasis_hasSum_inner_sq c (T (b i))
  have hcol : ∀ j : κ,
      HasSum (fun i : ι => F i j) (‖T.adjoint (c j)‖ ^ 2) := by
    intro j
    have key : (fun i : ι => F i j) =
        (fun i : ι => (inner ℝ (b i) (T.adjoint (c j))) ^ 2) := by
      funext i
      change (inner ℝ (c j) (T (b i))) ^ 2 = _
      have e1 : inner ℝ (c j) (T (b i)) =
          inner ℝ (T.adjoint (c j)) (b i) :=
        (ContinuousLinearMap.adjoint_inner_left T (b i) (c j)).symm
      rw [e1, real_inner_comm (T.adjoint (c j)) (b i)]
    rw [key]
    exact realHilbertBasis_hasSum_inner_sq b (T.adjoint (c j))
  let G : κ → ι → ℝ := fun j i => F i j
  have hjoint : Summable (Function.uncurry F) := by
    rw [summable_prod_of_nonneg hFnonneg]
    refine ⟨fun i => (hrow i).summable, ?_⟩
    have heq : (fun i : ι => ∑' j : κ, F i j) =
        (fun i : ι => ‖T (b i)‖ ^ 2) :=
      funext fun i => (hrow i).tsum_eq
    show Summable (fun i : ι => ∑' j : κ, F i j)
    rwa [heq]
  have hswap := hjoint.tsum_comm'
    (fun i => (hrow i).summable)
    (fun j => (hcol j).summable)
  have hLHS :
      (∑' j : κ, ∑' i : ι, F i j) =
      (∑' j : κ, ‖T.adjoint (c j)‖ ^ 2) :=
    tsum_congr fun j => (hcol j).tsum_eq
  have hRHS :
      (∑' i : ι, ∑' j : κ, F i j) =
      (∑' i : ι, ‖T (b i)‖ ^ 2) :=
    tsum_congr fun i => (hrow i).tsum_eq
  have hEq :
      (∑' j : κ, ‖T.adjoint (c j)‖ ^ 2) =
      (∑' i : ι, ‖T (b i)‖ ^ 2) := by
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
  have hc : Summable (fun j : κ => ‖T.adjoint (c j)‖ ^ 2) := by
    have hpair := (summable_prod_of_nonneg hGnonneg).mp hjointG
    have hs : Summable (fun j : κ => ∑' i : ι, G j i) := by
      show Summable (fun j : κ => ∑' i : ι, Function.uncurry G (j, i))
      exact hpair.2
    have heq : (fun j : κ => ∑' i : ι, G j i) =
        (fun j : κ => ‖T.adjoint (c j)‖ ^ 2) :=
      funext fun j => (hcol j).tsum_eq
    rwa [heq] at hs
  rw [← hEq]
  exact hc.hasSum

/-- Intrinsic Hilbert–Schmidt squared mass for EVERY real bounded
operator: the choice and index type of complete Hilbert basis
are immaterial, with no self-adjointness hypothesis. -/
theorem realHilbert_hsMass_hasSum_any_basis
    (T : H →L[ℝ] H)
    {ι κ : Type*}
    (b : HilbertBasis ι ℝ H) (c : HilbertBasis κ ℝ H)
    (hb : Summable (fun i : ι => ‖T (b i)‖ ^ 2)) :
    HasSum (fun j : κ => ‖T (c j)‖ ^ 2)
      (∑' i : ι, ‖T (b i)‖ ^ 2) := by
  have hAdj := realHilbert_hsMass_adjoint_hasSum T b b hb
  have hBack :=
    realHilbert_hsMass_adjoint_hasSum T.adjoint b c hAdj.summable
  have hDouble : T.adjoint.adjoint = T := by
    exact ContinuousLinearMap.adjoint_adjoint T
  rw [hDouble, hAdj.tsum_eq] at hBack
  exact hBack

/-- An intrinsic squared S₂ mass equality for the *actual* canonical
real Sturm resolvent, valid on every complete Hilbert basis. -/
theorem sturmRealClosedResolvent_hsMass_general_basis
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    {ι : Type*}
    (c : HilbertBasis ι ℝ (Lp ℝ 2 (measure lam))) :
    HasSum
      (fun i : ι =>
        ‖sturmRealPositiveResolventFullCLM lam t hlam ht (c i)‖ ^ 2)
      (sturmResolventSquaredSpectralTrace lam t) := by
  let b := sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam
  let R := sturmRealPositiveResolventFullCLM lam t hlam ht
  have hb : Summable (fun n : ℕ => ‖R (b n)‖ ^ 2) :=
    sturmRealPositiveResolvent_isHS_on_actual_basis lam t hlam ht
  have h := realHilbert_hsMass_hasSum_any_basis R b c hb
  have hmass : (∑' n : ℕ, ‖R (b n)‖ ^ 2) =
      sturmResolventSquaredSpectralTrace lam t := by
    unfold sturmResolventSquaredSpectralTrace
    exact tsum_congr (fun n =>
      sturmRealPositiveResolvent_basis_norm_sq lam t hlam ht n)
  rw [← hmass]
  exact h

#print axioms GegenbauerFock.Ultraspherical.realHilbert_hsMass_adjoint_hasSum
#print axioms GegenbauerFock.Ultraspherical.realHilbert_hsMass_hasSum_any_basis
#print axioms GegenbauerFock.Ultraspherical.sturmRealClosedResolvent_hsMass_general_basis

end GegenbauerFock.Ultraspherical
