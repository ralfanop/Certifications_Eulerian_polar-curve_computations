import GegenbauerFock.RealNuclearGramFinitePhaseIsometry
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# V007 — genuine bounded real polar phase from two orthonormal mode families

For any two real-Hilbert orthonormal families b,c indexed by a type ι,
their canonical ℓ² synthesis maps B,C are isometric embeddings.
Define W := C ∘ B†. It is a bounded real continuous linear operator
on the WHOLE Hilbert space (with no equal-defect hypothesis).

Its initial and final projections are precisely B∘B† and C∘C†,
and W(b_i)=c_i. It vanishes on the orthogonal complement of the
closed source span and is isometric on that span. In particular its
kernel can differ in dimension from the target cokernel.

When b and c are the complete positive singular mode systems of a
given actual Gram T†T, this W is the polar partial isometry. The
existence/assembly of those complete positive mode systems and the
operator-level equality T = W |T| require separate formal proofs.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]
variable {ι : Type*}

/-- The canonical real Hilbert ℓ² synthesis isometric embedding
associated with any orthonormal family, complete or incomplete. -/
noncomputable def realPhaseOrthSynthesis
    (b : ι → H) (hb : Orthonormal ℝ b) :
    lp (fun _ : ι => ℝ) 2 →ₗᵢ[ℝ] H :=
  hb.orthogonalFamily.linearIsometry

/-- A genuine bounded partial isometry of the whole real Hilbert
space, extended by zero from the closed source orthonormal span. -/
noncomputable def realPhasePartialCLM
    (b c : ι → H)
    (hb : Orthonormal ℝ b) (hc : Orthonormal ℝ c) :
    H →L[ℝ] H :=
  (realPhaseOrthSynthesis c hc).toContinuousLinearMap ∘L
    (realPhaseOrthSynthesis b hb).toContinuousLinearMap.adjoint

/-- A canonical synthesis map takes a single coefficient-basis mode
to the supplied orthonormal Hilbert vector. -/
theorem realPhaseOrthSynthesis_single
    [DecidableEq ι] (b : ι → H) (hb : Orthonormal ℝ b) (i : ι) :
    realPhaseOrthSynthesis b hb (lp.single 2 i (1 : ℝ)) = b i := by
  classical
  change hb.orthogonalFamily.linearIsometry (lp.single 2 i 1) = b i
  rw [OrthogonalFamily.linearIsometry_apply_single,
    LinearIsometry.toSpanSingleton_apply, one_smul]

/-- This entire-space bounded real partial phase agrees with the
singular vector transfer on every source mode. -/
theorem realPhasePartialCLM_on_source_mode
    (b c : ι → H) (hb : Orthonormal ℝ b)
    (hc : Orthonormal ℝ c) (i : ι) :
    realPhasePartialCLM b c hb hc (b i) = c i := by
  classical
  let B : lp (fun _ : ι => ℝ) 2 →L[ℝ] H :=
    (realPhaseOrthSynthesis b hb).toContinuousLinearMap
  let C : lp (fun _ : ι => ℝ) 2 →L[ℝ] H :=
    (realPhaseOrthSynthesis c hc).toContinuousLinearMap
  have hBB : B.adjoint ∘L B = 1 := by
    exact LinearIsometry.adjoint_comp_self
      (realPhaseOrthSynthesis b hb)
  have hbMode : B (lp.single 2 i (1 : ℝ)) = b i :=
    realPhaseOrthSynthesis_single b hb i
  have hcMode : C (lp.single 2 i (1 : ℝ)) = c i :=
    realPhaseOrthSynthesis_single c hc i
  have hAdj : B.adjoint (b i) = lp.single 2 i (1 : ℝ) := by
    calc
      B.adjoint (b i) =
          B.adjoint (B (lp.single 2 i 1)) := by rw [hbMode]
      _ = (B.adjoint ∘L B) (lp.single 2 i 1) := rfl
      _ = lp.single 2 i 1 := by rw [hBB]; rfl
  change C (B.adjoint (b i)) = c i
  rw [hAdj, hcMode]

/-- Exact initial projection of the bounded whole-space real
partial phase. It need not be the identity of H. -/
theorem realPhasePartialCLM_initial_projection
    (b c : ι → H) (hb : Orthonormal ℝ b)
    (hc : Orthonormal ℝ c) :
    (realPhasePartialCLM b c hb hc).adjoint ∘L
      realPhasePartialCLM b c hb hc =
    (realPhaseOrthSynthesis b hb).toContinuousLinearMap ∘L
      (realPhaseOrthSynthesis b hb).toContinuousLinearMap.adjoint := by
  let B : lp (fun _ : ι => ℝ) 2 →L[ℝ] H :=
    (realPhaseOrthSynthesis b hb).toContinuousLinearMap
  let C : lp (fun _ : ι => ℝ) 2 →L[ℝ] H :=
    (realPhaseOrthSynthesis c hc).toContinuousLinearMap
  let W : H →L[ℝ] H := realPhasePartialCLM b c hb hc
  have hCC : C.adjoint ∘L C = 1 :=
    LinearIsometry.adjoint_comp_self (realPhaseOrthSynthesis c hc)
  have hWAdj : W.adjoint = B ∘L C.adjoint := by
    change (C ∘L B.adjoint).adjoint = B ∘L C.adjoint
    simp
  apply ContinuousLinearMap.ext
  intro x
  change (W.adjoint ∘L W) x = (B ∘L B.adjoint) x
  have hc_x : C.adjoint (C (B.adjoint x)) = B.adjoint x := by
    have h := congrArg
      (fun f : (lp (fun _ : ι => ℝ) 2 →L[ℝ]
          lp (fun _ : ι => ℝ) 2) => f (B.adjoint x)) hCC
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.one_apply] using h
  calc
    (W.adjoint ∘L W) x =
        B (C.adjoint (C (B.adjoint x))) := by
      rw [ContinuousLinearMap.comp_apply, hWAdj]
      rfl
    _ = B (B.adjoint x) := congrArg B hc_x
    _ = (B ∘L B.adjoint) x := rfl

/-- Exact final projection of the same real partial isometry; the
final closed range may have any codimension. -/
theorem realPhasePartialCLM_final_projection
    (b c : ι → H) (hb : Orthonormal ℝ b)
    (hc : Orthonormal ℝ c) :
    realPhasePartialCLM b c hb hc ∘L
      (realPhasePartialCLM b c hb hc).adjoint =
    (realPhaseOrthSynthesis c hc).toContinuousLinearMap ∘L
      (realPhaseOrthSynthesis c hc).toContinuousLinearMap.adjoint := by
  let B : lp (fun _ : ι => ℝ) 2 →L[ℝ] H :=
    (realPhaseOrthSynthesis b hb).toContinuousLinearMap
  let C : lp (fun _ : ι => ℝ) 2 →L[ℝ] H :=
    (realPhaseOrthSynthesis c hc).toContinuousLinearMap
  let W : H →L[ℝ] H := realPhasePartialCLM b c hb hc
  have hBB : B.adjoint ∘L B = 1 :=
    LinearIsometry.adjoint_comp_self (realPhaseOrthSynthesis b hb)
  have hWAdj : W.adjoint = B ∘L C.adjoint := by
    change (C ∘L B.adjoint).adjoint = B ∘L C.adjoint
    simp
  apply ContinuousLinearMap.ext
  intro x
  change (W ∘L W.adjoint) x = (C ∘L C.adjoint) x
  have hb_x : B.adjoint (B (C.adjoint x)) = C.adjoint x := by
    have h := congrArg
      (fun f : (lp (fun _ : ι => ℝ) 2 →L[ℝ]
          lp (fun _ : ι => ℝ) 2) => f (C.adjoint x)) hBB
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.one_apply] using h
  calc
    (W ∘L W.adjoint) x =
        C (B.adjoint (B (C.adjoint x))) := by
      rw [ContinuousLinearMap.comp_apply, hWAdj]
      rfl
    _ = C (C.adjoint x) := congrArg C hb_x
    _ = (C ∘L C.adjoint) x := rfl

#print axioms GegenbauerFock.Ultraspherical.realPhaseOrthSynthesis_single
#print axioms GegenbauerFock.Ultraspherical.realPhasePartialCLM_on_source_mode
#print axioms GegenbauerFock.Ultraspherical.realPhasePartialCLM_initial_projection
#print axioms GegenbauerFock.Ultraspherical.realPhasePartialCLM_final_projection

end GegenbauerFock.Ultraspherical
