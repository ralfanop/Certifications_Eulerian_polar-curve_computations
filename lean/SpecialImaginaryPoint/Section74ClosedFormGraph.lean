import Mathlib

/-! Manuscript 14 §7.4, source SHA256
b0aba7205b0e915ff49512ffd66f4deeaef29d2de766293be58c090820aeca68.
Bridge from a covariant derivative and its densely defined formal adjoint
to a complete form space with its actual graph norm and dense embedding.
Classical closed-form framework: Kato VI §1.3–4, §2.1–3;
Schmüdgen §§10.1–10.4 (pp. 221–235).
The concrete distributional magnetic derivative and its integration by
parts, and the compactness of the specific embedding, remain separate. -/
noncomputable section
open scoped InnerProductSpace
namespace Manuscript14.ClosedFormGraph

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [CompleteSpace K]

/-- A densely defined formal adjoint supplies a genuine closed extension. -/
theorem closable_of_formal_adjoint (T : H →ₗ.[ℂ] K) (S : K →ₗ.[ℂ] H)
    (hS : Dense (S.domain : Set K)) (hf : T.IsFormalAdjoint S) :
    T.IsClosable := by
  apply LinearPMap.isClosable_iff_exists_closed_extension.mpr
  exact ⟨S.adjoint, LinearPMap.adjoint_isClosed hS,
    LinearPMap.IsFormalAdjoint.le_adjoint hS hf.symm⟩

/-- In particular a densely defined symmetric operator is closable. -/
theorem symmetric_closable (T : H →ₗ.[ℂ] H)
    (hd : Dense (T.domain : Set H)) (hs : T.IsFormalAdjoint T) :
    T.IsClosable := closable_of_formal_adjoint T T hd hs

/-- The graph of the closed covariant derivative with the Hilbert L²-product
    norm (not the default maximum norm of the plain product). -/
def graphSpace (T : H →ₗ.[ℂ] K) : Submodule ℂ (WithLp 2 (H × K)) :=
  T.graph.comap (WithLp.linearEquiv 2 ℂ (H × K)).toLinearMap

theorem graphSpace_closed (T : H →ₗ.[ℂ] K) (hc : T.IsClosed) :
    IsClosed (graphSpace T : Set (WithLp 2 (H × K))) := by
  change IsClosed ((WithLp.prodContinuousLinearEquiv 2 ℂ H K) ⁻¹'
    (T.graph : Set (H × K)))
  exact hc.preimage (WithLp.prodContinuousLinearEquiv 2 ℂ H K).continuous

theorem graphSpace_complete (T : H →ₗ.[ℂ] K) (hc : T.IsClosed) :
    CompleteSpace (graphSpace T) := by
  letI : IsClosed (graphSpace T : Set (WithLp 2 (H × K))) :=
    graphSpace_closed T hc
  infer_instance

def inclusion (T : H →ₗ.[ℂ] K) : graphSpace T →L[ℂ] H :=
  (WithLp.fstL 2 ℂ H K).comp (graphSpace T).subtypeL

def covariant (T : H →ₗ.[ℂ] K) : graphSpace T →L[ℂ] K :=
  (WithLp.sndL 2 ℂ H K).comp (graphSpace T).subtypeL

/-- Formula for the complete graph/form norm. -/
theorem energy_norm (T : H →ₗ.[ℂ] K) (u : graphSpace T) :
    ‖u‖^2 = ‖inclusion T u‖^2 + ‖covariant T u‖^2 :=
  WithLp.prod_norm_sq_eq_of_L2 u.1

theorem inclusion_injective (T : H →ₗ.[ℂ] K) :
    Function.Injective (inclusion T) := by
  intro u v h
  apply Subtype.ext
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ H K).injective
  have hu : (u.1.fst, u.1.snd) ∈ T.graph := u.2
  have hv : (v.1.fst, v.1.snd) ∈ T.graph := v.2
  have hfst : u.1.fst = v.1.fst := h
  exact Prod.ext hfst (T.mem_graph_snd_inj hu hv hfst)

theorem inclusion_range (T : H →ₗ.[ℂ] K) :
    Set.range (inclusion T) = (T.domain : Set H) := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    have h : (u.1.fst, u.1.snd) ∈ T.graph := u.2
    exact LinearPMap.mem_domain_of_mem_graph h
  · intro hx
    have h : (x, T ⟨x,hx⟩) ∈ T.graph := T.mem_graph ⟨x,hx⟩
    exact ⟨⟨WithLp.toLp 2 (x, T ⟨x,hx⟩), h⟩, rfl⟩

theorem closed_form_domain_dense (T : H →ₗ.[ℂ] K)
    (hd : Dense (T.domain : Set H)) :
    DenseRange (inclusion T.closure) := by
  rw [DenseRange, inclusion_range]
  exact hd.mono (fun x hx => T.le_closure.1 hx)

/-- The closure of the covariant derivative defines a complete graph
    Hilbert space and an injective dense embedding into the ambient space. -/
theorem closed_form_space (T : H →ₗ.[ℂ] K) (S : K →ₗ.[ℂ] H)
    (hd : Dense (T.domain : Set H)) (hS : Dense (S.domain : Set K))
    (hf : T.IsFormalAdjoint S) :
    CompleteSpace (graphSpace T.closure) ∧
      Function.Injective (inclusion T.closure) ∧
      DenseRange (inclusion T.closure) := by
  have hc := (closable_of_formal_adjoint T S hS hf).closure_isClosed
  exact ⟨graphSpace_complete _ hc, inclusion_injective _, closed_form_domain_dense T hd⟩

#print axioms closable_of_formal_adjoint
#print axioms symmetric_closable
#print axioms graphSpace_closed
#print axioms graphSpace_complete
#print axioms energy_norm
#print axioms inclusion_injective
#print axioms inclusion_range
#print axioms closed_form_domain_dense
#print axioms closed_form_space

end Manuscript14.ClosedFormGraph
