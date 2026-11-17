import Mathlib

/-!
M16 v16.5 §13, eq. mixed-factor-164 (graph-domain Schur factorization).
Authoritative ZIP SHA-256:
4bde685f7a340e45c43f413aea973db50feea7ba30023f84aefa5de042499c0e.

D is the graph-norm space, X is the ambient space. They remain distinct.
L is ASSUMED to be a continuous linear equivalence D ≃L X; its construction
from the concrete closed L₀ and Neumann argument is a separate obligation.
B : D →L P is the restriction of the manuscript's ambient B to D.
-/
namespace Manuscript16.V165GraphSchur

variable {𝕜 P D X : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup P] [NormedSpace 𝕜 P]
  [NormedAddCommGroup D] [NormedSpace 𝕜 D]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- Domain-side triangular isomorphism, with its explicit continuous inverse. -/
def rightShear (Q : P →L[𝕜] D) : (P × D) ≃L[𝕜] (P × D) where
  toLinearEquiv :=
    { toFun := fun z => (z.1, z.2 + Q z.1)
      invFun := fun z => (z.1, z.2 - Q z.1)
      left_inv := by
        rintro ⟨p,x⟩
        simp
      right_inv := by
        rintro ⟨p,x⟩
        simp
      map_add' := by
        rintro ⟨p,x⟩ ⟨q,y⟩
        simp [map_add, add_assoc, add_left_comm, add_comm]
      map_smul' := by
        rintro c ⟨p,x⟩
        simp [smul_add] }
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Codomain-side triangular isomorphism, on P × X rather than P × D. -/
def leftShear (Q : X →L[𝕜] P) : (P × X) ≃L[𝕜] (P × X) where
  toLinearEquiv :=
    { toFun := fun z => (z.1 + Q z.2, z.2)
      invFun := fun z => (z.1 - Q z.2, z.2)
      left_inv := by
        rintro ⟨p,x⟩
        simp
      right_inv := by
        rintro ⟨p,x⟩
        simp
      map_add' := by
        rintro ⟨p,x⟩ ⟨q,y⟩
        simp [map_add, add_assoc, add_left_comm, add_comm]
      map_smul' := by
        rintro c ⟨p,x⟩
        simp [smul_add] }
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def schur (A : P →L[𝕜] P) (B : D →L[𝕜] P)
    (C : P →L[𝕜] X) (L : D ≃L[𝕜] X) : P →L[𝕜] P :=
  A - B.comp (L.symm.toContinuousLinearMap.comp C)

def block (A : P →L[𝕜] P) (B : D →L[𝕜] P)
    (C : P →L[𝕜] X) (L : D ≃L[𝕜] X) : (P × D) →L[𝕜] (P × X) where
  toFun := fun z => (A z.1 + B z.2, C z.1 + L z.2)
  map_add' := by
    rintro ⟨p,x⟩ ⟨q,y⟩
    simp [map_add, add_assoc, add_left_comm, add_comm]
  map_smul' := by
    rintro c ⟨p,x⟩
    simp [smul_add]
  cont := by fun_prop

def diagonal (F : P →L[𝕜] P) (L : D ≃L[𝕜] X) :
    (P × D) →L[𝕜] (P × X) where
  toFun := fun z => (F z.1, L z.2)
  map_add' := by
    rintro ⟨p,x⟩ ⟨q,y⟩
    simp
  map_smul' := by
    rintro c ⟨p,x⟩
    simp
  cont := by fun_prop

/-- Equality of continuous linear maps between the two distinct spaces. -/
theorem typed_factorization (A : P →L[𝕜] P) (B : D →L[𝕜] P)
    (C : P →L[𝕜] X) (L : D ≃L[𝕜] X) :
    (leftShear (B.comp L.symm.toContinuousLinearMap)).toContinuousLinearMap.comp
      ((diagonal (schur A B C L) L).comp
        (rightShear (L.symm.toContinuousLinearMap.comp C)).toContinuousLinearMap)
      = block A B C L := by
  apply ContinuousLinearMap.ext
  intro z
  rcases z with ⟨p,x⟩
  change
    (A p - B (L.symm (C p)) + B (L.symm (L (x + L.symm (C p)))),
      L (x + L.symm (C p))) = (A p + B x, C p + L x)
  rw [L.symm_apply_apply]
  simp only [map_add, L.apply_symm_apply]
  apply Prod.ext <;> simp <;> abel

/-- Actual block equation with arbitrary right hand side; a solution is
equivalent to the reduced equation and the forced domain component. -/
theorem block_equation_iff (A : P →L[𝕜] P) (B : D →L[𝕜] P)
    (C : P →L[𝕜] X) (L : D ≃L[𝕜] X) (p f : P) (x : D) (g : X) :
    block A B C L (p,x) = (f,g) ↔
      schur A B C L p = f - B (L.symm g) ∧
        x = L.symm (g - C p) := by
  change (A p + B x, C p + L x) = (f,g) ↔
    A p - B (L.symm (C p)) = f - B (L.symm g) ∧
      x = L.symm (g - C p)
  constructor
  · intro h
    have h1 : A p + B x = f := congrArg Prod.fst h
    have h2 : C p + L x = g := congrArg Prod.snd h
    have hx : x = L.symm (g - C p) := by
      rw [← h2, add_sub_cancel_left, L.symm_apply_apply]
    refine ⟨?_,hx⟩
    rw [hx, map_sub, map_sub] at h1
    calc
      A p - B (L.symm (C p)) =
        (A p + (B (L.symm g) - B (L.symm (C p)))) - B (L.symm g) := by abel
      _ = f - B (L.symm g) := by rw [h1]
  · rintro ⟨h,hx⟩
    rw [hx]
    apply Prod.ext
    · change A p + B (L.symm (g - C p)) = f
      rw [map_sub, map_sub]
      calc
        A p + (B (L.symm g) - B (L.symm (C p))) =
            (A p - B (L.symm (C p))) + B (L.symm g) := by abel
        _ = f := by rw [h, sub_add_cancel]
    · change C p + L (L.symm (g - C p)) = g
      rw [L.apply_symm_apply]
      abel

#print axioms Manuscript16.V165GraphSchur.rightShear
#print axioms Manuscript16.V165GraphSchur.leftShear
#print axioms Manuscript16.V165GraphSchur.typed_factorization
#print axioms Manuscript16.V165GraphSchur.block_equation_iff
end Manuscript16.V165GraphSchur
