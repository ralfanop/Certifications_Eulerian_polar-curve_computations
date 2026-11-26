import Mathlib

namespace M16KreinDomains

/- Graphs encode unbounded operators without extending them to total maps.
   Transport and adjunction below are equalities of graphs, not merely
   identities of values on a common domain. The pairing can be specialized
   to the real or complex Hilbert inner product. -/

def transport {E F : Type*} (u : E ≃ F) (G : Set (E × E)) : Set (F × F) :=
  {v | (u.symm v.1, u.symm v.2) ∈ G}

def domain {E : Type*} (G : Set (E × E)) : Set E :=
  {x | ∃ y, (x,y) ∈ G}

def adjGraph {E R : Type*} (p : E → E → R) (G : Set (E × E)) : Set (E × E) :=
  {v | ∀ x y, (x,y) ∈ G → p y v.1 = p x v.2}

theorem transport_domain {E F : Type*} (u : E ≃ F) (G : Set (E × E)) :
    domain (transport u G) = u '' domain G := by
  ext x
  constructor
  · intro hx
    change ∃ y, (u.symm x, u.symm y) ∈ G at hx
    obtain ⟨y, hy⟩ := hx
    exact ⟨u.symm x, ⟨u.symm y, hy⟩, u.apply_symm_apply x⟩
  · rintro ⟨v, ⟨w, hw⟩, rfl⟩
    change ∃ y, (u.symm (u v), u.symm y) ∈ G
    exact ⟨u w, by simpa only [Equiv.symm_apply_apply] using hw⟩

theorem transport_adjGraph {E F R : Type*} (u : E ≃ F)
    (p : E → E → R) (q : F → F → R) (G : Set (E × E))
    (hp : ∀ x y, q (u x) (u y) = p x y) :
    adjGraph q (transport u G) = transport u (adjGraph p G) := by
  ext v
  change (∀ x y, (u.symm x,u.symm y) ∈ G → q y v.1 = q x v.2) ↔
    (∀ x y, (x,y) ∈ G → p y (u.symm v.1) = p x (u.symm v.2))
  constructor
  · intro h x y hxy
    have hh := h (u x) (u y) (by simpa only [Equiv.symm_apply_apply] using hxy)
    have h1 : q (u y) v.1 = p y (u.symm v.1) := by
      simpa only [Equiv.apply_symm_apply] using hp y (u.symm v.1)
    have h2 : q (u x) v.2 = p x (u.symm v.2) := by
      simpa only [Equiv.apply_symm_apply] using hp x (u.symm v.2)
    exact h1.symm.trans (hh.trans h2)
  · intro h x y hxy
    have hh := h (u.symm x) (u.symm y) hxy
    have h1 : q y v.1 = p (u.symm y) (u.symm v.1) := by
      simpa only [Equiv.apply_symm_apply] using hp (u.symm y) (u.symm v.1)
    have h2 : q x v.2 = p (u.symm x) (u.symm v.2) := by
      simpa only [Equiv.apply_symm_apply] using hp (u.symm x) (u.symm v.2)
    exact h1.trans (hh.trans h2.symm)

theorem transport_adjoint_domain {E F R : Type*} (u : E ≃ F)
    (p : E → E → R) (q : F → F → R) (G : Set (E × E))
    (hp : ∀ x y, q (u x) (u y) = p x y) :
    domain (adjGraph q (transport u G)) = u '' domain (adjGraph p G) := by
  rw [transport_adjGraph u p q G hp, transport_domain]

-- Resolvent equations on the graph; boundedness is a separate obligation.
def uniquelySolvable {E : Type*} [AddCommGroup E] [Module ℂ E]
    (G : Set (E × E)) (z : ℂ) : Prop :=
  ∀ f, ∃! x, (x, f + z • x) ∈ G

theorem transport_unique_solvability {E F : Type*}
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (u : E ≃ₗ[ℂ] F) (G : Set (E × E)) (z : ℂ) :
    uniquelySolvable (transport u.toEquiv G) z ↔ uniquelySolvable G z := by
  constructor
  · intro h f
    obtain ⟨x, hx, hu⟩ := h (u f)
    change (u.symm x, u.symm (u f + z • x)) ∈ G at hx
    refine ⟨u.symm x, ?_, ?_⟩
    · simpa only [map_add, map_smul, LinearEquiv.symm_apply_apply] using hx
    · intro y hy
      have hh : (u y, u f + z • u y) ∈ transport u.toEquiv G := by
        change (u.symm (u y),u.symm (u f + z • u y)) ∈ G
        simpa only [map_add, map_smul, LinearEquiv.symm_apply_apply] using hy
      have he := hu (u y) hh
      simpa only [LinearEquiv.symm_apply_apply] using congrArg (fun v : F => u.symm v) he
  · intro h f
    obtain ⟨x, hx, hu⟩ := h (u.symm f)
    refine ⟨u x, ?_, ?_⟩
    · change (u.symm (u x),u.symm (f + z • u x)) ∈ G
      simpa only [map_add, map_smul, LinearEquiv.symm_apply_apply] using hx
    · intro y hy
      change (u.symm y,u.symm (f + z • y)) ∈ G at hy
      have hh : (u.symm y,u.symm f + z • u.symm y) ∈ G := by
        simpa only [map_add, map_smul] using hy
      have he := hu (u.symm y) hh
      simpa only [LinearEquiv.apply_symm_apply] using congrArg (fun v : E => u v) he

def perturb {E : Type*} [AddCommGroup E] (G : Set (E × E)) (k : E → E) :
    Set (E × E) := {v | (v.1, v.2-k v.1) ∈ G}

theorem perturb_domain {E : Type*} [AddCommGroup E]
    (G : Set (E × E)) (k : E → E) :
    domain (perturb G k) = domain G := by
  ext x
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y-k x, hy⟩
  · rintro ⟨y, hy⟩
    refine ⟨y+k x, ?_⟩
    change (x,y+k x-k x) ∈ G
    simpa only [add_sub_cancel_right] using hy

-- The graph form of the bounded-perturbation adjoint identity.
-- The everywhere-defined adjoint ka of k is supplied by the Hilbert
-- bounded-adjoint theorem in applications.
theorem adjGraph_perturb {E : Type*} [AddCommGroup E]
    (p : E → E → ℂ) (G : Set (E × E)) (k ka : E → E)
    (hadd : ∀ x y z, p (x+y) z = p x z + p y z)
    (hsub : ∀ x y z, p x (y-z) = p x y - p x z)
    (hk : ∀ x y, p (k x) y = p x (ka y)) :
    adjGraph p (perturb G k) = perturb (adjGraph p G) ka := by
  ext v
  change (∀ x y, (x,y-k x) ∈ G → p y v.1 = p x v.2) ↔
    (∀ x y, (x,y) ∈ G → p y v.1 = p x (v.2-ka v.1))
  constructor
  · intro h x y hxy
    have hh := h x (y+k x) (by simpa only [add_sub_cancel_right] using hxy)
    rw [hadd, hk] at hh
    rw [hsub]
    exact eq_sub_of_add_eq hh
  · intro h x y hxy
    have hh := h x (y-k x) hxy
    have he : y-k x+k x = y := sub_add_cancel y (k x)
    calc
      p y v.1 = p (y-k x+k x) v.1 := by rw [he]
      _ = p (y-k x) v.1 + p (k x) v.1 := hadd _ _ _
      _ = p x v.2 := by rw [hh,hsub,hk]; abel

theorem adjGraph_perturb_domain {E : Type*} [AddCommGroup E]
    (p : E → E → ℂ) (G : Set (E × E)) (k ka : E → E)
    (hadd : ∀ x y z, p (x+y) z = p x z + p y z)
    (hsub : ∀ x y z, p x (y-z) = p x y - p x z)
    (hk : ∀ x y, p (k x) y = p x (ka y)) :
    domain (adjGraph p (perturb G k)) = domain (adjGraph p G) := by
  rw [adjGraph_perturb p G k ka hadd hsub hk, perturb_domain]

#print axioms transport_domain
#print axioms transport_adjGraph
#print axioms transport_adjoint_domain
#print axioms transport_unique_solvability
#print axioms perturb_domain
#print axioms adjGraph_perturb
#print axioms adjGraph_perturb_domain

end M16KreinDomains
