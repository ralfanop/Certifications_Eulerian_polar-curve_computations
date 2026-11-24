import Mathlib

/-! M13 Proposition 4.9, global obstruction and transported domains.
A group-valued path transport with composition/reversal laws admits a
global phase exactly when every loop has trivial transport. This is an
abstract path-integral algebra theorem; smoothness, actual manifold
line integrals, and the differential relation h⁻¹ dh = iω A remain open.
The domain and inverse transport below are explicit equivalences, not
a proof of selfadjointness of an unbounded magnetic Laplacian. -/
namespace Manuscript13.GlobalHolonomy20261124

section Holonomy
variable {X G : Type*} [Group G]
variable (P : X → X → Type*)
variable (comp : ∀ {x y z}, P x y → P y z → P x z)
variable (rev : ∀ {x y}, P x y → P y x)
variable (T : ∀ {x y}, P x y → G)

theorem phase_from_trivial_loops (base : X) (paths : ∀ x, P base x)
    (hcomp : ∀ {x y z} (p : P x y) (q : P y z),
      T (comp p q) = T q * T p)
    (hrev : ∀ {x y} (p : P x y), T (rev p) = (T p)⁻¹)
    (hloop : ∀ x (p : P x x), T p = 1) :
    ∃ h : X → G, ∀ {x y} (p : P x y), T p = h y * (h x)⁻¹ := by
  refine ⟨fun x => T (paths x), ?_⟩
  intro x y p
  have hl := hloop base (comp (comp (paths x) p) (rev (paths y)))
  rw [hcomp, hcomp, hrev] at hl
  change T p = T (paths y) * (T (paths x))⁻¹
  calc
    T p = T (paths y) * ((T (paths y))⁻¹ * (T p * T (paths x))) *
        (T (paths x))⁻¹ := by group
    _ = _ := by rw [hl, mul_one]

theorem trivial_loops_from_phase
    (h : X → G) (hp : ∀ {x y} (p : P x y), T p = h y * (h x)⁻¹) :
    ∀ x (p : P x x), T p = 1 := by
  intro x p
  rw [hp, mul_inv_cancel]

theorem holonomy_iff_phase (base : X) (paths : ∀ x, P base x)
    (hcomp : ∀ {x y z} (p : P x y) (q : P y z),
      T (comp p q) = T q * T p)
    (hrev : ∀ {x y} (p : P x y), T (rev p) = (T p)⁻¹) :
    (∀ x (p : P x x), T p = 1) ↔
    ∃ h : X → G, ∀ {x y} (p : P x y), T p = h y * (h x)⁻¹ := by
  constructor
  · exact phase_from_trivial_loops P comp rev T base paths hcomp hrev
  · rintro ⟨h, hp⟩
    exact trivial_loops_from_phase P T h hp

theorem path_independence (h : X → G)
    (hp : ∀ {x y} (p : P x y), T p = h y * (h x)⁻¹)
    {x y : X} (p q : P x y) : T p = T q := by
  rw [hp p, hp q]

end Holonomy

noncomputable def chargedPhase (ω s : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((ω*s : ℝ) : ℂ))

theorem chargedPhase_zero (ω : ℝ) : chargedPhase ω 0 = 1 := by
  simp [chargedPhase]

theorem chargedPhase_add (ω s t : ℝ) :
    chargedPhase ω (s+t) = chargedPhase ω s * chargedPhase ω t := by
  unfold chargedPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem chargedPhase_reverse (ω s : ℝ) :
    chargedPhase ω s * chargedPhase ω (-s) = 1 := by
  rw [← chargedPhase_add, add_neg_cancel, chargedPhase_zero]

theorem chargedPhase_unit (ω s : ℝ) : ‖chargedPhase ω s‖ = 1 := by
  unfold chargedPhase
  rw [Complex.norm_exp]
  simp [Complex.mul_re]

section Domain
variable {X Y : Type*}

def transportedDomain (U : X ≃ Y) (D : Set X) : Set Y :=
  {y | U.symm y ∈ D}

theorem transported_mem (U : X ≃ Y) (D : Set X) (x : X) :
    U x ∈ transportedDomain U D ↔ x ∈ D := by
  simp [transportedDomain]

def domainEquiv (U : X ≃ Y) (D : Set X) :
    D ≃ transportedDomain U D where
  toFun x := ⟨U x, (transported_mem U D x).2 x.property⟩
  invFun y := ⟨U.symm y, y.property⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp

def conjugate (U : X ≃ Y) (A : X → X) (y : Y) : Y :=
  U (A (U.symm y))

theorem conjugate_intertwines (U : X ≃ Y) (A : X → X) (x : X) :
    conjugate U A (U x) = U (A x) := by simp [conjugate]

theorem conjugate_leftInverse (U : X ≃ Y) (A R : X → X)
    (h : Function.LeftInverse R A) :
    Function.LeftInverse (conjugate U R) (conjugate U A) := by
  intro y
  simp [conjugate, h]

theorem conjugate_rightInverse (U : X ≃ Y) (A R : X → X)
    (h : Function.RightInverse R A) :
    Function.RightInverse (conjugate U R) (conjugate U A) := by
  intro y
  simp [conjugate, h]

theorem inverse_on_domain_transport (U : X ≃ Y) (D : Set X)
    (A R : X → X) (h : ∀ x ∈ D, R (A x) = x)
    (y : Y) (hy : y ∈ transportedDomain U D) :
    conjugate U R (conjugate U A y) = y := by
  have hx : U.symm y ∈ D := hy
  simp [conjugate, h (U.symm y) hx]

end Domain
end Manuscript13.GlobalHolonomy20261124

#print axioms Manuscript13.GlobalHolonomy20261124.phase_from_trivial_loops
#print axioms Manuscript13.GlobalHolonomy20261124.trivial_loops_from_phase
#print axioms Manuscript13.GlobalHolonomy20261124.holonomy_iff_phase
#print axioms Manuscript13.GlobalHolonomy20261124.path_independence
#print axioms Manuscript13.GlobalHolonomy20261124.chargedPhase_zero
#print axioms Manuscript13.GlobalHolonomy20261124.chargedPhase_add
#print axioms Manuscript13.GlobalHolonomy20261124.chargedPhase_reverse
#print axioms Manuscript13.GlobalHolonomy20261124.chargedPhase_unit
#print axioms Manuscript13.GlobalHolonomy20261124.transported_mem
#print axioms Manuscript13.GlobalHolonomy20261124.domainEquiv
#print axioms Manuscript13.GlobalHolonomy20261124.conjugate_intertwines
#print axioms Manuscript13.GlobalHolonomy20261124.conjugate_leftInverse
#print axioms Manuscript13.GlobalHolonomy20261124.conjugate_rightInverse
#print axioms Manuscript13.GlobalHolonomy20261124.inverse_on_domain_transport
