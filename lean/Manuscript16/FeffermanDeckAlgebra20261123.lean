import Mathlib

/-!
Manuscript 16, 23 November 2026, §2.3 Fefferman--Einstein.
Source ZIP SHA-256: c17ef25f36523f66d5788a5bbec4809345c4593ae41075672938e1d012d9b9ad.

The deck-conjugacy identity holds in every group. The parity and shifted
resonance calculations are exact. The Hodge-geometric realisation of the
metric, differential operators and their unbounded domains is not claimed.
-/
namespace Manuscript16.Fefferman20261123

variable {G : Type*} [Group G]

/-- Algebraic chart (v,q) ↦ (v,v⁻¹q). -/
def phi (x : G × G) : G × G := (x.1, x.1⁻¹ * x.2)

def phiInv (x : G × G) : G × G := (x.1, x.1 * x.2)

/-- Simultaneous deck action, specialised to the antipodal element. -/
def iota (s : G) (x : G × G) : G × G := (s * x.1, s * x.2)

/-- Target action on the first factor only. -/
def deckA (s : G) (x : G × G) : G × G := (s * x.1, x.2)

theorem phi_left_inverse (x : G × G) : phiInv (phi x) = x := by
  cases x with
  | mk v q => simp [phi, phiInv]

theorem phi_right_inverse (x : G × G) : phi (phiInv x) = x := by
  cases x with
  | mk v q => simp [phi, phiInv]

/-- The exact chart/deck conjugacy, without assuming commutativity. -/
theorem phi_iota_eq_deckA_phi (s : G) (x : G × G) :
    phi (iota s x) = deckA s (phi x) := by
  cases x with
  | mk v q => simp [phi, iota, deckA, mul_inv_rev, mul_assoc]

theorem iota_involutive (s : G) (hs : s * s = 1) (x : G × G) :
    iota s (iota s x) = x := by
  cases x with
  | mk v q => simp [iota, ← mul_assoc, hs]

theorem deckA_involutive (s : G) (hs : s * s = 1) (x : G × G) :
    deckA s (deckA s x) = x := by
  cases x with
  | mk v q => simp [deckA, ← mul_assoc, hs]

/-- Operator conjugation by a bijection. Geometric domains are separate. -/
def transported {X : Type*} (P : X ≃ X) (W : X → X) : X → X :=
  fun x => P (W (P.symm x))

theorem transported_intertwines {X : Type*} (P : X ≃ X) (W : X → X)
    (x : X) : transported P W (P x) = P (W x) := by
  simp [transported]

theorem shifted_resonance_factor (ell n k : ℤ) :
    ell ^ 2 - (n - k) ^ 2 = (ell - n + k) * (ell + n - k) := by
  ring

theorem resonance_shift_or (ell n k : ℤ)
    (h : ell ^ 2 - (n - k) ^ 2 = 0) :
    n = k + ell ∨ n = k - ell := by
  rw [shifted_resonance_factor] at h
  rcases mul_eq_zero.mp h with h1 | h2
  · left; omega
  · right; omega

/-- Weight parity, deck parity and the shifted resonance imply even degree. -/
theorem fefferman_invariant_resonance_even (ell n k : ℤ)
    (hweight : (k - ell) % 2 = 0)
    (hinvariant : (n + ell) % 2 = 0)
    (hres : ell ^ 2 - (n - k) ^ 2 = 0) :
    ell % 2 = 0 := by
  rcases resonance_shift_or ell n k hres with h | h <;> omega

/-- Original frequencies ±ell satisfy diagonal deck parity at every degree. -/
theorem original_resonances_deck_even (ell : ℤ) :
    (ell + ell) % 2 = 0 ∧ (-ell + ell) % 2 = 0 := by
  constructor <;> omega

#print axioms Manuscript16.Fefferman20261123.phi_left_inverse
#print axioms Manuscript16.Fefferman20261123.phi_right_inverse
#print axioms Manuscript16.Fefferman20261123.phi_iota_eq_deckA_phi
#print axioms Manuscript16.Fefferman20261123.iota_involutive
#print axioms Manuscript16.Fefferman20261123.deckA_involutive
#print axioms Manuscript16.Fefferman20261123.transported_intertwines
#print axioms Manuscript16.Fefferman20261123.shifted_resonance_factor
#print axioms Manuscript16.Fefferman20261123.resonance_shift_or
#print axioms Manuscript16.Fefferman20261123.fefferman_invariant_resonance_even
#print axioms Manuscript16.Fefferman20261123.original_resonances_deck_even
end Manuscript16.Fefferman20261123
