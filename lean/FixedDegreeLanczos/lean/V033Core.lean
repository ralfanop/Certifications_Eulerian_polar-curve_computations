import Mathlib.Data.Rat.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-! Transparent polynomial certificates. Ascending coefficients; no native_decide.
    This module proves that the list arithmetic used by the certificates has its
    usual real-polynomial meaning. No probability assertion is assumed here. -/
namespace V033

def padd {R : Type} [Add R] : List R → List R → List R
  | [], q => q
  | p, [] => p
  | a::p, b::q => (a+b)::padd p q

def pscale {R : Type} [Mul R] (a : R) (p : List R) : List R := p.map (a * ·)

def pmul {R : Type} [Semiring R] : List R → List R → List R
  | [], _ => []
  | a::p, q => padd (pscale a q) (0::pmul p q)

def peval (p : List ℤ) (x : ℝ) : ℝ :=
  match p with
  | [] => 0
  | a::p => (a : ℝ) + x * peval p x

def pzero (p : List ℤ) : Bool := p.all (· == 0)
def psub (p q : List ℤ) := padd p (pscale (-1) q)

theorem peval_add (p q : List ℤ) (x : ℝ) :
    peval (padd p q) x = peval p x + peval q x := by
  induction p generalizing q with
  | nil => simp [padd, peval]
  | cons a p ih =>
    cases q with
    | nil => simp [padd, peval]
    | cons b q => simp only [padd, peval, Int.cast_add, ih]; ring

theorem peval_scale (a : ℤ) (p : List ℤ) (x : ℝ) :
    peval (pscale a p) x = (a : ℝ) * peval p x := by
  induction p with
  | nil => simp [pscale, peval]
  | cons b p ih => simp only [pscale, List.map_cons, peval, Int.cast_mul] at *; rw [ih]; ring

theorem peval_mul (p q : List ℤ) (x : ℝ) :
    peval (pmul p q) x = peval p x * peval q x := by
  induction p with
  | nil => simp [pmul, peval]
  | cons a p ih =>
    rw [pmul, peval_add, peval_scale]
    simp only [peval, Int.cast_zero, zero_add, ih]
    ring

theorem peval_sub (p q : List ℤ) (x : ℝ) :
    peval (psub p q) x = peval p x - peval q x := by
  rw [psub, peval_add, peval_scale]
  push_cast
  ring

theorem peval_zero (p : List ℤ) (h : pzero p = true) (x : ℝ) : peval p x = 0 := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [pzero, List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    simp [peval, h.1, ih h.2]

theorem checked_equality (p q : List ℤ) (h : pzero (psub p q) = true) (x : ℝ) :
    peval p x = peval q x := by
  have hz := peval_zero _ h x
  rw [peval_sub] at hz
  linarith

def momentCombination (mu : List (List ℤ)) : List (List ℤ) → ℕ → List ℤ
  | [], _ => []
  | p::ps, k => padd (pmul p (mu[k]?.getD [])) (momentCombination mu ps (k+1))

def realCombination (mu : List (List ℤ)) (x : ℝ) : List (List ℤ) → ℕ → ℝ
  | [], _ => 0
  | p::ps, k => peval p x * peval (mu[k]?.getD []) x + realCombination mu x ps (k+1)

theorem momentCombination_eval (mu ps : List (List ℤ)) (k : ℕ) (x : ℝ) :
    peval (momentCombination mu ps k) x = realCombination mu x ps k := by
  induction ps generalizing k with
  | nil => rfl
  | cons p ps ih => simp only [momentCombination, realCombination, peval_add, peval_mul, ih]

theorem checked_orthogonality (mu ps : List (List ℤ)) (k : ℕ)
    (h : pzero (momentCombination mu ps k) = true) (x : ℝ) :
    realCombination mu x ps k = 0 := by
  rw [← momentCombination_eval]
  exact peval_zero _ h x

/-- The monic norm-ratio identity after denominators have been cleared. -/
theorem checked_norm_ratio (N D H Hprev C Cprev : List ℤ)
    (h : pzero (psub (pmul (pmul N Hprev) C) (pmul (pmul D H) Cprev)) = true)
    (x : ℝ) (hD : peval D x ≠ 0) (hHprev : peval Hprev x ≠ 0)
    (hC : peval C x ≠ 0) (hCprev : peval Cprev x ≠ 0) :
    peval N x / peval D x =
      (peval H x / peval C x) / (peval Hprev x / peval Cprev x) := by
  have he := checked_equality _ _ h x
  simp only [peval_mul] at he
  field_simp
  nlinarith [he]

#print axioms checked_norm_ratio
#print axioms checked_orthogonality
end V033
