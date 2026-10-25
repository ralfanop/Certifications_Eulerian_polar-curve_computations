import Mathlib

/-!
# Two commuting bosonic modes: algebraic coefficient model

A two-index array represents formal power-series coefficients. Creators
shift indices; annihilators differentiate. These are formal Weyl algebra
identities, NOT the adjoint or domain theory of the Gaussian Hilbert space.
-/
namespace GegenbauerFock

abbrev TwoMode := ℕ → ℕ → ℂ

def annA (f : TwoMode) (m n : ℕ) : ℂ :=
  ((m : ℂ) + 1) * f (m+1) n

def creA (f : TwoMode) (m n : ℕ) : ℂ :=
  match m with
  | 0 => 0
  | k+1 => f k n

def annB (f : TwoMode) (m n : ℕ) : ℂ :=
  ((n : ℂ) + 1) * f m (n+1)

def creB (f : TwoMode) (m n : ℕ) : ℂ :=
  match n with
  | 0 => 0
  | k+1 => f m k

theorem annA_creA_CCR (f : TwoMode) (m n : ℕ) :
    annA (creA f) m n - creA (annA f) m n = f m n := by
  cases m with
  | zero => simp [annA, creA]
  | succ k =>
      simp [annA, creA, Nat.cast_succ]
      ring

theorem annB_creB_CCR (f : TwoMode) (m n : ℕ) :
    annB (creB f) m n - creB (annB f) m n = f m n := by
  cases n with
  | zero => simp [annB, creB]
  | succ k =>
      simp [annB, creB, Nat.cast_succ]
      ring

theorem annA_annB_commute (f : TwoMode) (m n : ℕ) :
    annA (annB f) m n = annB (annA f) m n := by
  simp only [annA, annB]
  ring

theorem annA_creB_commute (f : TwoMode) (m n : ℕ) :
    annA (creB f) m n = creB (annA f) m n := by
  cases n <;> simp [annA, creB] <;> ring

theorem creA_annB_commute (f : TwoMode) (m n : ℕ) :
    creA (annB f) m n = annB (creA f) m n := by
  cases m <;> simp [annB, creA] <;> ring

theorem creA_creB_commute (f : TwoMode) (m n : ℕ) :
    creA (creB f) m n = creB (creA f) m n := by
  cases m <;> cases n <;> simp [creA, creB]

def aVacuumFromB (g : ℕ → ℂ) : TwoMode :=
  fun m n => if m = 0 then g n else 0

theorem annA_aVacuumFromB (g : ℕ → ℂ) (m n : ℕ) :
    annA (aVacuumFromB g) m n = 0 := by
  simp [annA, aVacuumFromB]

theorem annB_aVacuumFromB_zero (g : ℕ → ℂ) (n : ℕ) :
    annB (aVacuumFromB g) 0 n = ((n : ℂ)+1) * g (n+1) := by
  simp [annB, aVacuumFromB]

def jointVacuum : TwoMode :=
  fun m n => if m = 0 ∧ n = 0 then 1 else 0

theorem annA_jointVacuum (m n : ℕ) :
    annA jointVacuum m n = 0 := by
  simp [annA, jointVacuum]

theorem annB_jointVacuum (m n : ℕ) :
    annB jointVacuum m n = 0 := by
  simp [annB, jointVacuum]

end GegenbauerFock
