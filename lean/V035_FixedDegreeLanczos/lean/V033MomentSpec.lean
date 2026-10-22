import V033Core
import Mathlib.Data.Nat.Factorial.Basic
namespace V033
/- z tracks t^2. All divisions here are exact integer divisions.
   Clearing r! * A^r avoids rational reduction in the kernel. -/
def egfDen : ℕ := 37294565193577646874314695526467900538880000000
def uniformEGFInteger (r : ℕ) : ℤ :=
  if r=0 then 0 else (egfDen / (4^r * (2*r+1).factorial) : ℕ)
def uniformEGFIntegers : List ℤ := (List.range 17).map uniformEGFInteger
def ipow (p : List ℤ) : ℕ → List ℤ
  | 0 => [1]
  | k+1 => (pmul p (ipow p k)).take 17
def fallingInteger : ℕ → List ℤ
  | 0 => [1]
  | k+1 => pmul [-(k:ℤ), 1] (fallingInteger k)
def occupancyScale (r : ℕ) : ℤ := (r.factorial * egfDen^r : ℕ)
def clearedOccupancyMoment (L : ℤ) (r : ℕ) : List ℤ :=
  ((List.range (r+1)).map (fun k =>
    pscale (((2*r).factorial : ℤ) * (r.factorial / k.factorial : ℕ) * L *
      (egfDen^(r-k) : ℕ) * ((ipow uniformEGFIntegers k)[r]?.getD 0))
      (fallingInteger k))).foldr padd []
end V033
