import Mathlib

/-!
Manuscript 16 v16.4, Section 13: integer nearest-mode shell combinatorics.
Authoritative source identifier (not a re-certification of source bytes):
ZIP SHA-256 c6e92c8a6a58504f41fb1756be20e9be66739fb9880b00a34012718b46d2586f.
This file proves only a finite integer candidate bound. It does not prove
Schatten summability, spectral multiplicity, or the det4 theorem.
-/

namespace Manuscript16

/-- For fixed integer separation ell, each nearest-mode shell has at most
four possible integer indices. No restrictions on ell or j are required
for this elementary implication. -/
theorem nearest_mode_four_candidates (ell k j : ℤ)
    (h : min |k| |(ell + k)| = j) :
    k = -j ∨ k = j ∨ k = -ell - j ∨ k = -ell + j := by
  omega

#print axioms Manuscript16.nearest_mode_four_candidates

end Manuscript16
