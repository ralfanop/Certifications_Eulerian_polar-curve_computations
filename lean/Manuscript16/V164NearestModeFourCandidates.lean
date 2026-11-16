import Mathlib

/-!
Manuscript 16 v16.4, Section 13: integer nearest-mode shell combinatorics.
Authoritative ZIP SHA-256:
72afc74dba6ad9d2be925c1c7ee964faffcd767ef43aa88a1557e1a6b1707966.
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
  rcases le_total 0 k with hk | hk
  · rcases le_total 0 (ell + k) with hs | hs
    · rw [abs_of_nonneg hk, abs_of_nonneg hs] at h
      omega
    · rw [abs_of_nonneg hk, abs_of_nonpos hs] at h
      omega
  · rcases le_total 0 (ell + k) with hs | hs
    · rw [abs_of_nonpos hk, abs_of_nonneg hs] at h
      omega
    · rw [abs_of_nonpos hk, abs_of_nonpos hs] at h
      omega

#print axioms Manuscript16.nearest_mode_four_candidates

end Manuscript16
