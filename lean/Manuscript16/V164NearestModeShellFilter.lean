import Mathlib
import Manuscript16.V164NearestModeFourCandidates

/-!
Manuscript 16 v16.4, Section 13: finite-shell containment.
Authoritative source ZIP SHA-256:
72afc74dba6ad9d2be925c1c7ee964faffcd767ef43aa88a1557e1a6b1707966.
This is a finite combinatorial lemma only; it does not establish
Schatten summability, spectral multiplicity, or Fredholm/det4 results.
-/

namespace Manuscript16

/-- The integer indices selected by a nearest-mode shell from any finite
cutoff are contained in a set with four explicitly specified candidates. -/
theorem nearest_mode_shell_filter_subset (ell j : ℤ) (s : Finset ℤ) :
    (s.filter (fun k => min |k| |ell + k| = j)) ⊆
      ({-j, j, -ell - j, -ell + j} : Finset ℤ) := by
  intro k hk
  have h : min |k| |ell + k| = j := (Finset.mem_filter.mp hk).2
  rcases nearest_mode_four_candidates ell k j h with h | h | h | h
  all_goals simp [h]

#print axioms Manuscript16.nearest_mode_shell_filter_subset

end Manuscript16
