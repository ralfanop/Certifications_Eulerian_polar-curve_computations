import Mathlib
import Manuscript16.V164NearestModeShellFilter

/-!
Manuscript 16 v16.4, Section 13: finite cutoff shell cardinality.
Authoritative ZIP SHA-256:
72afc74dba6ad9d2be925c1c7ee964faffcd767ef43aa88a1557e1a6b1707966.
Only a finite combinatorial bound; no infinite Schatten summability,
Fredholm or det4 conclusion is claimed.
-/

namespace Manuscript16

/-- Every nearest-mode shell contains at most four integer indices,
even after restriction to an arbitrary finite spectral cutoff. -/
theorem nearest_mode_shell_filter_card_le_four (ell j : ℤ) (s : Finset ℤ) :
    (s.filter (fun k => min |k| |ell + k| = j)).card ≤ 4 := by
  have hsubset := nearest_mode_shell_filter_subset ell j s
  have hcard := Finset.card_le_card hsubset
  have hfour : ({-j, j, -ell - j, -ell + j} : Finset ℤ).card ≤ 4 := by
    simp [Finset.card_insert_le]
    omega
  omega

#print axioms Manuscript16.nearest_mode_shell_filter_card_le_four

end Manuscript16
