# Eulerian distributions, n = 3, …, 670, in the Flajolet–Sedgewick Figure IX.14 field

`Eulerian_distribution_FS_IX14_field_n3_670_vector_thin100.pdf` extends Figure IX.14 of
P. Flajolet and R. Sedgewick, *Analytic Combinatorics* (Cambridge University Press, 2009, p. 695)
from n = 3, …, 60 to n = 3, …, 670, in the same field x ∈ [0, 1], y ∈ [0, 0.7].

**Data.** Only the book's formulas are used. A geometric-series expansion of its generating
function (75), A(z,u) = (u − 1)/(u − e^{z(u−1)}) (p. 209), gives the Eulerian numbers exactly in
integers: A_{n,k} = Σ_{i=0}^{k} (−1)^i C(n+1, i) (k+1−i)^n. The points are (k/(n+1), A_{n,k−1}/n!),
k = 1, …, n, i.e. the coefficients [zⁿuᵏ] F(z,u) of F = uA (p. 658), joined by straight segments.
Checks: the first rows match the book, each row sums to n!, and every vertex agrees with the
Eulerian recurrence.

**Drawing.** `fs_ix14_vector.py` writes the PDF directly, with no plotting library or axes.
The page is the field itself, at 14,400 pt per unit on both axes (200 × 140 in). All 224,782
vertices are kept, with coordinates to 10⁻⁴ pt. The lines are 0.0205 pt wide, so individual
curves separate under magnification.

Reproduce: `python3 fs_ix14_vector.py Eulerian_distribution_FS_IX14_field_n3_670_vector_thin100.pdf 100`
(byte-identical output).
