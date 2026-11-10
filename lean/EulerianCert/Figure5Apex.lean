/-
Manuscript 11 (10 November 2026), Figure 5, p. 21.

A formal certificate for the apex of the n = 3 Eulerian distribution
inside the full Figure 5 family n = 3, ..., 670.
The histogram itself is the extension of Flajolet--Sedgewick
(2009), Analytic Combinatorics, Fig. IX.14 (n = 3, ..., 60).

The angle certificate uses the exact Eulerian recurrence, not
lengths or angles read from the rendered figure.

The five targets are:
  1. The exact rational coordinates of the three n=3 vertices;
  2. Equality of the oblique Euclidean side lengths;
  3. Exact half-base/height ratio;
  4. Cosine and principal-half-tangent identities for the apex angle;
  5. UNIQUENESS of the internal angle in the open interval (0, pi),
     separately by cosine injectivity and by the principal arctangent branch.

A053? NO: the relevant OEIS entry is A073000, for arctan(1/2),
not for the doubled apex angle.

No numerical Arb certificate is necessary: all values preceding the
inverse trigonometric functions are rational and the identities exact.
Isometric axes are an external requirement on the TikZ drawing.
-/

import EulerianCert.Bracket
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

namespace EulerianCert.Figure5Apex

open Real

/-! Eulerian histogram coordinates, precisely as in manuscript 11. -/

def x (n k : ℕ) : ℚ := (k : ℚ) / (n + 1)
def p (n k : ℕ) : ℚ := (Bracket.E n (k - 1) : ℚ) / (n.factorial : ℚ)
def point (n k : ℕ) : ℚ × ℚ := (x n k, p n k)

/-- Exact small Eulerian row, from the already formalized Eulerian recurrence. -/
theorem eulerian_row_three : Bracket.row 3 = [1, 4, 1] := by decide +kernel

private theorem e30 : Bracket.E 3 0 = 1 := by decide +kernel
private theorem e31 : Bracket.E 3 1 = 4 := by decide +kernel
private theorem e32 : Bracket.E 3 2 = 1 := by decide +kernel

/-- Part 1: the three vertices originate in E(3,0)=1, E(3,1)=4, E(3,2)=1. -/
theorem exact_vertices :
    point 3 1 = ((1 / 4 : ℚ), (1 / 6 : ℚ)) ∧
    point 3 2 = ((1 / 2 : ℚ), (2 / 3 : ℚ)) ∧
    point 3 3 = ((3 / 4 : ℚ), (1 / 6 : ℚ)) := by
  constructor
  · norm_num [point, x, p, e30]
  constructor
  · norm_num [point, x, p, e31]
  · norm_num [point, x, p, e32]

def leftVertex : ℚ × ℚ := point 3 1
def topVertex : ℚ × ℚ := point 3 2
def rightVertex : ℚ × ℚ := point 3 3

private theorem left_coords : leftVertex = ((1 / 4 : ℚ), (1 / 6 : ℚ)) :=
  exact_vertices.1
private theorem top_coords : topVertex = ((1 / 2 : ℚ), (2 / 3 : ℚ)) :=
  exact_vertices.2.1
private theorem right_coords : rightVertex = ((3 / 4 : ℚ), (1 / 6 : ℚ)) :=
  exact_vertices.2.2

def subCoords (u v : ℚ × ℚ) : ℚ × ℚ := (u.1 - v.1, u.2 - v.2)
def topToLeft : ℚ × ℚ := subCoords leftVertex topVertex
def topToRight : ℚ × ℚ := subCoords rightVertex topVertex

theorem top_to_left : topToLeft = ((-1 / 4 : ℚ), (-1 / 2 : ℚ)) := by
  norm_num [topToLeft, subCoords, left_coords, top_coords]

theorem top_to_right : topToRight = ((1 / 4 : ℚ), (-1 / 2 : ℚ)) := by
  norm_num [topToRight, subCoords, right_coords, top_coords]

def sqNorm (v : ℚ × ℚ) : ℚ := v.1 ^ 2 + v.2 ^ 2
def dot (u v : ℚ × ℚ) : ℚ := u.1 * v.1 + u.2 * v.2

/-- Both oblique sides have the same (rational) squared length 5/16. -/
theorem equal_squared_lengths :
    sqNorm topToLeft = 5 / 16 ∧ sqNorm topToRight = 5 / 16 := by
  constructor
  · norm_num [sqNorm, top_to_left]
  · norm_num [sqNorm, top_to_right]

noncomputable def euclideanLength (v : ℚ × ℚ) : ℝ :=
  Real.sqrt (sqNorm v : ℝ)

/-- Part 2: equality of the actual Euclidean lengths, not just their squares. -/
theorem equal_side_lengths :
    euclideanLength topToLeft = euclideanLength topToRight := by
  have h := (equal_squared_lengths.1).trans (equal_squared_lengths.2).symm
  unfold euclideanLength
  rw [h]

def halfBase : ℚ := (rightVertex.1 - leftVertex.1) / 2
def altitude : ℚ := topVertex.2 - leftVertex.2

/-- Part 3: the geometric half-base is 1/4 and the altitude is 1/2. -/
theorem half_base_height_ratio :
    halfBase = 1 / 4 ∧ altitude = 1 / 2 ∧ halfBase / altitude = 1 / 2 := by
  have hb : halfBase = 1 / 4 := by
    norm_num [halfBase, right_coords, left_coords]
  have hh : altitude = 1 / 2 := by
    norm_num [altitude, top_coords, left_coords]
  refine ⟨hb, hh, ?_⟩
  rw [hb, hh]
  norm_num

/-- Independent rational dot-product check: 3/16 over 5/16 = 3/5. -/
theorem normalized_dot_product :
    dot topToLeft topToRight / sqNorm topToLeft = 3 / 5 := by
  have hd : dot topToLeft topToRight = 3 / 16 := by
    norm_num [dot, top_to_left, top_to_right]
  rw [hd, equal_squared_lengths.1]
  norm_num

/-! Part 4: the principal half-angle and its cosine. -/

noncomputable def apexAngle : ℝ := 2 * Real.arctan (1 / 2 : ℝ)

/-- The apex angle belongs to the OPEN internal-angle interval (0, pi).
The strict inequalities are vital for branch uniqueness. -/
theorem apex_angle_mem_open_interval :
    0 < apexAngle ∧ apexAngle < Real.pi := by
  have hp : 0 < Real.arctan (1 / 2 : ℝ) :=
    Real.arctan_pos.mpr (by norm_num)
  have hl : Real.arctan (1 / 2 : ℝ) < Real.pi / 2 :=
    Real.arctan_lt_pi_div_two _
  constructor
  · dsimp [apexAngle]
    linarith
  · dsimp [apexAngle]
    linarith

/-- The half-angle has tangent precisely halfBase / altitude = 1/2. -/
theorem tan_half_apex :
    Real.tan (apexAngle / 2) = (1 / 2 : ℝ) := by
  have h : apexAngle / 2 = Real.arctan (1 / 2 : ℝ) := by
    unfold apexAngle
    ring
  rw [h, Real.tan_arctan]

/-- Exact independent trigonometric check: cos(2 arctan(1/2)) = 3/5. -/
theorem cos_apex : Real.cos apexAngle = (3 / 5 : ℝ) := by
  change Real.cos (2 * Real.arctan (1 / 2 : ℝ)) = (3 / 5 : ℝ)
  rw [Real.cos_two_mul]
  simp only [Real.cos_sq_arctan, Real.sin_sq_arctan]
  norm_num

/-! Part 5: two independent statements that rule out branch ambiguity. -/

/-- UNIQUE internal angle from the scalar-product cosine.
Without 0 < phi < pi the cosine equation does not give uniqueness. -/
theorem unique_internal_angle_of_cos
    (phi : ℝ) (hphi0 : 0 < phi) (hphiPi : phi < Real.pi)
    (hcos : Real.cos phi = (3 / 5 : ℝ)) :
    phi = apexAngle := by
  have hphi : phi ∈ Set.Icc (0 : ℝ) Real.pi := ⟨hphi0.le, hphiPi.le⟩
  have hapex : apexAngle ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨apex_angle_mem_open_interval.1.le, apex_angle_mem_open_interval.2.le⟩
  exact Real.injOn_cos hphi hapex (hcos.trans cos_apex.symm)

/-- UNIQUE principal half-angle: 0 < phi < pi implies
-pi/2 < phi/2 < pi/2, the injectivity interval for tan.
Consequently arctan(tan(phi/2)) = phi/2. -/
theorem unique_internal_angle_of_half_tan
    (phi : ℝ) (hphi0 : 0 < phi) (hphiPi : phi < Real.pi)
    (htan : Real.tan (phi / 2) = (1 / 2 : ℝ)) :
    phi = apexAngle := by
  have hlo : -(Real.pi / 2) < phi / 2 := by
    have hpi := Real.pi_pos
    linarith
  have hhi : phi / 2 < Real.pi / 2 := by linarith
  have hprincipal := Real.arctan_tan hlo hhi
  rw [htan] at hprincipal
  unfold apexAngle
  linarith

/-- The arccot notation in the caption is principal arccot on positive reals.
The OEIS entry A073000 concerns *principalArccot 2*, not twice it. -/
noncomputable def principalArccot (z : ℝ) : ℝ := Real.arctan (1 / z)

theorem apex_angle_eq_twice_arccot_two :
    apexAngle = 2 * principalArccot 2 := rfl

end EulerianCert.Figure5Apex
