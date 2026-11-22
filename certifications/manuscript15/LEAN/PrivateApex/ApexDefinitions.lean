import PrivateApex.GlobalApex

/-!
PRIVATE.  Manuscript 15, Definition 7.3: central slopes, real vertices and virtual apex.

Self-contained definitions, stated directly from the Eulerian numbers `E n k`, of

* the isometric profile: the vertices `(profX n k, profY n k)`, `1 ≤ k ≤ n`;
* `sOdd m = s_n` for `n = 2m + 1` and `tEven m = t_n` for `n = 2m`;
* the interior angle `realApexAngle` at the real apex (odd `n`), the interior angle
  `plateauAngle` at each real vertex of the central plateau (even `n`), and the interior angle
  `virtualApexAngle` at the virtual apex (even `n`), whose height is `virtualApexHeight`;
* the unified angle `alphaVirt n`.

The lemmas identify these objects with the quantities used in the certified proof
(`slopeQ`, `virtualApex`), check that `sOdd` and `tEven` are the slopes of the central edges,
that the two extended edges meet at the virtual apex, and restate Theorem 7.3 in terms of
`alphaVirt`.
-/

namespace PrivateApex
open Real
open EulerianCert.Bracket

/-- Abscissa `k / (n + 1)` of the `k`-th vertex of the profile of order `n`. -/
def profX (n k : ℕ) : ℚ := (k : ℚ) / (n + 1)

/-- Ordinate `E(n, k-1) / n!` of the `k`-th vertex of the profile of order `n`. -/
noncomputable def profY (n k : ℕ) : ℚ := (E n (k - 1) : ℚ) / n.factorial

/-- `s_n` for odd `n = 2m + 1`. -/
noncomputable def sOdd (m : ℕ) : ℚ :=
  ((2 * m + 1 : ℕ) + 1 : ℚ) * ((E (2 * m + 1) m : ℚ) - E (2 * m + 1) (m - 1)) /
    (2 * m + 1).factorial

/-- `t_n` for even `n = 2m`. -/
noncomputable def tEven (m : ℕ) : ℚ :=
  ((2 * m : ℕ) + 1 : ℚ) * ((E (2 * m) (m - 1) : ℚ) - E (2 * m) (m - 2)) / (2 * m).factorial

/-- Interior angle `α_n = 2 arccot(s_n)` at the real apex, `n = 2m + 1`. -/
noncomputable def realApexAngle (m : ℕ) : ℝ := 2 * arctan (1 / ((sOdd m : ℚ) : ℝ))

/-- Interior angle `α_n = π - arctan(t_n)` at each real vertex of the plateau, `n = 2m`. -/
noncomputable def plateauAngle (m : ℕ) : ℝ := π - arctan ((tEven m : ℚ) : ℝ)

/-- Interior angle `α_n^virt = 2 arccot(t_n)` at the virtual apex, `n = 2m`. -/
noncomputable def virtualApexAngle (m : ℕ) : ℝ := 2 * arctan (1 / ((tEven m : ℚ) : ℝ))

/-- Height of the virtual apex above the axis, `n = 2m`; its abscissa is `1/2`. -/
noncomputable def virtualApexHeight (m : ℕ) : ℚ := profY (2 * m) m + tEven m / (2 * ((2 * m : ℕ) + 1))

/-- The angle `α_n^virt` of Definition 7.3 for every order. -/
noncomputable def alphaVirt (n : ℕ) : ℝ :=
  if n % 2 = 1 then realApexAngle (n / 2) else virtualApexAngle (n / 2)

/-! ### Identification with the certified quantities -/

theorem sOdd_eq (m : ℕ) : sOdd m = slopeQ (2 * m + 1) := (slopeQ_odd m).symm

theorem tEven_eq {m : ℕ} (hm : 1 ≤ m) : tEven m = slopeQ (2 * m) := (slopeQ_even hm).symm

theorem alphaVirt_eq (n : ℕ) (hn : 2 ≤ n) : alphaVirt n = virtualApex n := by
  unfold alphaVirt virtualApex
  split_ifs with h
  · have hn' : 2 * (n / 2) + 1 = n := by omega
    unfold realApexAngle
    rw [sOdd_eq, hn']
  · have hn' : 2 * (n / 2) = n := by omega
    have hm : 1 ≤ n / 2 := by omega
    unfold virtualApexAngle
    rw [tEven_eq hm, hn']

/-! ### Geometry of the profile -/

theorem profX_step (n k : ℕ) : profX n (k + 1) - profX n k = 1 / ((n : ℚ) + 1) := by
  unfold profX
  push_cast
  ring

/-- The real apex of an odd profile lies on the axis `x = 1/2`. -/
theorem profX_apex (m : ℕ) : profX (2 * m + 1) (m + 1) = 1 / 2 := by
  unfold profX
  push_cast
  field_simp
  ring

/-- `s_n` is the slope of the edge ending at the real apex. -/
theorem sOdd_is_slope (m : ℕ) :
    sOdd m = (profY (2 * m + 1) (m + 1) - profY (2 * m + 1) m) /
      (profX (2 * m + 1) (m + 1) - profX (2 * m + 1) m) := by
  rw [profX_step]
  unfold sOdd profY
  rw [Nat.add_sub_cancel]
  push_cast
  field_simp

/-- `t_n` is the slope of the edge ending at the left real vertex of the plateau. -/
theorem tEven_is_slope (k : ℕ) :
    tEven (k + 1) = (profY (2 * (k + 1)) (k + 1) - profY (2 * (k + 1)) k) /
      (profX (2 * (k + 1)) (k + 1) - profX (2 * (k + 1)) k) := by
  rw [profX_step]
  unfold tEven profY
  rw [Nat.add_sub_cancel, show k + 1 - 2 = k - 1 by omega]
  push_cast
  field_simp

/-- The two real vertices of the plateau have the same ordinate. -/
theorem plateau_level {m : ℕ} (hm : 1 ≤ m) : profY (2 * m) (m + 1) = profY (2 * m) m := by
  unfold profY
  rw [Nat.add_sub_cancel, E_even_central_symm hm]

/-- The line through the left real vertex with slope `t_n` and the line through the right
real vertex with slope `-t_n` both pass through the virtual apex `(1/2, virtualApexHeight)`. -/
theorem virtual_apex_point {m : ℕ} (hm : 1 ≤ m) :
    profY (2 * m) m + tEven m * (1 / 2 - profX (2 * m) m) = virtualApexHeight m ∧
    profY (2 * m) (m + 1) - tEven m * (1 / 2 - profX (2 * m) (m + 1)) = virtualApexHeight m := by
  rw [plateau_level hm]
  unfold virtualApexHeight profX
  constructor
  · push_cast
    field_simp
    ring
  · push_cast
    field_simp
    ring

/-- `α_n^virt = 2 α_n - π` for even `n = 2m ≥ 4`. -/
theorem virtualApexAngle_eq {m : ℕ} (hm : 2 ≤ m) :
    virtualApexAngle m = 2 * plateauAngle m - π := by
  have hpos : (0 : ℝ) < ((tEven m : ℚ) : ℝ) := by
    rw [tEven_eq (by omega)]
    exact_mod_cast (slopeQ_classification (2 * m) (by omega)).1
  unfold virtualApexAngle plateauAngle
  rw [one_div, arctan_inv_of_pos hpos]
  ring

/-! ### Theorem 7.3 in terms of Definition 7.3 -/

/-- The minimum of `α_n^virt` over all orders `n ≥ 3` is attained only at `n = 12`. -/
theorem alphaVirt_unique_min (n : ℕ) (hn : 3 ≤ n) (h12 : n ≠ 12) :
    alphaVirt 12 < alphaVirt n := by
  rw [alphaVirt_eq 12 (by norm_num), alphaVirt_eq n (by omega)]
  exact virtualApex_unique_min n hn h12

/-- `α₁₂^virt = 2 arccot(9473633/3628800)`. -/
theorem alphaVirt_twelve : alphaVirt 12 = 2 * arctan (3628800 / 9473633) := by
  rw [alphaVirt_eq 12 (by norm_num)]
  exact virtualApex_twelve

theorem alphaVirt_three : alphaVirt 3 = 2 * arctan (1 / 2) := by
  have h : slopeQ 3 = 2 := (slopeQ_classification 3 le_rfl).2.2.2.2.mpr (Or.inl rfl)
  rw [alphaVirt_eq 3 (by norm_num)]
  unfold virtualApex
  rw [h]
  norm_num

/-- Exact threshold against the exceptional odd-order angle `α₃ = α₅`. -/
theorem alphaVirt_threshold (n : ℕ) (hn : 3 ≤ n) :
    (alphaVirt n < alphaVirt 3 ↔ Even n ∧ n ≤ 48) ∧
    (alphaVirt n = alphaVirt 3 ↔ n = 3 ∨ n = 5) ∧
    (alphaVirt 3 < alphaVirt n ↔ ¬ (Even n ∧ n ≤ 48) ∧ ¬ (n = 3 ∨ n = 5)) := by
  rw [alphaVirt_three, alphaVirt_eq n (by omega)]
  exact virtualApex_threshold n hn

end PrivateApex
