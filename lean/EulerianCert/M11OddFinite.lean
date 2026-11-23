import EulerianCert.Bracket

/-!
Manuscript 11, frozen 23 November 2026: Remark 3.16.
Every finite odd-index comparison 5, 7, ..., 1001 is a kernel-checked integer
comparison, using the same Eulerian recurrence as the original manuscript.
No FLINT/Arb, no native_decide, no sorry and no extra axioms.
-/

namespace EulerianCert.M11OddFinite

/-- The central Eulerian-number difference in the inverse-slope formula. -/
noncomputable def centralGap (n : ℕ) : ℕ :=
  Bracket.E n ((n - 1) / 2) - Bracket.E n (((n - 1) / 2) - 1)

/-- The strict rise `c_n < c_(n+2)` is equivalent to the last natural-number
inequality once the central gaps are positive. -/
def oddStep (j : ℕ) : Prop :=
  let n := 5 + 2 * j
  0 < centralGap n ∧
  0 < centralGap (n + 2) ∧
  (n + 3) * centralGap (n + 2) < (n + 2) * (n + 1) ^ 2 * centralGap n

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
/-- All 498 exact comparisons; the Lean kernel checks the decidable proof. -/
theorem all_odd_steps : ∀ j : Fin 498, oddStep j.val := by
  decide +kernel

/-- Algebraic equivalence of the exact integer inequality and the strict
increase in the actual real inverse slope, for positive central differences. -/
private theorem cn_step_of_nat (n k : ℕ)
    (h1 : Bracket.E n (k - 1) < Bracket.E n k)
    (h2 : Bracket.E (n + 2) k < Bracket.E (n + 2) (k + 1))
    (hI : (n + 3) * (Bracket.E (n + 2) (k + 1) - Bracket.E (n + 2) k) <
          (n + 2) * (n + 1) ^ 2 * (Bracket.E n k - Bracket.E n (k - 1))) :
    Bracket.cn n k < Bracket.cn (n + 2) (k + 1) := by
  let d1 : ℕ := Bracket.E n k - Bracket.E n (k - 1)
  let d2 : ℕ := Bracket.E (n + 2) (k + 1) - Bracket.E (n + 2) k
  have hd1 : 0 < d1 := by dsimp [d1]; omega
  have hd2 : 0 < d2 := by dsimp [d2]; omega
  have hdiff1 : (Bracket.E n k : ℝ) - Bracket.E n (k - 1) = (d1 : ℝ) := by
    simp [d1, Nat.cast_sub h1.le]
  have hdiff2 : (Bracket.E (n + 2) (k + 1) : ℝ) - Bracket.E (n + 2) k = (d2 : ℝ) := by
    simp [d2, Nat.cast_sub h2.le]
  have hfNat : (n + 2).factorial = (n + 2) * (n + 1) * n.factorial := by
    rw [show n + 2 = (n + 1) + 1 by omega, Nat.factorial_succ, Nat.factorial_succ]
    ring
  have hf : ((n + 2).factorial : ℝ) = ((n : ℝ) + 2) * ((n : ℝ) + 1) * (n.factorial : ℝ) := by
    exact_mod_cast hfNat
  have hcast : ((n : ℝ) + 3) * (d2 : ℝ) <
      ((n : ℝ) + 2) * ((n : ℝ) + 1) ^ 2 * (d1 : ℝ) := by
    exact_mod_cast hI
  have hnfac : 0 < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hc : (n.factorial : ℝ) * (((n : ℝ) + 3) * (d2 : ℝ)) <
      ((n + 2).factorial : ℝ) * (((n : ℝ) + 1) * (d1 : ℝ)) := by
    calc
      _ < (n.factorial : ℝ) * (((n : ℝ) + 2) * ((n : ℝ) + 1) ^ 2 * (d1 : ℝ)) :=
        mul_lt_mul_of_pos_left hcast hnfac
      _ = _ := by rw [hf]; ring
  have hp1 : 0 < ((n : ℝ) + 1) * (d1 : ℝ) :=
    mul_pos (by positivity) (by exact_mod_cast hd1)
  have hp2 : 0 < (((n + 2 : ℕ) : ℝ) + 1) * (d2 : ℝ) :=
    mul_pos (by positivity) (by exact_mod_cast hd2)
  have hdiv : (n.factorial : ℝ) / (((n : ℝ) + 1) * (d1 : ℝ)) <
      ((n + 2).factorial : ℝ) / ((((n + 2 : ℕ) : ℝ) + 1) * (d2 : ℝ)) := by
    apply (div_lt_div_iff₀ hp1 hp2).mpr
    convert hc using 1 <;> push_cast <;> ring
  simpa [Bracket.cn, hdiff1, hdiff2] using hdiv

/-- The literal strict-monotonicity assertion of Remark 3.16:
`c_5 < c_7 < ... < c_1001`, with the indexing of the original text. -/
theorem odd_inverse_slopes_strictly_increasing (j : Fin 498) :
    Bracket.cn (5 + 2 * j.val) (((5 + 2 * j.val) - 1) / 2) <
      Bracket.cn (7 + 2 * j.val) (((7 + 2 * j.val) - 1) / 2) := by
  let n : ℕ := 5 + 2 * j.val
  let k : ℕ := (n - 1) / 2
  have hk : ((n + 2) - 1) / 2 = k + 1 := by dsimp [k, n]; omega
  obtain ⟨h1, h2, hI⟩ := all_odd_steps j
  change 0 < Bracket.E n k - Bracket.E n (k - 1) at h1
  change 0 < Bracket.E (n + 2) (((n + 2) - 1) / 2) -
    Bracket.E (n + 2) ((((n + 2) - 1) / 2) - 1) at h2
  rw [hk, Nat.add_sub_cancel] at h2
  change (n + 3) * (Bracket.E (n + 2) (((n + 2) - 1) / 2) -
    Bracket.E (n + 2) ((((n + 2) - 1) / 2) - 1)) <
    (n + 2) * (n + 1) ^ 2 * (Bracket.E n k - Bracket.E n (k - 1)) at hI
  rw [hk, Nat.add_sub_cancel] at hI
  have he1 : Bracket.E n (k - 1) < Bracket.E n k := by omega
  have he2 : Bracket.E (n + 2) k < Bracket.E (n + 2) (k + 1) := by omega
  have result := cn_step_of_nat n k he1 he2 hI
  have hresult : Bracket.cn n k < Bracket.cn (n + 2) (((n + 2) - 1) / 2) := by
    simpa only [hk] using result
  convert hresult using 1 <;> congr 1 <;> dsimp [n, k] <;> omega

end EulerianCert.M11OddFinite
