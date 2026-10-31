import GegenbauerFock.UltrasphericalSturmLiouvilleResolventMultiplierDecay

/-!
# V007 — monotonicity and uniform scalar tails of true Sturm multipliers

These are precise scalar inequalities for the complete normalized
Gegenbauer spectral coefficients of the genuine positive closed
Sturm resolvent. They are a prerequisite for the uniform *operator*
tail estimate, which must additionally use Parseval and the finite
rank coordinate identities.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

/-- The positive-shift resolvent multiplier decreases with the
Gegenbauer polynomial degree, for all positive λ and t. -/
theorem sturmResolventMultiplier_antitone
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    Antitone (fun n : ℕ =>
      (t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹) := by
  intro n m hnm
  have hcast : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
  have hmult :
      (n : ℝ) * ((n : ℝ) + 2 * lam) ≤
      (m : ℝ) * ((m : ℝ) + 2 * lam) :=
    mul_le_mul hcast (by linarith) (by positivity) (by positivity)
  have hden : 0 < t + (n : ℝ) * ((n : ℝ) + 2 * lam) :=
    inv_pos.mp (sturmResolventMultiplier_pos lam t hlam ht n)
  have h := one_div_le_one_div_of_le hden (add_le_add_left hmult t)
  simpa only [one_div] using h

/-- All scalar multipliers past degree N are bounded by the first
omitted multiplier, with no parameter-dependent constant loss. -/
theorem sturmResolventMultiplier_tail_le
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (N n : ℕ) (hn : N ≤ n) :
    (t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹ ≤
      (t + (N : ℝ) * ((N : ℝ) + 2 * lam))⁻¹ :=
  sturmResolventMultiplier_antitone lam t hlam ht hn

#print axioms GegenbauerFock.Ultraspherical.sturmResolventMultiplier_antitone
#print axioms GegenbauerFock.Ultraspherical.sturmResolventMultiplier_tail_le

end GegenbauerFock.Ultraspherical
