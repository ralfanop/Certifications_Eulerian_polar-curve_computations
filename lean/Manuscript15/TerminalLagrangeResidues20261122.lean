import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic

/-! M15 §6.2: the algebraic residue route, independent of analytic composition.
This module does not assume a residue substitution or an inversion theorem. -/
namespace M15TerminalLagrangeResidues

open HahnSeries

abbrev L := LaurentSeries ℝ
abbrev P := PowerSeries ℝ

noncomputable def D : L →ₗ[ℝ] L := LaurentSeries.derivative ℝ
def residue (f : L) : ℝ := f.coeff (-1)

/-- Laurent derivative, including the negative powers. -/
theorem derivative_coeff (f : L) (j : ℤ) :
    (D f).coeff j = ((j + 1 : ℤ) : ℝ) * f.coeff (j + 1) := by
  simp [D, Ring.choose_one_right, zsmul_eq_mul]

/-- Formal derivative has no residue (no convergence hypothesis). -/
theorem residue_derivative (f : L) : residue (D f) = 0 := by
  rw [residue, derivative_coeff]
  norm_num

theorem residue_add (f g : L) :
    residue (f + g) = residue f + residue g := by
  simp [residue, HahnSeries.coeff_add', Pi.add_apply]

/-- Extract any coefficient of an embedded formal power series by a residue. -/
theorem residue_extract (f : P) (n : ℕ) :
    residue (HahnSeries.single (-(n : ℤ) - 1) (1 : ℝ) * (f : L)) =
      PowerSeries.coeff n f := by
  rw [residue, HahnSeries.coeff_single_mul, one_mul]
  have h : (-1 : ℤ) - (-(n : ℤ) - 1) = (n : ℤ) := by omega
  rw [h]
  exact LaurentSeries.coeff_coe_powerSeries f n

/-- Differentiation of a monomial times an arbitrary Laurent series. -/
theorem derivative_single_mul (k : ℤ) (a : ℝ) (f : L) :
    D (HahnSeries.single k a * f) =
      HahnSeries.single (k - 1) ((k : ℝ) * a) * f +
        HahnSeries.single k a * D f := by
  ext j
  simp only [derivative_coeff, HahnSeries.coeff_single_mul, HahnSeries.coeff_add',
    Pi.add_apply]
  have h₁ : j - (k - 1) = j + 1 - k := by omega
  have h₂ : j - k + 1 = j + 1 - k := by omega
  rw [h₁, h₂]
  push_cast
  ring

/-- The Laurent derivative extends the formal power series derivative. -/
theorem derivative_coe (f : P) :
    D (f : L) = ((PowerSeries.derivative (R := ℝ) f : P) : L) := by
  ext j
  by_cases hj : 0 ≤ j
  · lift j to ℕ using hj
    rw [derivative_coeff]
    have h : (j : ℤ) + 1 = ((j + 1 : ℕ) : ℤ) := by omega
    rw [h, LaurentSeries.coeff_coe_powerSeries, LaurentSeries.coeff_coe_powerSeries,
      PowerSeries.coeff_derivative]
    push_cast
    ring
  · by_cases h : j = -1
    · subst j
      rw [derivative_coeff]
      simp [PowerSeries.coeff_coe]
    · have hj' : j < 0 := by omega
      have hnext : j + 1 < 0 := by omega
      rw [derivative_coeff, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
      simp [hj', hnext]

/-- Multiplication of the two monomial factors in the Laurent product rule. -/
theorem monomial_derivative_split (m n : ℤ) :
    (HahnSeries.single (m + n - 1) (((m + n : ℤ) : ℝ) * 1) : L) =
      HahnSeries.single (m - 1) ((m : ℝ) * 1) * HahnSeries.single n 1 +
      HahnSeries.single m 1 * HahnSeries.single (n - 1) ((n : ℝ) * 1) := by
  simp only [HahnSeries.single_mul_single, mul_one, one_mul]
  have h₁ : m - 1 + n = m + n - 1 := by omega
  have h₂ : m + (n - 1) = m + n - 1 := by omega
  rw [h₁, h₂]
  ext j
  simp only [HahnSeries.coeff_single, HahnSeries.coeff_add', Pi.add_apply]
  split <;> push_cast <;> ring

/-- Full Leibniz identity on genuine Laurent series, by their monomial factorization. -/
theorem derivative_mul (f g : L) : D (f * g) = D f * g + f * D g := by
  obtain ⟨m, p, rfl⟩ : ∃ (m : ℤ) (p : P),
      f = HahnSeries.single m 1 * (p : L) :=
    ⟨f.order, f.powerSeriesPart, (LaurentSeries.single_order_mul_powerSeriesPart f).symm⟩
  obtain ⟨n, q, rfl⟩ : ∃ (n : ℤ) (q : P),
      g = HahnSeries.single n 1 * (q : L) :=
    ⟨g.order, g.powerSeriesPart, (LaurentSeries.single_order_mul_powerSeriesPart g).symm⟩
  have hm : (HahnSeries.single m 1 : L) * HahnSeries.single n 1 =
      HahnSeries.single (m+n) 1 := by simp
  have hp : (HahnSeries.single m 1 * (p : L)) *
      (HahnSeries.single n 1 * (q : L)) =
        HahnSeries.single (m+n) 1 * ((p*q : P) : L) := by
    rw [PowerSeries.coe_mul, ← hm]
    ring
  have hDpq : D ((p : L) * (q : L)) =
      (p : L) * (((PowerSeries.derivative (R := ℝ) q : P) : L)) +
        (q : L) * (((PowerSeries.derivative (R := ℝ) p : P) : L)) := by
    rw [← PowerSeries.coe_mul, derivative_coe,
      (PowerSeries.derivative (R := ℝ)).leibniz]
    simp only [PowerSeries.coe_add, PowerSeries.coe_mul, smul_eq_mul]
  simp only [hp, derivative_single_mul, derivative_coe,
    PowerSeries.coe_add, PowerSeries.coe_mul]
  rw [hDpq, monomial_derivative_split, ← hm]
  ring

/-- Residue integration by parts, for arbitrary Laurent series. -/
theorem residue_integration_by_parts (f g : L) :
    residue (D f * g) + residue (f * D g) = 0 := by
  rw [← residue_add, ← derivative_mul, residue_derivative]

/-- The Laurent derivative is a derivation over the real scalars. -/
noncomputable def formalDerivation : Derivation ℝ L L :=
  Derivation.mk'
    { toFun := fun f => D f
      map_add' := by
        intro f g
        exact D.map_add f g
      map_smul' := by
        intro r f
        simpa only [smul_eq_mul] using D.map_smul r f }
    (by
      intro f g
      change D (f * g) = f • D g + g • D f
      simpa only [smul_eq_mul, mul_comm, add_comm] using derivative_mul f g)

/-- Integer-power rule, valid also for negative exponents. -/
theorem derivative_zpow (f : L) (k : ℤ) :
    D (f ^ k) = (k : L) * f ^ (k - 1) * D f := by
  simpa [formalDerivation, zsmul_eq_mul, smul_eq_mul, mul_assoc] using
    (formalDerivation.leibniz_zpow f k)

/-- The algebraic integration-by-parts step in Lagrange–Bürmann, every positive order.
The change-of-variable identity is a separate next theorem. -/
theorem residue_lagrange_by_parts (g f : L) (n : ℕ) :
    residue (D g * f ^ (-(n : ℤ))) =
      (n : ℝ) * residue (g * ((f ^ (-(n : ℤ) - 1)) * D f)) := by
  have h := residue_integration_by_parts g (f ^ (-(n : ℤ)))
  rw [derivative_zpow] at h
  -- Move a scalar through residue using the Hahn series coefficient map.
  have hmul : g * ((-(n : ℤ) : L) * f ^ (-(n : ℤ) - 1) * D f) =
      -((n : ℕ) • (g * (f ^ (-(n : ℤ) - 1) * D f))) := by
    push_cast
    rw [nsmul_eq_mul]
    ring
  simp only [Int.cast_neg, Int.cast_natCast] at h
  rw [hmul] at h
  have hneg : residue (-(n • (g * (f ^ (-(n : ℤ) - 1) * D f)))) =
      -(n : ℝ) * residue (g * (f ^ (-(n : ℤ) - 1) * D f)) := by
    simp [residue, HahnSeries.coeff_neg, HahnSeries.coeff_nsmul, Pi.smul_apply,
      nsmul_eq_mul]
  rw [hneg] at h
  linarith

#print axioms derivative_coeff
#print axioms residue_derivative
#print axioms residue_extract
#print axioms derivative_single_mul
#print axioms derivative_coe
#print axioms derivative_mul
#print axioms residue_integration_by_parts
#print axioms derivative_zpow
#print axioms residue_lagrange_by_parts

end M15TerminalLagrangeResidues
