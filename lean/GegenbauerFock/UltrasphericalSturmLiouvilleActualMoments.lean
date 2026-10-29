import GegenbauerFock.UltrasphericalSturmLiouvilleGreenMoments
import GegenbauerFock.UltrasphericalOddVanishing

/-!
# V007 — exact Green moment recurrence of the genuine ultraspherical law

The full, unconditional two-step moment recurrence is derived from
the already certified even-moment beta integration by parts and
odd-moment reflection. This theorem concerns the ACTUAL concrete
Beta-pushforward probability measure, not an abstract moment functional.

The concluding Green coefficient identity gives the real symmetric
monomial matrix entries in degrees >= 2. A domain-aware L²
Sturm–Liouville operator and its self-adjointness are not claimed.
-/

noncomputable section
open MeasureTheory

namespace GegenbauerFock.Ultraspherical

/-- The genuine n-th real monomial moment of the Beta-pushforward law. -/
noncomputable def sturmMoment (lam : ℝ) (n : ℕ) : ℝ :=
  ∫ u : ℝ, u ^ n ∂(measure lam)

theorem sturmMoment_even (lam : ℝ) (k : ℕ) :
    sturmMoment lam (2 * k) = evenMoment lam k := rfl

theorem sturmMoment_odd (lam : ℝ) (k : ℕ) :
    sturmMoment lam (2 * k + 1) = oddMoment lam k := rfl

/-- Genuine all-degree two-step ultraspherical moment recurrence.
It is proved separately in the even and odd cases. -/
theorem sturmMoment_two_step (lam : ℝ) (hlam : 0 < lam) (n : ℕ) :
    (((n + 2 : ℕ) : ℝ) + 2 * lam) * sturmMoment lam (n + 2) =
      (((n + 1 : ℕ) : ℝ)) * sturmMoment lam n := by
  obtain ⟨k, hk⟩ :
      ∃ k : ℕ, n = 2 * k ∨ n = 2 * k + 1 :=
    ⟨n / 2, by omega⟩
  rcases hk with hk | hk
  · subst n
    have hden : ((k : ℝ) + lam + 1) ≠ 0 := by positivity
    have hrec :
        evenMoment lam (k + 1) * ((k : ℝ) + lam + 1) =
          evenMoment lam k * ((k : ℝ) + 1 / 2) :=
      (eq_div_iff hden).mp (evenMoment_recurrence lam hlam k)
    rw [show 2 * k + 2 = 2 * (k + 1) by omega,
      sturmMoment_even, sturmMoment_even]
    push_cast
    linear_combination 2 * hrec
  · subst n
    have hidx : 2 * k + 1 + 2 = 2 * (k + 1) + 1 := by omega
    rw [hidx, sturmMoment_odd, sturmMoment_odd]
    rw [oddMoment_eq_zero lam hlam (k + 1),
      oddMoment_eq_zero lam hlam k]
    ring

/-- The high-degree monomial Green identity holds for the actual
Beta-pushforward law, using its proved moment recurrence. -/
theorem sturmMoment_green_high_monomials
    (lam : ℝ) (hlam : 0 < lam) (a b : ℕ) :
    (((a + 2 : ℕ) : ℝ) * ((a + 1 : ℕ) : ℝ)) *
        sturmMoment lam (a + b + 2) -
      (((a + 2 : ℕ) : ℝ) * (((a + 2 : ℕ) : ℝ) + 2 * lam)) *
        sturmMoment lam (a + b + 4) =
    (((b + 2 : ℕ) : ℝ) * ((b + 1 : ℕ) : ℝ)) *
        sturmMoment lam (a + b + 2) -
      (((b + 2 : ℕ) : ℝ) * (((b + 2 : ℕ) : ℝ) + 2 * lam)) *
        sturmMoment lam (a + b + 4) := by
  apply green_high_monomials lam (sturmMoment lam) a b
  convert sturmMoment_two_step lam hlam (a + b + 2) using 1 <;>
    push_cast <;> ring

#print axioms GegenbauerFock.Ultraspherical.sturmMoment_two_step
#print axioms GegenbauerFock.Ultraspherical.sturmMoment_green_high_monomials

end GegenbauerFock.Ultraspherical
