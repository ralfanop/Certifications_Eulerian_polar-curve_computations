import GegenbauerFock.GegenbauerIntrinsicEntireHSRealGammaIntegral
import GegenbauerFock.RationalTraceAnalyticTail

/-!
# V007 — exact rational numerical enclosure of genuine Gaussian Fock S₂ energy

Combines the separately kernel-checked fifteen-term infinite Taylor
remainder with the actual, basis-independent Hilbert–Schmidt energy
of the intrinsic entire Gaussian Bargmann–Fock Gegenbauer transform.
The inequalities hold for EVERY Hilbert source basis, not merely
for an abstract coefficient model or a single finite matrix.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

private abbrev LegendreH :=
  Lp ℂ 2 (Ultraspherical.measure (1 / 2))

/-- For every complete orthonormal basis of the actual complex
ultraspherical L², the squared S₂ energy is the Eulerian integral
already enclosed by the exact-rational Lean theorem. -/
theorem C_intrinsicEntire_HS_energy_legendre_eq_integral
    {ι : Type*} (b : HilbertBasis ι ℂ LegendreH) :
    (∑' i : ι,
        ‖C_intrinsicEntire (1 / 2) 1 (by norm_num) (by norm_num) (b i)‖ ^ 2) =
      ∫ u : ℝ, Real.exp (u ^ 2 / 4)
        ∂(Ultraspherical.measure (1 / 2)) := by
  have h :=
    C_intrinsicEntire_HS_energy_eq_kummer
      (1 / 2) 1 (by norm_num) (by norm_num) b
  have hint :=
    exp_integral_eq_kummerSeries
      (1 / 2) 1 (by norm_num) (by norm_num)
  have heq := h.trans hint.symm
  simpa only [mul_one] using heq

/-- Fully certified, 24-decimal strict rational interval for the
Hilbert–Schmidt squared energy of the actual Fock-valued transform. -/
theorem C_intrinsicEntire_HS_energy_legendre_decimal_enclosure
    {ι : Type*} (b : HilbertBasis ι ℂ LegendreH) :
    ((1089974208367244447324816 : ℝ) / 10^24) <
       (∑' i : ι,
         ‖C_intrinsicEntire (1 / 2) 1 (by norm_num) (by norm_num) (b i)‖ ^ 2) ∧
       (∑' i : ι,
         ‖C_intrinsicEntire (1 / 2) 1 (by norm_num) (by norm_num) (b i)‖ ^ 2) <
       ((1089974208367244447325767 : ℝ) / 10^24) := by
  rw [C_intrinsicEntire_HS_energy_legendre_eq_integral b]
  exact RationalTrace.legendre_exp_integral_decimal_enclosure

/-- The source Gram's genuine complete-Hilbert-basis diagonal trace
has exactly the same real-line normalized Eulerian integral. -/
theorem C_intrinsicEntire_Gram_trace_legendre_eq_integral
    {ι : Type*} (b : HilbertBasis ι ℂ LegendreH) :
    (∑' i : ι,
      RCLike.re (inner ℂ
        (C_intrinsicEntire_gram (1 / 2) 1 (by norm_num) (by norm_num) (b i))
          (b i))) =
      ∫ u : ℝ, Real.exp (u ^ 2 / 4)
        ∂(Ultraspherical.measure (1 / 2)) := by
  have h :=
    C_intrinsicEntire_Gram_basis_trace_eq_kummer
      (1 / 2) 1 (by norm_num) (by norm_num) b
  have hint :=
    exp_integral_eq_kummerSeries
      (1 / 2) 1 (by norm_num) (by norm_num)
  have heq := h.trans hint.symm
  simpa only [mul_one] using heq

/-- Strict rational enclosure for the actual intrinsic Gaussian Fock
source-Gram basis trace (all complete source bases). -/
theorem C_intrinsicEntire_Gram_trace_legendre_decimal_enclosure
    {ι : Type*} (b : HilbertBasis ι ℂ LegendreH) :
    ((1089974208367244447324816 : ℝ) / 10^24) <
      (∑' i : ι,
        RCLike.re (inner ℂ
          (C_intrinsicEntire_gram (1 / 2) 1 (by norm_num) (by norm_num) (b i))
            (b i))) ∧
      (∑' i : ι,
        RCLike.re (inner ℂ
          (C_intrinsicEntire_gram (1 / 2) 1 (by norm_num) (by norm_num) (b i))
            (b i))) <
      ((1089974208367244447325767 : ℝ) / 10^24) := by
  rw [C_intrinsicEntire_Gram_trace_legendre_eq_integral b]
  exact RationalTrace.legendre_exp_integral_decimal_enclosure

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_HS_energy_legendre_eq_integral
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_HS_energy_legendre_decimal_enclosure
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_Gram_trace_legendre_eq_integral
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_Gram_trace_legendre_decimal_enclosure

end GegenbauerFock.GeneralUltrasphericalFock
