import Mathlib

/-!
# V007: exponential coherent sections as actual elements of L²

For an arbitrary finite measure on ℝ, the clamped exponential coherentSection
    u ↦ exp(i*z*clamp(u)/2)
is a genuinely bounded continuous function, hence a member of L².

For the ultraspherical beta-pushforward νλ, the clamp agrees with u
on [-1,1]. Identifying this concrete L² coherentSection with the original
unclamped exp(i*z*u/2) almost everywhere requires an additional
support theorem for νλ; it is not claimed here.
-/

open MeasureTheory

namespace GegenbauerFock.CoherentL2

/-- Real unit-interval clamp (the ordinary identity on [-1,1]). -/
noncomputable def clamp (u : ℝ) : ℝ := max (-1) (min u 1)

theorem clamp_abs_le_one (u : ℝ) : |clamp u| ≤ 1 := by
  have hlo : (-1 : ℝ) ≤ clamp u := by
    unfold clamp
    exact le_max_left _ _
  have hhi : clamp u ≤ 1 := by
    unfold clamp
    exact max_le (by norm_num) (min_le_right _ _)
  exact abs_le.mpr ⟨by linarith, hhi⟩

theorem continuous_clamp : Continuous clamp := by
  unfold clamp
  fun_prop

/-- Globally bounded, pointwise analytic Fourier coherent coherentSection. -/
noncomputable def coherentSection (z : ℂ) (u : ℝ) : ℂ :=
  Complex.exp (Complex.I * z * (clamp u : ℂ) / 2)

theorem continuous_section (z : ℂ) : Continuous (coherentSection z) := by
  unfold coherentSection
  fun_prop

theorem section_bound (z : ℂ) (u : ℝ) :
    ‖coherentSection z u‖ ≤ Real.exp (‖z‖ / 2) := by
  have hclamp : ‖(clamp u : ℂ)‖ ≤ 1 := by
    simpa using clamp_abs_le_one u
  have harg :
      ‖Complex.I * z * (clamp u : ℂ) / 2‖ ≤ ‖z‖ / 2 := by
    calc
      ‖Complex.I * z * (clamp u : ℂ) / 2‖ =
          ‖z‖ * ‖(clamp u : ℂ)‖ / 2 := by
            simp [norm_div, norm_mul, mul_comm, mul_left_comm, mul_assoc]
      _ ≤ ‖z‖ * 1 / 2 := by gcongr
      _ = ‖z‖ / 2 := by ring
  unfold coherentSection
  exact (Complex.norm_exp_le_exp_norm _).trans
    (Real.exp_le_exp.mpr harg)

/-- Genuine L² integrability, using the finite-measure theorem
for bounded measurable functions. -/
theorem section_memLp (μ : Measure ℝ) [IsFiniteMeasure μ] (z : ℂ) :
    MemLp (coherentSection z) 2 μ := by
  exact MemLp.of_bound
    (continuous_section z).aestronglyMeasurable
    (Real.exp (‖z‖ / 2))
    (Filter.Eventually.of_forall (section_bound z))

/-- A concrete L² equivalence class for each complex frequency z. -/
noncomputable def sectionLp (μ : Measure ℝ) [IsFiniteMeasure μ] (z : ℂ) :
    Lp ℂ 2 μ :=
  (section_memLp μ z).toLp (coherentSection z)

#print axioms GegenbauerFock.CoherentL2.clamp_abs_le_one
#print axioms GegenbauerFock.CoherentL2.continuous_section
#print axioms GegenbauerFock.CoherentL2.section_bound
#print axioms GegenbauerFock.CoherentL2.section_memLp

end GegenbauerFock.CoherentL2
