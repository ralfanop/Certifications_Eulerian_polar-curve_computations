/-
Manuscript 15 — pointwise sharp Lipschitz estimates for the real
Fourier phases used in the Wasserstein-1 stability theorem.

Every statement concerns actual trigonometric functions, with no
external unproved probability lemma. The subsequent integration over
a coupling and minimisation defining W1 are separate obligations.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib

open Real
noncomputable section
namespace Manuscript15

/-- Sharp cosine Fourier-phase transport bound, constant |s|. -/
theorem cosine_phase_lipschitz (s x y : ℝ) :
    |Real.cos (s * x) - Real.cos (s * y)| ≤ |s| * |x - y| := by
  calc
    |Real.cos (s * x) - Real.cos (s * y)| ≤ |s * x - s * y| :=
      Real.abs_cos_sub_cos_le (s * x) (s * y)
    _ = |s| * |x - y| := by
      rw [← mul_sub, abs_mul]

/-- Sharp sine Fourier-phase transport bound, constant |s|. -/
theorem sine_phase_lipschitz (s x y : ℝ) :
    |Real.sin (s * x) - Real.sin (s * y)| ≤ |s| * |x - y| := by
  calc
    |Real.sin (s * x) - Real.sin (s * y)| ≤ |s * x - s * y| :=
      Real.abs_sin_sub_sin_le (s * x) (s * y)
    _ = |s| * |x - y| := by
      rw [← mul_sub, abs_mul]

/-- Coupling distance majorants propagate to real cosine Fourier
    phases by a sharp multiplicative |s|. -/
theorem cosine_phase_coupling_bound (s x y delta : ℝ)
    (hxy : |x - y| ≤ delta) :
    |Real.cos (s * x) - Real.cos (s * y)| ≤ |s| * delta := by
  calc
    _ ≤ |s| * |x - y| := cosine_phase_lipschitz s x y
    _ ≤ |s| * delta := mul_le_mul_of_nonneg_left hxy (abs_nonneg s)

/-- The analogous sharp bound for the sine Fourier phase. -/
theorem sine_phase_coupling_bound (s x y delta : ℝ)
    (hxy : |x - y| ≤ delta) :
    |Real.sin (s * x) - Real.sin (s * y)| ≤ |s| * delta := by
  calc
    _ ≤ |s| * |x - y| := sine_phase_lipschitz s x y
    _ ≤ |s| * delta := mul_le_mul_of_nonneg_left hxy (abs_nonneg s)

#print axioms Manuscript15.cosine_phase_lipschitz
#print axioms Manuscript15.sine_phase_lipschitz
#print axioms Manuscript15.cosine_phase_coupling_bound
#print axioms Manuscript15.sine_phase_coupling_bound

end Manuscript15
