import SpecialImaginaryPoint.EulerianLegendreAnisotropic

/-! M14.120 Proposition 11.1: identify the manuscript's normalized
Legendre supremum with the previously certified actual normalized rate.
Equality of ranges avoids any boundedness assumption on the supremum. -/
namespace M14.EulerianLegendre
noncomputable section

def manuscriptRate (s : ℝ) : ℝ :=
  sSup (Set.range (fun h : ℝ => s*h - cumulant (Real.sqrt 3*h)))

theorem normalizedRate_eq_manuscriptRate (s : ℝ) :
    normalizedRate s = manuscriptRate s := by
  have hq : Real.sqrt (3 : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  unfold normalizedRate conjugate manuscriptRate
  congr 1
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨x / Real.sqrt 3, ?_⟩
    have hx : Real.sqrt 3 * (x / Real.sqrt 3) = x := by
      field_simp [hq]
    rw [hx]
    ring
  · rintro ⟨h, rfl⟩
    refine ⟨Real.sqrt 3 * h, ?_⟩
    have hx : (s / Real.sqrt 3) * (Real.sqrt 3 * h) = s*h := by
      field_simp [hq]
    rw [hx]

theorem manuscriptRate_order_six_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, |s| ≤ 1/2 →
      |manuscriptRate s - (s^2/2 + s^4/20)| ≤ C * |s|^6 := by
  obtain ⟨C,hC,h⟩ := normalizedRate_order_six_bound
  exact ⟨C,hC,fun s hs => by rw [← normalizedRate_eq_manuscriptRate]; exact h s hs⟩

end
end M14.EulerianLegendre

#print axioms M14.EulerianLegendre.normalizedRate_eq_manuscriptRate
#print axioms M14.EulerianLegendre.manuscriptRate_order_six_bound
