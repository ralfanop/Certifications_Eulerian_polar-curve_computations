import Peters2024
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-! Woodhouse (1992), p. 198, Section 2. Affine incidence in flat split
signature. A common alpha-plane is not a path between disconnected spaces. -/
namespace Peters2024.Woodhouse
noncomputable section

abbrev Event := ℂ × ℂ

def incidence (z : ℂ) (p : Event) : ℂ := p.1 + star z * p.2

def splitNull (p q : Event) : Prop := ‖q.1 - p.1‖ = ‖q.2 - p.2‖

theorem common_plane_null {p q : Event} {z : ℂ} (hz : ‖z‖ = 1)
    (h : incidence z p = incidence z q) : splitNull p q := by
  have he : q.1 - p.1 = -(star z * (q.2 - p.2)) := by
    unfold incidence at h
    linear_combination -h
  unfold splitNull
  rw [he, norm_neg, norm_mul]
  change ‖(starRingEnd ℂ) z‖ * ‖q.2 - p.2‖ = _
  rw [Complex.norm_conj, hz, one_mul]

theorem null_common_plane {p q : Event} (h : splitNull p q) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ incidence z p = incidence z q := by
  by_cases ht : q.2 - p.2 = 0
  · have hx : q.1 - p.1 = 0 := by
      apply norm_eq_zero.mp
      rw [show ‖q.1 - p.1‖ = ‖q.2 - p.2‖ from h, ht, norm_zero]
    exact ⟨1, norm_one, by simp [incidence, sub_eq_zero.mp hx, sub_eq_zero.mp ht]⟩
  · let z : ℂ := star (-(q.1 - p.1) / (q.2 - p.2))
    refine ⟨z, ?_, ?_⟩
    · change ‖(starRingEnd ℂ) (-(q.1 - p.1) / (q.2 - p.2))‖ = 1
      rw [Complex.norm_conj, norm_div, norm_neg, show ‖q.1 - p.1‖ = ‖q.2 - p.2‖ from h]
      exact div_self (norm_ne_zero_iff.mpr ht)
    · unfold incidence
      have he : star z * (q.2 - p.2) = -(q.1 - p.1) := by
        simp [z, div_mul_cancel₀ _ ht]
      linear_combination -he

theorem null_iff_common_plane (p q : Event) :
    splitNull p q ↔ ∃ z : ℂ, ‖z‖ = 1 ∧ incidence z p = incidence z q := by
  constructor
  · exact null_common_plane
  · rintro ⟨z, hz, he⟩
    exact common_plane_null hz he

def affineSegment (p q : Event) (t : ℝ) : Event :=
  (p.1 + (t : ℂ) * (q.1 - p.1), p.2 + (t : ℂ) * (q.2 - p.2))

theorem affineSegment_incidence {p q : Event} {z : ℂ}
    (h : incidence z p = incidence z q) (t : ℝ) :
    incidence z (affineSegment p q t) = incidence z p := by
  change p.1 + (starRingEnd ℂ) z * p.2 = q.1 + (starRingEnd ℂ) z * q.2 at h
  change (p.1 + (t : ℂ) * (q.1 - p.1)) + (starRingEnd ℂ) z *
    (p.2 + (t : ℂ) * (q.2 - p.2)) = p.1 + (starRingEnd ℂ) z * p.2
  linear_combination -(t : ℂ) * h

theorem affineSegment_continuous (p q : Event) : Continuous (affineSegment p q) := by
  unfold affineSegment
  exact (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).prodMk
    (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))

theorem affineSegment_null {p q : Event} {z : ℂ} (hz : ‖z‖ = 1)
    (h : incidence z p = incidence z q) (s t : ℝ) :
    splitNull (affineSegment p q s) (affineSegment p q t) := by
  apply common_plane_null hz
  rw [affineSegment_incidence h s, affineSegment_incidence h t]

/-- Two orientation values suffice to reconstruct an event. -/
theorem two_orientations_injective {p q : Event}
    (h₁ : incidence 1 p = incidence 1 q) (h₂ : incidence (-1) p = incidence (-1) q) : p = q := by
  simp [incidence] at h₁ h₂
  apply Prod.ext
  · linear_combination (h₁ + h₂) / 2
  · linear_combination (h₁ - h₂) / 2

/-- For distinct events sharing an alpha-plane, its orientation is unique. -/
theorem unique_orientation {p q : Event} (hpq : p ≠ q)
    {z v : ℂ} (hz : incidence z p = incidence z q)
    (hv : incidence v p = incidence v q) : z = v := by
  have ht : q.2 - p.2 ≠ 0 := by
    intro ht
    have ht' : q.2 = p.2 := sub_eq_zero.mp ht
    apply hpq
    apply Prod.ext
    · unfold incidence at hz
      rw [ht'] at hz
      exact add_right_cancel hz
    · exact ht'.symm
  have hm : ((starRingEnd ℂ) z - (starRingEnd ℂ) v) * (q.2 - p.2) = 0 := by
    change p.1 + (starRingEnd ℂ) z * p.2 = q.1 + (starRingEnd ℂ) z * q.2 at hz
    change p.1 + (starRingEnd ℂ) v * p.2 = q.1 + (starRingEnd ℂ) v * q.2 at hv
    linear_combination hv - hz
  have hs : (starRingEnd ℂ) z = (starRingEnd ℂ) v := sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_right ht)
  exact star_injective hs

/-- The actual continuous path inside the common alpha-plane. -/
def affinePath (p q : Event) : Path p q where
  toFun t := affineSegment p q t
  continuous_toFun := (affineSegment_continuous p q).comp continuous_subtype_val
  source' := by simp [affineSegment]
  target' := by simp [affineSegment]

theorem null_path (p q : Event) (h : splitNull p q) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ ∃ γ : Path p q,
      (∀ t, incidence z (γ t) = incidence z p) ∧
      ∀ s t, splitNull (γ s) (γ t) := by
  obtain ⟨z, hz, he⟩ := null_common_plane h
  exact ⟨z, hz, affinePath p q, fun t => affineSegment_incidence he t,
    fun s t => affineSegment_null hz he s t⟩

/-- Intersection points with Woodhouse's initial two-plane form precisely
the circle of centre xi and radius |tau|, including the zero-radius case. -/
theorem initial_plane_circle (p : Event) (w : ℂ) :
    (∃ z : ℂ, ‖z‖ = 1 ∧ incidence z p = w) ↔ ‖w - p.1‖ = ‖p.2‖ := by
  have he := null_iff_common_plane p (w, 0)
  simpa [splitNull, incidence] using he.symm

/-- Woodhouse's domain of dependence for an initial subset U of the
spacelike plane τ = 0: every alpha-plane through p intersects U. -/
def initialDomain (U : Set ℂ) : Set Event :=
  {p | ∀ z : ℂ, ‖z‖ = 1 → incidence z p ∈ U}

theorem initialDomain_iff_circle (U : Set ℂ) (p : Event) :
    p ∈ initialDomain U ↔ ∀ w : ℂ, ‖w - p.1‖ = ‖p.2‖ → w ∈ U := by
  constructor
  · intro hp w hw
    obtain ⟨z, hz, he⟩ := (initial_plane_circle p w).mpr hw
    rw [← he]
    exact hp z hz
  · intro hp z hz
    exact hp _ ((initial_plane_circle p _).mp ⟨z, hz, rfl⟩)

end
end Peters2024.Woodhouse

#print axioms Peters2024.Woodhouse.common_plane_null
#print axioms Peters2024.Woodhouse.null_common_plane
#print axioms Peters2024.Woodhouse.null_iff_common_plane
#print axioms Peters2024.Woodhouse.affineSegment_incidence
#print axioms Peters2024.Woodhouse.affineSegment_continuous
#print axioms Peters2024.Woodhouse.affineSegment_null
#print axioms Peters2024.Woodhouse.two_orientations_injective
#print axioms Peters2024.Woodhouse.unique_orientation
#print axioms Peters2024.Woodhouse.null_path
#print axioms Peters2024.Woodhouse.initial_plane_circle
#print axioms Peters2024.Woodhouse.initialDomain_iff_circle
