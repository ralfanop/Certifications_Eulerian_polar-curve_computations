import WoodhouseJadczyk
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp

/-! Coordinate form of Jadczyk (2026), Proposition 12, equations (203)–(208).
The flat affine chart is the slice x₅ − x₆ = 1. We establish both directions
of its isotropic-plane/null-line correspondence, and the differential equation
of these affine null lines. This is not a formalization of the global
Levi-Civita connection or of the converse for arbitrary manifold geodesics. -/
namespace Peters2024.JadczykNullGeodesic
noncomputable section

abbrev E := Fin 4 → ℝ
abbrev V := E × ℝ × ℝ

def mink (x : E) : ℝ := x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 - x 3 ^ 2
def dot (x y : E) : ℝ := x 0 * y 0 + x 1 * y 1 + x 2 * y 2 - x 3 * y 3
def ambientQ (X : V) : ℝ := mink X.1 + X.2.1 ^ 2 - X.2.2 ^ 2
def pairing (X Y : V) : ℝ := dot X.1 Y.1 + X.2.1 * Y.2.1 - X.2.2 * Y.2.2
def sign (X : V) : ℝ := X.2.1 - X.2.2
def lift (x : E) : V := (x, (1 - mink x) / 2, -(1 + mink x) / 2)
def project (X : V) : E := (sign X)⁻¹ • X.1
def affineLine (x d : E) (s : ℝ) : E := x + s • d
def plane (X Y : V) : Set V := {Z | ∃ a b : ℝ, Z = a • X + b • Y}

/-- Coordinate change from the complex realization of the preceding PR. -/
def fromAmbient (X : WoodhouseJadczyk.Ambient) : V :=
  (![X.1.re, X.1.im, X.2.1.re, X.2.2.re], X.2.1.im, X.2.2.im)

theorem fromAmbient_quad (X : WoodhouseJadczyk.Ambient) :
    ambientQ (fromAmbient X) = WoodhouseJadczyk.quad X := by
  simp [ambientQ, fromAmbient, mink, WoodhouseJadczyk.quad, Complex.sq_norm, Complex.normSq_apply]
  ring

theorem fromAmbient_sign (X : WoodhouseJadczyk.Ambient) :
    sign (fromAmbient X) = WoodhouseJadczyk.chartSign X := rfl

theorem mink_line (x d : E) (s : ℝ) :
    mink (affineLine x d s) = mink x + 2 * s * dot x d + s^2 * mink d := by
  simp [mink, affineLine, dot, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem lift_null (x : E) : ambientQ (lift x) = 0 := by
  simp [ambientQ, lift]
  ring

theorem lift_sign (x : E) : sign (lift x) = 1 := by
  simp [sign, lift]
  ring

theorem lift_project (x : E) : project (lift x) = x := by
  unfold project
  rw [lift_sign, inv_one, one_smul]
  rfl

theorem slice_unique (X : V) (hQ : ambientQ X = 0) (hs : sign X = 1) :
    X = lift X.1 := by
  have h : X.2.1 = 1 + X.2.2 := by unfold sign at hs; linarith
  unfold ambientQ at hQ
  rw [h] at hQ
  have hb : X.2.2 = -(1 + mink X.1) / 2 := by nlinarith
  exact Prod.ext rfl (Prod.ext (by simp [lift]; linarith) hb)

theorem pairing_lifts (x y : E) : pairing (lift x) (lift y) = -mink (x-y) / 2 := by
  simp [pairing, lift, mink, dot, Pi.sub_apply]
  ring

theorem isotropic_pair_iff (x y : E) : pairing (lift x) (lift y) = 0 ↔ mink (x-y) = 0 := by
  rw [pairing_lifts]
  constructor <;> intro h <;> linarith

theorem sign_combination (X Y : V) (a b : ℝ) :
    sign (a • X + b • Y) = a * sign X + b * sign Y := by
  simp [sign, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

theorem quad_combination (X Y : V) (a b : ℝ) :
    ambientQ (a • X + b • Y) = a^2 * ambientQ X + 2*a*b*pairing X Y + b^2 * ambientQ Y := by
  simp [ambientQ, mink, pairing, dot, Pi.add_apply, Pi.smul_apply,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

theorem lift_line (x d : E) (hd : mink d = 0) (s : ℝ) :
    lift (affineLine x d s) = (1-s) • lift x + s • lift (x+d) := by
  have h₁ := mink_line x d s
  have h₂ := mink_line x d 1
  simp [hd, affineLine] at h₁ h₂
  apply Prod.ext
  · funext i
    simp [lift, affineLine, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · apply Prod.ext <;> simp [lift, affineLine, h₁, h₂, smul_eq_mul] <;> ring

theorem null_line_span (x y : E) (h : mink (y-x) = 0) :
    ∀ X ∈ plane (lift x) (lift y), ambientQ X = 0 := by
  have hp : pairing (lift x) (lift y) = 0 := by
    apply (isotropic_pair_iff x y).2
    unfold mink at h ⊢
    simp only [Pi.sub_apply] at h ⊢
    linarith only [h, show (x 0-y 0)^2+(x 1-y 1)^2+(x 2-y 2)^2-(x 3-y 3)^2 =
      (y 0-x 0)^2+(y 1-x 1)^2+(y 2-x 2)^2-(y 3-x 3)^2 by ring]
  rintro X ⟨a,b,rfl⟩
  simp [quad_combination, lift_null, hp]

/-- Exact affine slice correspondence (both inclusions). -/
theorem slice_line_iff (x d : E) (hd : mink d = 0) (X : V) :
    X ∈ plane (lift x) (lift (x+d)) ∧ sign X = 1 ↔
      ∃ s : ℝ, X = lift (affineLine x d s) := by
  constructor
  · rintro ⟨⟨a,b,rfl⟩,hs⟩
    rw [sign_combination, lift_sign, lift_sign] at hs
    have ha : a = 1-b := by linarith
    exact ⟨b, by rw [lift_line x d hd, ha]⟩
  · rintro ⟨s,rfl⟩
    exact ⟨⟨1-s,s,lift_line x d hd s⟩,lift_sign _⟩

/-- Any two independent null vectors in the unit affine slice of an isotropic
plane determine precisely its affine null line. -/
theorem isotropic_slice (X Y : V) (hx : ambientQ X = 0) (hy : ambientQ Y = 0)
    (hsx : sign X = 1) (hsy : sign Y = 1) (hp : pairing X Y = 0) (hne : X ≠ Y) :
    mink (Y.1-X.1) = 0 ∧ Y.1-X.1 ≠ 0 ∧
      ∀ Z : V, Z ∈ plane X Y ∧ sign Z = 1 ↔
        ∃ s : ℝ, Z = lift (affineLine X.1 (Y.1-X.1) s) := by
  have eX := slice_unique X hx hsx
  have eY := slice_unique Y hy hsy
  have hp' : pairing (lift Y.1) (lift X.1) = 0 := by
    have hh : pairing Y X = pairing X Y := by simp [pairing, dot]; ring
    rw [← eX, ← eY, hh, hp]
  have hd := (isotropic_pair_iff Y.1 X.1).1 hp'
  refine ⟨hd, ?_, ?_⟩
  · intro h
    have he : Y.1 = X.1 := sub_eq_zero.mp h
    apply hne
    exact eX.trans (by rw [← he, ← eY])
  · intro Z
    have he : X.1 + (Y.1-X.1) = Y.1 := by abel
    have h := slice_line_iff X.1 (Y.1-X.1) hd Z
    rw [he, ← eX, ← eY] at h
    exact h

/-- The local projective path of (208) is reparameterized by t/(1+t). -/
theorem project_combination (x d : E) (a b : ℝ) (h : a+b ≠ 0) :
    project (a • lift x + b • lift (x+d)) = affineLine x d (b/(a+b)) := by
  have hs : sign (a • lift x + b • lift (x+d)) = a+b := by
    simp [sign_combination, lift_sign]
  unfold project
  rw [hs]
  funext i
  simp [affineLine, lift, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp [h]
  ring

theorem affineLine_derivative (x d : E) (s : ℝ) : HasDerivAt (affineLine x d) d s := by
  change HasDerivAt (fun t : ℝ => x + t • d) d s
  simpa only [id_eq, one_smul] using ((hasDerivAt_id s).smul_const d).const_add x

theorem affineLine_acceleration (x d : E) (s : ℝ) : deriv (deriv (affineLine x d)) s = 0 := by
  have he : deriv (affineLine x d) = fun _ => d := funext fun t => (affineLine_derivative x d t).deriv
  rw [he]
  simp

theorem affine_null_geodesic (x d : E) (hd : mink d = 0) (hne : d ≠ 0) (s : ℝ) :
    mink (deriv (affineLine x d) s) = 0 ∧ deriv (affineLine x d) s ≠ 0 ∧
      deriv (deriv (affineLine x d)) s = 0 := by
  rw [(affineLine_derivative x d s).deriv]
  exact ⟨hd,hne,affineLine_acceleration x d s⟩

/-- The parameter in Jadczyk's local formula has strictly positive derivative
away from the excluded point t = -1. -/
theorem projective_parameter_derivative (t : ℝ) (ht : 1+t ≠ 0) :
    HasDerivAt (fun s : ℝ => s/(1+s)) (1/(1+t)^2) t := by
  have h := (hasDerivAt_id t).div ((hasDerivAt_id t).const_add 1) ht
  convert h using 1
  simp

theorem projective_parameter_regular (t : ℝ) (ht : 1+t ≠ 0) :
    0 < deriv (fun s : ℝ => s/(1+s)) t := by
  rw [(projective_parameter_derivative t ht).deriv]
  positivity

theorem projective_null_velocity (x d : E) (hd : mink d = 0) (hne : d ≠ 0)
    (t : ℝ) (ht : 1+t ≠ 0) :
    HasDerivAt (fun s : ℝ => affineLine x d (s/(1+s))) ((1/(1+t)^2) • d) t ∧
      mink ((1/(1+t)^2) • d) = 0 ∧ ((1/(1+t)^2) • d) ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [affineLine] using (projective_parameter_derivative t ht).smul_const d |>.const_add x
  · have h : ∀ r : ℝ, mink (r • d) = r^2 * mink d := by
      intro r
      simp [mink, Pi.smul_apply, smul_eq_mul]
      ring
    rw [h,hd,mul_zero]
  · exact smul_ne_zero (by positivity) hne

/-- The rotating representative (205) has null tangent and harmonic
acceleration on any totally isotropic plane. -/
def circle (X Y : V) (t : ℝ) : V := Real.cos t • X + Real.sin t • Y
def velocity (X Y : V) (t : ℝ) : V := (-Real.sin t) • X + Real.cos t • Y

theorem circle_derivative (X Y : V) (t : ℝ) :
    HasDerivAt (circle X Y) (velocity X Y t) t := by
  exact ((Real.hasDerivAt_cos t).smul_const X).add ((Real.hasDerivAt_sin t).smul_const Y)

theorem circle_acceleration (X Y : V) (t : ℝ) :
    deriv (deriv (circle X Y)) t = -circle X Y t := by
  have he : deriv (circle X Y) = velocity X Y := funext fun s => (circle_derivative X Y s).deriv
  rw [he]
  have h := (((Real.hasDerivAt_sin t).neg).smul_const X).add ((Real.hasDerivAt_cos t).smul_const Y)
  have hh : HasDerivAt (velocity X Y) (-circle X Y t) t := by
    simpa only [circle, velocity, neg_add, neg_smul] using h
  exact hh.deriv

theorem circle_null_tangent (X Y : V) (hX : ambientQ X = 0) (hY : ambientQ Y = 0)
    (hp : pairing X Y = 0) (t : ℝ) :
    ambientQ (circle X Y t) = 0 ∧ ambientQ (deriv (circle X Y) t) = 0 := by
  rw [(circle_derivative X Y t).deriv]
  unfold circle velocity
  rw [quad_combination, quad_combination]
  simp [hX,hY,hp]

theorem circle_regular (X Y : V)
    (hi : ∀ a b : ℝ, a • X + b • Y = 0 → a = 0 ∧ b = 0) (t : ℝ) :
    circle X Y t ≠ 0 ∧ deriv (circle X Y) t ≠ 0 := by
  rw [(circle_derivative X Y t).deriv]
  constructor
  · intro h
    have hh := hi (Real.cos t) (Real.sin t) h
    have ht := Real.sin_sq_add_cos_sq t
    rw [hh.1,hh.2] at ht
    norm_num at ht
  · intro h
    have hh := hi (-Real.sin t) (Real.cos t) h
    have ht := Real.sin_sq_add_cos_sq t
    rw [neg_eq_zero.mp hh.1,hh.2] at ht
    norm_num at ht

theorem circle_chart_sign (X Y : V) (hx : sign X = 1) (hy : sign Y = 1) (t : ℝ) :
    sign (circle X Y t) = Real.cos t + Real.sin t := by
  simp [circle, sign_combination, hx, hy]

theorem circle_chart_projection (x d : E) (t : ℝ) (h : Real.cos t + Real.sin t ≠ 0) :
    project (circle (lift x) (lift (x+d)) t) =
      affineLine x d (Real.sin t/(Real.cos t+Real.sin t)) :=
  project_combination x d _ _ h

/-- A nonzero signed chart coordinate uniquely fixes the affine representative.
The sign may be negative: this theorem is about the unoriented affine chart. -/
theorem signed_ray_lift (X : V) (hq : ambientQ X = 0) (hs : sign X ≠ 0) :
    (sign X)⁻¹ • X = lift (project X) := by
  have hq' : ambientQ ((sign X)⁻¹ • X) = 0 := by
    have h := quad_combination X X (sign X)⁻¹ 0
    simpa [hq] using h
  have hs' : sign ((sign X)⁻¹ • X) = 1 := by
    have h := sign_combination X X (sign X)⁻¹ 0
    simpa [hs] using h
  exact slice_unique _ hq' hs'

/-- The fixed-chart portion of any isotropic plane meeting that chart has a
null-line description; the second vector need not initially be in the slice. -/
theorem rebase_plane (X Y : V) (c : ℝ) : plane X (c • X + Y) = plane X Y := by
  ext Z
  constructor
  · rintro ⟨a,b,rfl⟩
    refine ⟨a+b*c,b,?_⟩
    rw [smul_add, smul_smul, add_smul, add_assoc]
  · rintro ⟨a,b,rfl⟩
    refine ⟨a-b*c,b,?_⟩
    rw [smul_add, smul_smul, ← add_assoc, ← add_smul]
    congr 1
    ring

theorem pairing_rebase (X Y : V) (c : ℝ) :
    pairing X (c • X + Y) = c * ambientQ X + pairing X Y := by
  simp [pairing, ambientQ, dot, mink, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Prod.smul_fst, Prod.smul_snd]
  ring

/-- The affine chart characterization does not require an initially adapted
second basis vector. The non-collinearity assumption rules out a point. -/
theorem isotropic_plane_affine (X Y : V) (hx : ambientQ X = 0) (hy : ambientQ Y = 0)
    (hsx : sign X = 1) (hp : pairing X Y = 0)
    (hi : ∀ c : ℝ, Y ≠ c • X) :
    ∃ d : E, mink d = 0 ∧ d ≠ 0 ∧
      (∀ Z : V, Z ∈ plane X Y ∧ sign Z = 1 ↔
        ∃ s : ℝ, Z = lift (affineLine X.1 d s)) ∧
      ∀ s : ℝ, mink (deriv (affineLine X.1 d) s) = 0 ∧
        deriv (affineLine X.1 d) s ≠ 0 ∧ deriv (deriv (affineLine X.1 d)) s = 0 := by
  let c := 1-sign Y
  let W := c • X + Y
  have hW : ambientQ W = 0 := by
    have h := quad_combination X Y c 1
    simpa [W,hx,hy,hp] using h
  have hsW : sign W = 1 := by
    have h := sign_combination X Y c 1
    simpa [W,c,hsx] using h
  have hpW : pairing X W = 0 := by simp [W,pairing_rebase,hx,hp]
  have hnW : X ≠ W := by
    intro h
    apply hi (1-c)
    have he : Y = X - c • X := by
      have hh : c • X + Y = X := h.symm
      exact eq_sub_of_add_eq (by simpa only [add_comm] using hh)
    exact he.trans (by simpa only [one_smul] using (sub_smul (1 : ℝ) c X).symm)
  obtain ⟨hd,hne,hline⟩ := isotropic_slice X W hx hW hsx hsW hpW hnW
  refine ⟨W.1-X.1,hd,hne,?_,?_⟩
  · intro Z
    have h := hline Z
    change Z ∈ plane X (c • X + Y) ∧ sign Z = 1 ↔ _ at h
    rwa [rebase_plane] at h
  · exact affine_null_geodesic _ _ hd hne

end
end Peters2024.JadczykNullGeodesic

#print axioms Peters2024.JadczykNullGeodesic.fromAmbient_quad
#print axioms Peters2024.JadczykNullGeodesic.fromAmbient_sign
#print axioms Peters2024.JadczykNullGeodesic.mink_line
#print axioms Peters2024.JadczykNullGeodesic.lift_null
#print axioms Peters2024.JadczykNullGeodesic.lift_sign
#print axioms Peters2024.JadczykNullGeodesic.lift_project
#print axioms Peters2024.JadczykNullGeodesic.slice_unique
#print axioms Peters2024.JadczykNullGeodesic.pairing_lifts
#print axioms Peters2024.JadczykNullGeodesic.isotropic_pair_iff
#print axioms Peters2024.JadczykNullGeodesic.sign_combination
#print axioms Peters2024.JadczykNullGeodesic.quad_combination
#print axioms Peters2024.JadczykNullGeodesic.lift_line
#print axioms Peters2024.JadczykNullGeodesic.null_line_span
#print axioms Peters2024.JadczykNullGeodesic.slice_line_iff
#print axioms Peters2024.JadczykNullGeodesic.isotropic_slice
#print axioms Peters2024.JadczykNullGeodesic.project_combination
#print axioms Peters2024.JadczykNullGeodesic.affineLine_derivative
#print axioms Peters2024.JadczykNullGeodesic.affineLine_acceleration
#print axioms Peters2024.JadczykNullGeodesic.affine_null_geodesic
#print axioms Peters2024.JadczykNullGeodesic.projective_parameter_derivative
#print axioms Peters2024.JadczykNullGeodesic.projective_parameter_regular
#print axioms Peters2024.JadczykNullGeodesic.projective_null_velocity
#print axioms Peters2024.JadczykNullGeodesic.circle_derivative
#print axioms Peters2024.JadczykNullGeodesic.circle_acceleration
#print axioms Peters2024.JadczykNullGeodesic.circle_null_tangent
#print axioms Peters2024.JadczykNullGeodesic.circle_regular
#print axioms Peters2024.JadczykNullGeodesic.circle_chart_sign
#print axioms Peters2024.JadczykNullGeodesic.circle_chart_projection
#print axioms Peters2024.JadczykNullGeodesic.signed_ray_lift
#print axioms Peters2024.JadczykNullGeodesic.rebase_plane
#print axioms Peters2024.JadczykNullGeodesic.pairing_rebase
#print axioms Peters2024.JadczykNullGeodesic.isotropic_plane_affine
