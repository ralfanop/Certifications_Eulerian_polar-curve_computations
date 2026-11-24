import Mathlib

/-!
Manuscript 17, 24 Nov 2026, Cyclohedral.tex, labels
m17-feff-metric-proof, m17-feff-critical-metric, m17-feff-Dirichlet-energy.
Coordinate tangent realization of the null-normalization pullback. The
Herzlich metric theorem is a cited classical input, not proved here.
No claim of a complete smooth quotient, intrinsic Laplace--Beltrami,
or manifold-level integration is made by this module.
-/
noncomputable section
namespace EulerianCert.CassiniFeffermanTangent20261124

abbrev V := Fin 6 → ℝ

def B (x y : V) : ℝ :=
  x 0 * y 0 + x 1 * y 1 + x 2 * y 2 + x 3 * y 3 -
    x 4 * y 4 - x 5 * y 5

def lin (a b : ℝ) (u x : V) : V :=
  fun i => a * u i + b * x i

def normalizedTangent (R dR : ℝ) (x u : V) : V :=
  lin (1 / R) (-dR / R ^ 2) u x

/-- Full mixed tangent tensor evaluation, not just a norm or diagonal. -/
theorem ambient_mixed_expansion (a b c d : ℝ) (x u w : V) :
    B (lin a b u x) (lin c d w x) =
      a*c*B u w + a*d*B u x + b*c*B x w + b*d*B x x := by
  unfold B lin
  ring

theorem ambient_symmetric (x y : V) : B x y = B y x := by
  unfold B
  ring

/-- Differentiation of an actual null curve gives orthogonality. -/
theorem null_curve_tangent (c : ℝ → V) (s : ℝ) (u : V)
    (hc : ∀ i, HasDerivAt (fun t => c t i) (u i) s)
    (hn : ∀ t, B (c t) (c t) = 0) :
    B (c s) u = 0 := by
  have h0 := (hc 0).mul (hc 0)
  have h1 := (hc 1).mul (hc 1)
  have h2 := (hc 2).mul (hc 2)
  have h3 := (hc 3).mul (hc 3)
  have h4 := (hc 4).mul (hc 4)
  have h5 := (hc 5).mul (hc 5)
  have hd : HasDerivAt (fun t => B (c t) (c t)) (2 * B (c s) u) s := by
    convert (((((h0.add h1).add h2).add h3).sub h4).sub h5) using 1
    · funext t
      simp only [B, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
    · simp only [B]
      ring
  have hz : HasDerivAt (fun t => B (c t) (c t)) 0 s := by
    rw [show (fun t => B (c t) (c t)) = (fun _ : ℝ => (0 : ℝ)) from funext hn]
    exact hasDerivAt_const s 0
  have he := hd.unique hz
  linarith

/-- Differentiation of the normalized lift in each ambient coordinate. -/
theorem normalized_coordinate_derivative (c : ℝ → V) (r : ℝ → ℝ)
    (s dr : ℝ) (u : V)
    (hc : ∀ i, HasDerivAt (fun t => c t i) (u i) s)
    (hr : HasDerivAt r dr s) (hR : r s ≠ 0) (i : Fin 6) :
    HasDerivAt (fun t => c t i / r t)
      (normalizedTangent (r s) dr (c s) u i) s := by
  convert (hc i).div hr hR using 1 <;>
    simp only [normalizedTangent, lin] <;>
    field_simp [hR] <;> ring

/-- Ambient bilinear pullback under positive null normalization. -/
theorem normalized_null_pullback (R dR eR : ℝ) (x u w : V)
    (hR : R ≠ 0) (hn : B x x = 0)
    (hu : B x u = 0) (hw : B x w = 0) :
    B (normalizedTangent R dR x u) (normalizedTangent R eR x w) =
      B u w / R ^ 2 := by
  have hux : B u x = 0 := by rw [ambient_symmetric u x, hu]
  unfold normalizedTangent
  rw [ambient_mixed_expansion, hn, hux, hw]
  field_simp [hR] <;> ring

/-- The actual Cassini null-lift coordinate factor, for arbitrary tangent
directions; the half comes from the cited Herzlich normalization. -/
theorem cassini_tangent_metric (t R dR eR : ℝ) (x u w : V)
    (hR : R ≠ 0) (hR2 : R ^ 2 = 1 + t ^ 2)
    (hn : B x x = 0) (hu : B x u = 0) (hw : B x w = 0) :
    B (normalizedTangent R dR x u) (normalizedTangent R eR x w) / 2 =
      B u w / (2 * (1 + t ^ 2)) := by
  rw [normalized_null_pullback R dR eR x u w hR hn hu hw, hR2]
  have hp : 1 + t ^ 2 ≠ 0 := by positivity
  field_simp [hp] <;> ring

/-- Tensor pullback composition with the Herzlich identity as input. -/
theorem hereditary_pullback (T W : Type*) (J : T → W)
    (gE gF : W → W → ℝ)
    (hHerzlich : ∀ a b, gE a b = 2 * gF a b)
    (t : ℝ) (gPhi : T → T → ℝ)
    (hEinstein : ∀ a b, gE (J a) (J b) = gPhi a b / (1 + t ^ 2))
    (a b : T) :
    gF (J a) (J b) = gPhi a b / (2 * (1 + t ^ 2)) := by
  have h := hHerzlich (J a) (J b)
  rw [hEinstein] at h
  have hp : 1 + t ^ 2 ≠ 0 := by positivity
  field_simp [hp] at h ⊢
  linarith

/-- Integrated chart density equality, for any common reference measure.
The identification of these weighted densities with intrinsic manifold
norm and area remains a separate geometric obligation. -/
theorem dirichlet_chart_integral {X : Type*} [MeasurableSpace X]
    (mu : MeasureTheory.Measure X) (L E A : X → ℝ)
    (hL : ∀ x, L x ≠ 0) :
    (∫ x, (E x / L x) * (L x * A x) ∂mu) =
      ∫ x, E x * A x ∂mu := by
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by field_simp [hL x] <;> ring)

#print axioms ambient_mixed_expansion
#print axioms ambient_symmetric
#print axioms null_curve_tangent
#print axioms normalized_coordinate_derivative
#print axioms normalized_null_pullback
#print axioms cassini_tangent_metric
#print axioms hereditary_pullback
#print axioms dirichlet_chart_integral
end EulerianCert.CassiniFeffermanTangent20261124
