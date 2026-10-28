import GegenbauerFock.GaussianAreaEntireRepresentativeUniqueness

/-!
# V007 — intrinsic entire Gaussian-L² representative and point evaluation

The preceding uniqueness theorem makes the entire representative of
an intrinsic Gaussian holomorphic L² class canonical. Its evaluation
is linear and injectively separates the intrinsic classes.

This is not a claim that evaluation is bounded, nor that the
intrinsic space is closed, nor that Gaussian polynomials are dense.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- The unique entire function representing an intrinsic Gaussian-L²
class, chosen from the existential analytic definition. -/
noncomputable def entireRepresentative (alpha : ℝ)
    (x : entireGaussianL2Submodule alpha) : ℂ → ℂ :=
  Classical.choose
    (show HasEntireGaussianRepresentative alpha
      (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) from x.property)

/-- The chosen intrinsic representative is entire. -/
theorem entireRepresentative_differentiable (alpha : ℝ)
    (x : entireGaussianL2Submodule alpha) :
    Differentiable ℂ (entireRepresentative alpha x) :=
  (Classical.choose_spec
    (show HasEntireGaussianRepresentative alpha
      (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) from x.property)).1

/-- The chosen entire function represents the actual L² class. -/
theorem entireRepresentative_ae (alpha : ℝ)
    (x : entireGaussianL2Submodule alpha) :
    entireRepresentative alpha x =ᵐ[gaussianAreaMeasure alpha]
      ((x : Lp ℂ 2 (gaussianAreaMeasure alpha)) : ℂ → ℂ) :=
  (Classical.choose_spec
    (show HasEntireGaussianRepresentative alpha
      (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) from x.property)).2

/-- Intrinsic entire representatives respect vector addition exactly
at every complex point, not merely Gaussian-almost everywhere. -/
theorem entireRepresentative_add (alpha : ℝ) (ha : 0 < alpha)
    (x y : entireGaussianL2Submodule alpha) :
    entireRepresentative alpha (x + y) =
      entireRepresentative alpha x + entireRepresentative alpha y := by
  apply entireGaussianRepresentative_unique alpha ha
    ((x + y : entireGaussianL2Submodule alpha) :
      Lp ℂ 2 (gaussianAreaMeasure alpha))
  · exact entireRepresentative_differentiable alpha (x + y)
  · exact (entireRepresentative_differentiable alpha x).add
      (entireRepresentative_differentiable alpha y)
  · exact entireRepresentative_ae alpha (x + y)
  · filter_upwards [entireRepresentative_ae alpha x,
      entireRepresentative_ae alpha y,
      Lp.coeFn_add (x : Lp ℂ 2 (gaussianAreaMeasure alpha))
        (y : Lp ℂ 2 (gaussianAreaMeasure alpha))] with z hx hy hxy
    simpa only [Pi.add_apply, hx, hy, Submodule.coe_add] using hxy.symm

/-- Intrinsic entire representatives respect complex scalar
multiplication pointwise. -/
theorem entireRepresentative_smul (alpha : ℝ) (ha : 0 < alpha)
    (c : ℂ) (x : entireGaussianL2Submodule alpha) :
    entireRepresentative alpha (c • x) =
      c • entireRepresentative alpha x := by
  apply entireGaussianRepresentative_unique alpha ha
    ((c • x : entireGaussianL2Submodule alpha) :
      Lp ℂ 2 (gaussianAreaMeasure alpha))
  · exact entireRepresentative_differentiable alpha (c • x)
  · change Differentiable ℂ (fun z => c * entireRepresentative alpha x z)
    exact (differentiable_const : Differentiable ℂ (fun _ : ℂ => c)).mul
      (entireRepresentative_differentiable alpha x)
  · exact entireRepresentative_ae alpha (c • x)
  · filter_upwards [entireRepresentative_ae alpha x,
      Lp.coeFn_smul c (x : Lp ℂ 2 (gaussianAreaMeasure alpha))]
      with z hx hsmul
    simpa only [Pi.smul_apply, smul_eq_mul, hx, Submodule.coe_smul] using hsmul.symm

/-- Canonical complex-linear representative map on the intrinsic
entire Gaussian-L² vector space. -/
noncomputable def entireRepresentativeLinear (alpha : ℝ) (ha : 0 < alpha) :
    entireGaussianL2Submodule alpha →ₗ[ℂ] (ℂ → ℂ) where
  toFun := entireRepresentative alpha
  map_add' := entireRepresentative_add alpha ha
  map_smul' := entireRepresentative_smul alpha ha

/-- A unique entire representative separates intrinsic Gaussian-L²
classes: the canonical representative map is injective. -/
theorem entireRepresentative_injective (alpha : ℝ) :
    Function.Injective (entireRepresentative alpha) := by
  intro x y hxy
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [entireRepresentative_ae alpha x,
    entireRepresentative_ae alpha y] with z hx hy
  exact hx.symm.trans ((congrFun hxy z).trans hy)

/-- Point evaluation is a genuine complex-linear functional on the
intrinsic entire Gaussian-L² space. Continuity is not asserted. -/
noncomputable def intrinsicEntireEvaluation (alpha : ℝ) (ha : 0 < alpha)
    (z : ℂ) : entireGaussianL2Submodule alpha →ₗ[ℂ] ℂ where
  toFun := fun x => entireRepresentative alpha x z
  map_add' := by
    intro x y
    simpa only [Pi.add_apply] using
      congrFun (entireRepresentative_add alpha ha x y) z
  map_smul' := by
    intro c x
    simpa only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply] using
      congrFun (entireRepresentative_smul alpha ha c x) z

#print axioms GegenbauerFock.GaussianArea.entireRepresentative_differentiable
#print axioms GegenbauerFock.GaussianArea.entireRepresentative_ae
#print axioms GegenbauerFock.GaussianArea.entireRepresentative_add
#print axioms GegenbauerFock.GaussianArea.entireRepresentative_smul
#print axioms GegenbauerFock.GaussianArea.entireRepresentative_injective
#print axioms GegenbauerFock.GaussianArea.intrinsicEntireEvaluation

end GegenbauerFock.GaussianArea
