import GegenbauerFock.GaussianAreaPolynomialClosureEquiv

/-!
# V007 — the genuine entire-representative Gaussian L² submodule

We distinguish the *analytic* Bargmann–Fock candidate space from the
closed span of polynomial vectors. Here the former consists of
weighted Gaussian L² classes admitting an everywhere complex
differentiable representative. This condition is shown stable under
finite linear combinations; every normalized holomorphic monomial
has such a representative.

The crucial analytic closedness and polynomial-density identification
of this submodule are NOT claimed here.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- A weighted Gaussian L² class admits a genuinely entire
representative, in the sense of everywhere complex differentiability. -/
def HasEntireGaussianRepresentative
    (alpha : ℝ) (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) : Prop :=
  ∃ f : ℂ → ℂ, Differentiable ℂ f ∧
    f =ᵐ[gaussianAreaMeasure alpha] (x : ℂ → ℂ)

/-- Actual Gaussian-L² classes with entire representatives form a
complex linear submodule, without assuming they are already closed. -/
def entireGaussianL2Submodule
    (alpha : ℝ) : Submodule ℂ (Lp ℂ 2 (gaussianAreaMeasure alpha)) where
  carrier := {x | HasEntireGaussianRepresentative alpha x}
  zero_mem' := by
    refine ⟨fun _ : ℂ => (0 : ℂ), ?_, ?_⟩
    · fun_prop
    · filter_upwards [] with z
      simp
  add_mem' := by
    intro x y hx hy
    obtain ⟨f, hf, hfx⟩ := hx
    obtain ⟨g, hg, hgy⟩ := hy
    refine ⟨fun z => f z + g z, hf.add hg, ?_⟩
    filter_upwards [hfx, hgy] with z hxz hyz
    simpa [hxz, hyz, Lp.coeFn_add]
  smul_mem' := by
    intro c x hx
    obtain ⟨f, hf, hfx⟩ := hx
    refine ⟨fun z => c * f z, ?_, ?_⟩
    · fun_prop
    · filter_upwards [hfx] with z hz
      simpa [hz, smul_eq_mul, Lp.coeFn_smul]

/-- The normalized entire complex monomial is differentiable
everywhere, with no assumption on a limiting coefficient series. -/
theorem normalizedMonomial_differentiable
    (alpha : ℝ) (n : ℕ) :
    Differentiable ℂ (normalizedMonomial alpha n) := by
  change Differentiable ℂ
    (fun z : ℂ => monomialWeight alpha n * z ^ n)
  fun_prop

/-- Each genuine Gaussian L² normalized monomial vector belongs
to the analytic submodule by its explicitly entire representative. -/
theorem normalizedMonomialL2Vector_mem_entireGaussianL2Submodule
    (alpha : ℝ) (ha : 0 < alpha) (n : ℕ) :
    normalizedMonomialL2Vector alpha ha n ∈
      entireGaussianL2Submodule alpha := by
  exact ⟨normalizedMonomial alpha n,
    normalizedMonomial_differentiable alpha n,
    (normalizedMonomialL2Vector_ae alpha ha n).symm⟩

/-- In particular, every finite Gaussian holomorphic polynomial
vector lies in the entire-representative Hilbert-class submodule. -/
theorem gaussianPolynomialSpan_le_entireGaussianL2Submodule
    (alpha : ℝ) (ha : 0 < alpha) :
    Submodule.span ℂ (Set.range
      (fun n : ℕ => normalizedMonomialL2Vector alpha ha n)) ≤
      entireGaussianL2Submodule alpha := by
  apply Submodule.span_le.mpr
  rintro x ⟨n, rfl⟩
  exact normalizedMonomialL2Vector_mem_entireGaussianL2Submodule alpha ha n

#print axioms GegenbauerFock.GaussianArea.normalizedMonomial_differentiable
#print axioms GegenbauerFock.GaussianArea.normalizedMonomialL2Vector_mem_entireGaussianL2Submodule
#print axioms GegenbauerFock.GaussianArea.gaussianPolynomialSpan_le_entireGaussianL2Submodule

end GegenbauerFock.GaussianArea
