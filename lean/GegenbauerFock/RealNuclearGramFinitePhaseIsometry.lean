import GegenbauerFock.RealCompactGramActiveSingularModes

/-!
# V007 — actual finite positive-support singular phase isometry

For any bounded real Hilbert operator T and an orthonormal genuine
Gram eigenfamily of eigenvalues μ_i ≥ 0 (including zero modes),
normalize images ONLY on the subtype {i // 0 < μ_i}.
The source and target finite singular combinations have equal
inner products and exactly equal norms.

These are the finite-support isometry identities required to extend
the polar phase to the closure of the source positive spectral span.
No whole-space unitary, global partial isometry or closed-support
identification is asserted without a separate extension theorem.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open InnerProductSpace

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [InnerProductSpace ℝ E] [InnerProductSpace ℝ F]
variable [CompleteSpace E] [CompleteSpace F]
variable {ι : Type*}

/-- Any two independently orthonormal real Hilbert families induce
the same inner products of matching finite linear combinations. -/
theorem realOrthonormalFamilies_finite_phase_inner
    (b : ι → E) (c : ι → F)
    (hb : Orthonormal ℝ b) (hc : Orthonormal ℝ c)
    (s : Finset ι) (a d : ι → ℝ) :
    inner ℝ (∑ i ∈ s, a i • b i)
      (∑ i ∈ s, d i • b i) =
    inner ℝ (∑ i ∈ s, a i • c i)
      (∑ i ∈ s, d i • c i) := by
  have hsource := hb.inner_sum a d s
  have htarget := hc.inner_sum a d s
  exact hsource.trans htarget.symm

/-- Any two orthonormal real families induce an exact finite
partial-phase norm isometry, without matching their closed spans. -/
theorem realOrthonormalFamilies_finite_phase_norm
    (b : ι → E) (c : ι → F)
    (hb : Orthonormal ℝ b) (hc : Orthonormal ℝ c)
    (s : Finset ι) (a : ι → ℝ) :
    ‖∑ i ∈ s, a i • b i‖ =
      ‖∑ i ∈ s, a i • c i‖ := by
  have hi := realOrthonormalFamilies_finite_phase_inner
    b c hb hc s a a
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hi
  have hb0 : 0 ≤ ‖∑ i ∈ s, a i • b i‖ := norm_nonneg _
  have hc0 : 0 ≤ ‖∑ i ∈ s, a i • c i‖ := norm_nonneg _
  nlinarith

/-- For the ACTUAL Gram T†T, its positive spectral source/output
families have identical Gram matrices on every finite support.
Zero Gram eigenmodes are not normalized. -/
theorem realGram_positiveSupport_finite_phase_inner
    (T : E →L[ℝ] F)
    (b : ι → E) (hb : Orthonormal ℝ b)
    (mu : ι → ℝ) (hmu : ∀ i, 0 ≤ mu i)
    (heig : ∀ i, (T.adjoint ∘L T) (b i) = mu i • b i)
    (s : Finset {i : ι // 0 < mu i})
    (a d : {i : ι // 0 < mu i} → ℝ) :
    inner ℝ
      (∑ i ∈ s, a i • b i)
      (∑ i ∈ s, d i • b i) =
    inner ℝ
      (∑ i ∈ s, a i •
        ((Real.sqrt (mu i))⁻¹ • T (b i)))
      (∑ i ∈ s, d i •
        ((Real.sqrt (mu i))⁻¹ • T (b i))) := by
  have hsrc : Orthonormal ℝ
      (fun i : {i : ι // 0 < mu i} => b i) := by
    constructor
    · intro i
      exact hb.norm_eq_one i
    · intro i j hij
      apply hb.inner_eq_zero
      intro hval
      exact hij (Subtype.ext hval)
  have htgt : Orthonormal ℝ
      (fun i : {i : ι // 0 < mu i} =>
        (Real.sqrt (mu i))⁻¹ • T (b i)) :=
    realGram_positiveSupport_output_orthonormal_v007 T b hb mu hmu heig
  exact realOrthonormalFamilies_finite_phase_inner
    (fun i : {i : ι // 0 < mu i} => b i)
    (fun i : {i : ι // 0 < mu i} =>
      (Real.sqrt (mu i))⁻¹ • T (b i)) hsrc htgt s a d

/-- Actual finite positive Gram support polar phase: exact norm
isometry, including potentially unequal kernel/cokernel defects. -/
theorem realGram_positiveSupport_finite_phase_norm
    (T : E →L[ℝ] F)
    (b : ι → E) (hb : Orthonormal ℝ b)
    (mu : ι → ℝ) (hmu : ∀ i, 0 ≤ mu i)
    (heig : ∀ i, (T.adjoint ∘L T) (b i) = mu i • b i)
    (s : Finset {i : ι // 0 < mu i})
    (a : {i : ι // 0 < mu i} → ℝ) :
    ‖∑ i ∈ s, a i • b i‖ =
      ‖∑ i ∈ s, a i •
        ((Real.sqrt (mu i))⁻¹ • T (b i))‖ := by
  have hi :=
    realGram_positiveSupport_finite_phase_inner
      T b hb mu hmu heig s a a
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hi
  have h0a : 0 ≤ ‖∑ i ∈ s, a i • b i‖ := norm_nonneg _
  have h0b : 0 ≤ ‖∑ i ∈ s,
      a i • ((Real.sqrt (mu i))⁻¹ • T (b i))‖ := norm_nonneg _
  nlinarith

#print axioms GegenbauerFock.Ultraspherical.realOrthonormalFamilies_finite_phase_inner
#print axioms GegenbauerFock.Ultraspherical.realOrthonormalFamilies_finite_phase_norm
#print axioms GegenbauerFock.Ultraspherical.realGram_positiveSupport_finite_phase_inner
#print axioms GegenbauerFock.Ultraspherical.realGram_positiveSupport_finite_phase_norm

end GegenbauerFock.Ultraspherical
