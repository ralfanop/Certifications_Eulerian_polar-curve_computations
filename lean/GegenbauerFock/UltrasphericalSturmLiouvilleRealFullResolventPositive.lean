import GegenbauerFock.UltrasphericalSturmLiouvilleRealResolventSpectralGraph
import GegenbauerFock.UltrasphericalSturmLiouvilleRealEnergyNonpositive

/-!
# V007 — genuine positivity of the full Sturm positive resolvent

For λ>0, t>0 the canonical closed ultraspherical Sturm operator
has a nonpositive quadratic form and a bounded full-Hilbert resolvent R_t.
The exact graph relation yields the stronger positive energy bound

  t ⟨R_t f, R_t f⟩ ≤ ⟨R_t f, f⟩

for every genuine L² vector f. In particular R_t is positive
semidefinite. This adds a concrete spectral-theorem prerequisite
without assuming a discrete Gegenbauer eigenbasis.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- Genuine full-L² resolvent energy inequality derived from the
nonpositive quadratic form of the closed differential operator. -/
theorem sturmRealPositiveResolventFullCLM_inner_energy_bound
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (f : SturmH lam) :
    t * inner ℝ
      (sturmRealPositiveResolventFullCLM lam t hlam ht f)
      (sturmRealPositiveResolventFullCLM lam t hlam ht f) ≤
    inner ℝ
      (sturmRealPositiveResolventFullCLM lam t hlam ht f) f := by
  let A := sturmRealPartialOperator lam hlam
  let R := sturmRealPositiveResolventFullCLM lam t hlam ht
  obtain ⟨x, hx⟩ := (A.closure.mem_graph_iff').mp
    (sturmRealPositiveResolventFullCLM_closed_graph lam t hlam ht f)
  have hfirst : (x : SturmH lam) = R f := congrArg Prod.fst hx
  have hsecond : A.closure x = t • R f - f := congrArg Prod.snd hx
  have hnonpos :=
    sturmRealPartialOperator_closure_nonpositive lam hlam x
  rw [hfirst, hsecond] at hnonpos
  simp only [inner_sub_left, real_inner_smul_left] at hnonpos
  have hcomm : inner ℝ f (R f) = inner ℝ (R f) f :=
    (real_inner_comm f (R f)).symm
  rw [hcomm] at hnonpos
  exact sub_nonpos.mp hnonpos

/-- Positivity of the true all-L² bounded Sturm resolvent. -/
theorem sturmRealPositiveResolventFullCLM_inner_nonneg
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (f : SturmH lam) :
    0 ≤ inner ℝ
      (sturmRealPositiveResolventFullCLM lam t hlam ht f) f := by
  have henergy :=
    sturmRealPositiveResolventFullCLM_inner_energy_bound
      lam t hlam ht f
  have hself :
      0 ≤ inner ℝ
        (sturmRealPositiveResolventFullCLM lam t hlam ht f)
        (sturmRealPositiveResolventFullCLM lam t hlam ht f) :=
    real_inner_self_nonneg
  exact le_trans (mul_nonneg (le_of_lt ht) hself) henergy

/-- The genuine positive-shift resolvent has no nonzero kernel:
its closed-graph realization cannot send nonzero data to zero. -/
theorem sturmRealPositiveResolventFullCLM_kernel_zero
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (f : SturmH lam)
    (hf : sturmRealPositiveResolventFullCLM lam t hlam ht f = 0) :
    f = 0 := by
  let A := sturmRealPartialOperator lam hlam
  let R := sturmRealPositiveResolventFullCLM lam t hlam ht
  obtain ⟨x, hx⟩ := (A.closure.mem_graph_iff').mp
    (sturmRealPositiveResolventFullCLM_closed_graph lam t hlam ht f)
  have hfirst : (x : SturmH lam) = R f := congrArg Prod.fst hx
  have hsecond : A.closure x = t • R f - f :=
    congrArg Prod.snd hx
  have hxzero : x = 0 := Subtype.ext (hfirst.trans hf)
  rw [hxzero, hf] at hsecond
  simpa using hsecond.symm

/-- The full-L² bounded selfadjoint positive Sturm resolvent is
injective. Its inverse is the unbounded positive-shift operator
on the precisely certified closed Sturm domain. -/
theorem sturmRealPositiveResolventFullCLM_injective_via_kernel
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    Function.Injective
      (sturmRealPositiveResolventFullCLM lam t hlam ht) := by
  intro f g hfg
  apply sub_eq_zero.mp
  apply sturmRealPositiveResolventFullCLM_kernel_zero lam t hlam ht
    (f-g)
  rw [map_sub, hfg, sub_self]

/-- Strictly positive full-L² Sturm resolvent quadratic form for every
nonzero real datum, using the certified positive-shift graph and
the zero-kernel theorem. -/
theorem sturmRealPositiveResolventFullCLM_inner_pos
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (f : SturmH lam) (hf : f ≠ 0) :
    0 < inner ℝ
      (sturmRealPositiveResolventFullCLM lam t hlam ht f) f := by
  let R := sturmRealPositiveResolventFullCLM lam t hlam ht
  have hRne : R f ≠ 0 := by
    intro hzero
    exact hf (sturmRealPositiveResolventFullCLM_kernel_zero
      lam t hlam ht f hzero)
  have hself : 0 < inner ℝ (R f) (R f) :=
    real_inner_self_pos.mpr hRne
  have henergy :
      t * inner ℝ (R f) (R f) ≤ inner ℝ (R f) f :=
    sturmRealPositiveResolventFullCLM_inner_energy_bound
      lam t hlam ht f
  exact lt_of_lt_of_le (mul_pos ht hself) henergy

#print axioms GegenbauerFock.Ultraspherical.sturmRealPositiveResolventFullCLM_inner_energy_bound
#print axioms GegenbauerFock.Ultraspherical.sturmRealPositiveResolventFullCLM_inner_pos
#print axioms GegenbauerFock.Ultraspherical.sturmRealPositiveResolventFullCLM_inner_nonneg
#print axioms GegenbauerFock.Ultraspherical.sturmRealPositiveResolventFullCLM_kernel_zero
#print axioms GegenbauerFock.Ultraspherical.sturmRealPositiveResolventFullCLM_injective_via_kernel

end GegenbauerFock.Ultraspherical
