import GegenbauerFock.UltrasphericalSturmLiouvillePolynomialEnergyLeibniz
import GegenbauerFock.UltrasphericalSturmLiouvilleRealClosedSymmetry
import GegenbauerFock.UltrasphericalSturmLiouvilleRealL2Green

/-!
# V007 — carré-du-champ and nonpositivity on the actual real L² domain

Combine the exact polynomial Leibniz identity with genuine weighted
Green integration and true support of the ultraspherical probability
measure on [-1,1]. The resulting Dirichlet energy formula is

   ∫ (Lλ p) p dνλ = - ∫ (1-u²) (p'(u))² dνλ ≤ 0.

This supplies actual negative quadratic form, not an assumption.
Its transfer to the closure uses graph continuity, not a hypothetical
spectral eigenbasis.

All assertions await the dedicated pinned Lean CI kernel audit.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory Polynomial

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

private def sturmEnergyPolynomial (p : ℝ[X]) : ℝ[X] :=
  (1-X^2) * derivative p * derivative p

/-- Genuine exact Dirichlet energy formula on the full real
polynomial core of the Beta-pushforward ultraspherical law. -/
theorem sturmPolynomial_dirichlet_energy_integral
    (lam : ℝ) (hlam : 0 < lam) (p : ℝ[X]) :
    (∫ u : ℝ,
      (sturmPolynomial lam p).eval u * p.eval u ∂(measure lam)) =
      - (∫ u : ℝ, (sturmEnergyPolynomial p).eval u ∂(measure lam)) := by
  have hp :
      Integrable (fun u : ℝ =>
        (sturmPolynomial lam p).eval u * p.eval u) (measure lam) :=
    sturmPolynomial_operator_product_integrable lam hlam p p
  have he :
      Integrable (fun u : ℝ =>
        (sturmEnergyPolynomial p).eval u) (measure lam) :=
    sturmPolynomial_eval_integrable lam hlam (sturmEnergyPolynomial p)
  have hpoint (u : ℝ) :
      (sturmPolynomial lam (p*p)).eval u =
        2 * ((sturmPolynomial lam p).eval u * p.eval u) +
          2 * (sturmEnergyPolynomial p).eval u := by
    rw [sturmPolynomial_square_leibniz]
    simp only [sturmEnergyPolynomial, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
      Polynomial.eval_one, Polynomial.eval_pow, Polynomial.eval_X]
    ring
  have hsum :
      (∫ u : ℝ, (sturmPolynomial lam (p*p)).eval u ∂(measure lam)) =
        2 * (∫ u : ℝ,
          (sturmPolynomial lam p).eval u * p.eval u ∂(measure lam)) +
          2 * (∫ u : ℝ, (sturmEnergyPolynomial p).eval u ∂(measure lam)) := by
    calc
      _ = ∫ u : ℝ,
          (2 : ℝ) * ((sturmPolynomial lam p).eval u * p.eval u) +
            2 * (sturmEnergyPolynomial p).eval u ∂(measure lam) := by
        apply integral_congr_ae
        filter_upwards [] with u
        exact hpoint u
      _ = _ := by
        rw [integral_add (hp.const_mul 2) (he.const_mul 2),
          integral_const_mul, integral_const_mul]
  have hzero := sturmPolynomial_integral_zero lam hlam (p*p)
  rw [hzero] at hsum
  linarith

/-- The Dirichlet energy is genuinely nonnegative, because the
actual beta-pushforward probability law is supported on [-1,1]. -/
theorem sturmPolynomial_dirichlet_energy_nonneg
    (lam : ℝ) (p : ℝ[X]) :
    0 ≤ ∫ u : ℝ, (sturmEnergyPolynomial p).eval u ∂(measure lam) := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_mem_unit_interval lam] with u hu
  have hs : 0 ≤ (1-u)*(u+1) := by
    apply mul_nonneg
    · linarith [hu.2]
    · linarith [hu.1]
  have hsq : 0 ≤ (1 : ℝ) - u^2 := by nlinarith
  have hpos :
      0 ≤ ((1 : ℝ) - u^2) * (p.derivative.eval u)^2 :=
    mul_nonneg hsq (sq_nonneg _)
  simpa [sturmEnergyPolynomial, Polynomial.eval_mul,
    Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X] using hpos

/-- Concrete real-polynomial Sturm quadratic form is nonpositive
for ALL degrees, with no spectral semiboundedness hypothesis. -/
theorem sturmPolynomial_dirichlet_form_nonpos
    (lam : ℝ) (hlam : 0 < lam) (p : ℝ[X]) :
    (∫ u : ℝ,
      (sturmPolynomial lam p).eval u * p.eval u ∂(measure lam)) ≤ 0 := by
  rw [sturmPolynomial_dirichlet_energy_integral lam hlam p]
  have h := sturmPolynomial_dirichlet_energy_nonneg lam p
  linarith

/-- The actual weighted real-L² polynomial Sturm quadratic form
is nonpositive, not just its finite moment matrix. -/
theorem sturmRealPolynomialLp_sturm_nonpos
    (lam : ℝ) (hlam : 0 < lam) (p : ℝ[X]) :
    inner ℝ
      (sturmRealPolynomialLp lam hlam (sturmPolynomial lam p))
      (sturmRealPolynomialLp lam hlam p) ≤ 0 := by
  rw [sturmRealPolynomialLp_inner_eq_integral]
  exact sturmPolynomial_dirichlet_form_nonpos lam hlam p

/-- The exact real polynomial-image Sturm partial operator is
nonpositive on its genuine densely defined L² domain. -/
theorem sturmRealPartialOperator_nonpositive
    (lam : ℝ) (hlam : 0 < lam)
    (x : (sturmRealPartialOperator lam hlam).domain) :
    inner ℝ (sturmRealPartialOperator lam hlam x)
      (x : SturmH lam) ≤ 0 := by
  let p := sturmRealDomainRepresentative lam hlam
    (x : sturmRealPolynomialDomain lam hlam)
  have hrep :
      sturmRealPolynomialLp lam hlam p = (x : SturmH lam) :=
    sturmRealDomainRepresentative_spec lam hlam x
  have haction :
      sturmRealPartialOperator lam hlam x =
        sturmRealPolynomialLp lam hlam (sturmPolynomial lam p) := rfl
  rw [haction, ← hrep]
  exact sturmRealPolynomialLp_sturm_nonpos lam hlam p

/-- Nonpositivity persists on the canonical CLOSED graph by
continuity of the actual Hilbert inner product. -/
theorem sturmRealPartialOperator_closure_nonpositive
    (lam : ℝ) (hlam : 0 < lam)
    (x : (sturmRealPartialOperator lam hlam).closure.domain) :
    inner ℝ ((sturmRealPartialOperator lam hlam).closure x)
      (x : SturmH lam) ≤ 0 := by
  let A := sturmRealPartialOperator lam hlam
  have hc : Continuous
      (fun w : SturmH lam × SturmH lam => inner ℝ w.2 w.1) := by
    fun_prop
  have hgraph :
      (A.graph : Set (SturmH lam × SturmH lam)) ⊆
        {w | inner ℝ w.2 w.1 ≤ 0} := by
    intro w hw
    obtain ⟨u, hu1, hu2⟩ := (A.mem_graph_iff).mp hw
    have hw_eq : w = ((u : SturmH lam), A u) :=
      Prod.ext hu1.symm hu2.symm
    rw [hw_eq]
    exact sturmRealPartialOperator_nonpositive lam hlam u
  have hclosure :
      (A.graph.topologicalClosure : Set (SturmH lam × SturmH lam)) ⊆
        {w | inner ℝ w.2 w.1 ≤ 0} := by
    change closure (A.graph : Set (SturmH lam × SturmH lam)) ⊆ _
    exact closure_minimal hgraph (isClosed_le hc continuous_const)
  have hx :
      (((x : SturmH lam), A.closure x) :
        SturmH lam × SturmH lam) ∈
        (A.graph.topologicalClosure :
          Set (SturmH lam × SturmH lam)) := by
    rw [(sturmRealPartialOperator_isClosable lam hlam).graph_closure_eq_closure_graph]
    exact A.closure.mem_graph x
  exact hclosure hx

#print axioms GegenbauerFock.Ultraspherical.sturmPolynomial_dirichlet_energy_integral
#print axioms GegenbauerFock.Ultraspherical.sturmPolynomial_dirichlet_energy_nonneg
#print axioms GegenbauerFock.Ultraspherical.sturmPolynomial_dirichlet_form_nonpos
#print axioms GegenbauerFock.Ultraspherical.sturmRealPolynomialLp_sturm_nonpos
#print axioms GegenbauerFock.Ultraspherical.sturmRealPartialOperator_nonpositive
#print axioms GegenbauerFock.Ultraspherical.sturmRealPartialOperator_closure_nonpositive

end GegenbauerFock.Ultraspherical
