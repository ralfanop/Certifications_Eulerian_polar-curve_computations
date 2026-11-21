import Manuscript15.TerminalAnalyticGraph20261119
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
M15 §6.2, terminal all-order coefficients.  This module aims to certify the
finite composition formulas and triangular inverse recurrence for the
actual analytic local inverse and terminal graph, as a prerequisite of
the closed Lagrange–Bürmann coefficient extraction formula.
-/

open Filter Topology
open scoped BigOperators
noncomputable section

namespace Manuscript15.TerminalLagrange
open Manuscript15

abbrev RealSeries := FormalMultilinearSeries ℝ ℝ ℝ

/-- Scalar coefficient of a one-dimensional formal multilinear series. -/
def scalarCoeff (p : RealSeries) (n : ℕ) : ℝ := p n (fun _ => 1)

/-- Each one-dimensional multilinear map is determined by its value on ones. -/
theorem scalar_eval {n : ℕ}
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin n => ℝ) ℝ)
    (v : Fin n → ℝ) :
    f v = f (fun _ => 1) * ∏ j, v j := by
  have h := f.toMultilinearMap.map_smul_univ v (fun _ => (1 : ℝ))
  change f (fun i => v i • (1 : ℝ)) = (∏ i, v i) • f (fun _ => 1) at h
  simpa only [smul_eq_mul, mul_one, mul_comm] using h

/-- Contribution of an ordered composition of the target degree. -/
def compositionTerm (p q : RealSeries) {n : ℕ} (c : Composition n) : ℝ :=
  scalarCoeff p c.length * ∏ j : Fin c.length, scalarCoeff q (c.blocksFun j)

/-- All-order scalar coefficient formula for composition at matching centres. -/
theorem coeff_comp (p q : RealSeries) (n : ℕ) :
    scalarCoeff (p.comp q) n = ∑ c : Composition n, compositionTerm p q c := by
  classical
  simp only [scalarCoeff, FormalMultilinearSeries.comp,
    ContinuousMultilinearMap.sum_apply, FormalMultilinearSeries.compAlongComposition_apply]
  apply Finset.sum_congr rfl
  intro c _
  rw [scalar_eval]
  rfl

/-- Exactly one term can involve the degree-n coefficient of the inner series. -/
theorem single_term (p q : RealSeries) {n : ℕ} (hn : 0 < n) :
    compositionTerm p q (Composition.single n hn) =
      scalarCoeff p 1 * scalarCoeff q n := by
  simp only [compositionTerm, Composition.single_length, Fin.prod_univ_one,
    Composition.single_blocksFun]

/-- Every nonsingle composition involves only strictly lower degrees. -/
theorem lower_degree {n : ℕ} (hn : 0 < n) (c : Composition n)
    (hc : c ≠ Composition.single n hn) (j : Fin c.length) :
    c.blocksFun j < n :=
  (Composition.ne_single_iff hn).mp hc j

/-- Explicit triangular recursion for the scalar coefficients of a reverse
composition. The constant/linear identity series is centred at x. -/
theorem inverse_coeff_recurrence (p q : RealSeries) (x : ℝ)
    (hp : scalarCoeff p 1 ≠ 0)
    (hi : p.comp q = FormalMultilinearSeries.id ℝ ℝ x)
    (n : ℕ) (hn : 0 < n) :
    scalarCoeff q n =
      (scalarCoeff (FormalMultilinearSeries.id ℝ ℝ x) n -
        ∑ c ∈ (Finset.univ : Finset (Composition n)).erase (Composition.single n hn),
          compositionTerm p q c) / scalarCoeff p 1 := by
  classical
  have hs := coeff_comp p q n
  rw [hi] at hs
  have he := Finset.sum_erase_add (Finset.univ : Finset (Composition n))
    (compositionTerm p q) (Finset.mem_univ (Composition.single n hn))
  rw [single_term p q hn] at he
  apply (eq_div_iff hp).2
  rw [mul_comm]
  linarith

/-- At n≥2 the identity contribution vanishes, giving the homogeneous
lower-degree recursion used for actual series reversion. -/
theorem inverse_coeff_succ (p q : RealSeries) (x : ℝ)
    (hp : scalarCoeff p 1 ≠ 0)
    (hi : p.comp q = FormalMultilinearSeries.id ℝ ℝ x)
    (n : ℕ) (hn : 1 < n) :
    scalarCoeff q n =
      -(∑ c ∈ (Finset.univ : Finset (Composition n)).erase
        (Composition.single n (by omega : 0 < n)),
          compositionTerm p q c) / scalarCoeff p 1 := by
  have h := inverse_coeff_recurrence p q x hp hi n (by omega)
  have hz : scalarCoeff (FormalMultilinearSeries.id ℝ ℝ x) n = 0 := by
    simp [scalarCoeff, FormalMultilinearSeries.id_apply_of_one_lt, hn]
  rw [hz, zero_sub] at h
  exact h

/-- Real analytic series of an actual inverse and reconstructed terminal
graph. No formal inverse is postulated: the local inverse is the one
constructed in TerminalAnalyticGraph20261119. -/
theorem exists_terminal_all_order_series (a : ℝ) (ha : a ≠ 0)
    (M : ℕ) (hM : 2 ≤ M) :
    ∃ (T : ℝ → ℝ) (p q r : RealSeries),
      T (XConv a M (2 * Real.pi)) = 2 * Real.pi ∧
      HasFPowerSeriesAt (XConv a M) p (2 * Real.pi) ∧
      HasFPowerSeriesAt T q (XConv a M (2 * Real.pi)) ∧
      HasFPowerSeriesAt (YConv a M) r (2 * Real.pi) ∧
      scalarCoeff p 1 = a ∧
      scalarCoeff q 1 = a⁻¹ ∧
      p.comp q = FormalMultilinearSeries.id ℝ ℝ (XConv a M (2 * Real.pi)) ∧
      HasFPowerSeriesAt (YConv a M ∘ T) (r.comp q) (XConv a M (2 * Real.pi)) ∧
      (∀ n, scalarCoeff (r.comp q) n = ∑ c : Composition n, compositionTerm r q c) := by
  obtain ⟨T, hTa, hT0, hTd, hleft, hright⟩ :=
    TerminalAnalytic.exists_analytic_inverse a ha M hM
  obtain ⟨p, hp⟩ := TerminalAnalytic.X_analytic a M
  obtain ⟨q, hq⟩ := hTa
  obtain ⟨r, hr⟩ := TerminalAnalytic.Y_analytic a M
  have hp' : HasFPowerSeriesAt (XConv a M) p (T (XConv a M (2 * Real.pi))) := by
    rw [hT0]
    exact hp
  have hr' : HasFPowerSeriesAt (YConv a M) r (T (XConv a M (2 * Real.pi))) := by
    rw [hT0]
    exact hr
  have hid : HasFPowerSeriesAt (fun x : ℝ => x)
      (FormalMultilinearSeries.id ℝ ℝ (XConv a M (2 * Real.pi)))
      (XConv a M (2 * Real.pi)) :=
    (ContinuousLinearMap.id ℝ ℝ).hasFPowerSeriesAt _
  have hcomp := (hp'.comp hq).eq_formalMultilinearSeries_of_eventually hid hright
  have hp1 : scalarCoeff p 1 = a := by
    change p 1 (fun _ => 1) = a
    rw [← hp.deriv]
    exact convolution_endpoint_X_deriv a M hM
  have hq1 : scalarCoeff q 1 = a⁻¹ := by
    change q 1 (fun _ => 1) = a⁻¹
    rw [← hq.deriv]
    exact hTd.hasDerivAt.deriv
  exact ⟨T, p, q, r, hT0, hp, hq, hr, hp1, hq1, hcomp, hr'.comp hq, coeff_comp r q⟩

end Manuscript15.TerminalLagrange

#print axioms Manuscript15.TerminalLagrange.scalar_eval
#print axioms Manuscript15.TerminalLagrange.coeff_comp
#print axioms Manuscript15.TerminalLagrange.single_term
#print axioms Manuscript15.TerminalLagrange.lower_degree
#print axioms Manuscript15.TerminalLagrange.inverse_coeff_recurrence
#print axioms Manuscript15.TerminalLagrange.inverse_coeff_succ
#print axioms Manuscript15.TerminalLagrange.exists_terminal_all_order_series
