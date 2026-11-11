import Mathlib

/-!
# Priority 3 — Cauchy convergence of finite compression determinants
# from dense finite-rank convergence and uniform-in-N equicontinuity

For an arbitrary pseudometric domain E, a dense set s ⊆ E,
and a sequence of complex scalar functionals Dₙ:E→ℂ, if
  (1) for each x∈s, the complex sequence Dₙ(x) is Cauchy;
  (2) Dₙ are equicontinuous at every x, uniformly in n;
then Dₙ(x) is Cauchy at EVERY x∈E.

This standard but critical two-epsilon completion argument is a
separate kernel-certified obligation for the universal CFC Schatten-S₁
Fredholm determinant, where E is the genuine trace-class Banach
space, s is the dense finite-nuclear sector, and Dₙ are the actual
finite Hilbert compression determinants. It does not assume
unproved convergence, global uniform continuity of the determinant,
or finite exact optimal rank-one presentations.
-/

noncomputable section

namespace Manuscript14Priority3.DenseUniformCauchy

open Filter Topology

variable {E : Type*} [PseudoMetricSpace E]

/-- Pointwise Cauchy convergence on a dense set propagates to the
whole metric domain under actual uniform-in-n equicontinuity at
each point, without any compactness or dimension hypothesis. -/
theorem cauchySeq_everywhere_of_dense_equicontinuous
    (s : Set E) (hs : Dense s) (D : ℕ → E → ℂ)
    (hfinite : ∀ x ∈ s, CauchySeq (fun n : ℕ => D n x))
    (hequi : ∀ x : E, ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧
        ∀ y : E, dist x y < δ →
          ∀ n : ℕ, dist (D n x) (D n y) < ε) :
    ∀ x : E, CauchySeq (fun n : ℕ => D n x) := by
  intro x
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hthird : 0 < ε / 3 := by positivity
  obtain ⟨δ, hδ, hsmall⟩ := hequi x (ε / 3) hthird
  obtain ⟨y, hy, hxy⟩ := hs.exists_dist_lt x hδ
  obtain ⟨N, hN⟩ :=
    (Metric.cauchySeq_iff.mp (hfinite y hy)) (ε / 3) hthird
  refine ⟨N, ?_⟩
  intro m hm n hn
  have hmxy : dist (D m x) (D m y) < ε / 3 :=
    hsmall y hxy m
  have hnxy : dist (D n y) (D n x) < ε / 3 := by
    simpa only [dist_comm] using hsmall y hxy n
  have hmiddle : dist (D m y) (D n y) < ε / 3 :=
    hN m hm n hn
  calc
    dist (D m x) (D n x) ≤
        dist (D m x) (D m y) +
          dist (D m y) (D n x) :=
      dist_triangle _ _ _
    _ ≤ dist (D m x) (D m y) +
          (dist (D m y) (D n y) + dist (D n y) (D n x)) := by
        linarith only [dist_triangle (D m y) (D n y) (D n x)]
    _ < ε := by linarith

/-- In the complete complex codomain the preceding Cauchy result
provides an actual limit at EVERY point of E. -/
theorem exists_complex_limit_of_dense_equicontinuous
    (s : Set E) (hs : Dense s) (D : ℕ → E → ℂ)
    (hfinite : ∀ x ∈ s, CauchySeq (fun n : ℕ => D n x))
    (hequi : ∀ x : E, ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧
        ∀ y : E, dist x y < δ →
          ∀ n : ℕ, dist (D n x) (D n y) < ε) :
    ∀ x : E, ∃ L : ℂ,
      Tendsto (fun n : ℕ => D n x) atTop (𝓝 L) := by
  intro x
  exact cauchySeq_tendsto_of_complete
    (cauchySeq_everywhere_of_dense_equicontinuous
      s hs D hfinite hequi x)

#print axioms Manuscript14Priority3.DenseUniformCauchy.cauchySeq_everywhere_of_dense_equicontinuous
#print axioms Manuscript14Priority3.DenseUniformCauchy.exists_complex_limit_of_dense_equicontinuous

end Manuscript14Priority3.DenseUniformCauchy
