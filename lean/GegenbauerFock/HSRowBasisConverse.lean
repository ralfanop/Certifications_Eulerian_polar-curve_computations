import GegenbauerFock.HSRowBasisGeneral

/-!
# V007: exact bidirectional general Hilbert–Schmidt criterion for maps to ℓ²

For any complete complex Hilbert space E and bounded T:E → ℓ², and
any complete Hilbert basis b, the canonical output rows are square
summable if and only if the image norms of b are square summable.
Both sums then coincide. The converse implication is a genuine
Tonelli argument on the nonnegative matrix ‖(T(b_i))_n‖².

No probability-law assumption, finite-dimensionality hypothesis,
Physlib external dependency, or new axiom is used.
-/

noncomputable section

namespace GegenbauerFock.FockEnergy

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A square-summable image of ANY complete source Hilbert basis
forces square-summability of EVERY canonical ℓ² output row. -/
theorem summableRows_of_sourceBasis_energy
    (T : E →L[ℂ] InfiniteAnalysis.FockCoefficients)
    {ι : Type*} (b : HilbertBasis ι ℂ E)
    (hb : Summable (fun i : ι => ‖T (b i)‖ ^ 2)) :
    Summable (fun n : ℕ =>
      ‖SummableRowsCompact.row T n‖ ^ 2) := by
  let w : ι → ℕ → ℝ := fun i n => ‖(T (b i)) n‖ ^ 2
  have hinner (i : ι) : Summable (w i) := by
    change Summable (fun n : ℕ => ‖(T (b i)) n‖ ^ 2)
    simpa using
      (lp.memℓp (T (b i))).summable
        (by norm_num : 0 < (2 : ENNReal).toReal)
  have hrow (i : ι) :
      (∑' n : ℕ, w i n) = ‖T (b i)‖ ^ 2 := by
    simpa [w] using
      (lp.norm_rpow_eq_tsum
        (by norm_num : 0 < (2 : ENNReal).toReal)
        (T (b i))).symm
  have houter : Summable (fun i : ι => ∑' n : ℕ, w i n) :=
    hb.congr (fun i => (hrow i).symm)
  have hdouble : Summable (Function.uncurry w) := by
    exact (summable_prod_of_nonneg
      (f := Function.uncurry w) (fun p => sq_nonneg _)).2
        ⟨hinner, houter⟩
  have hswap : Summable (fun p : ℕ × ι => w p.2 p.1) := by
    simpa [Function.uncurry] using hdouble.prod_symm
  have hreverse : Summable (fun n : ℕ => ∑' i : ι, w i n) :=
    ((summable_prod_of_nonneg
      (f := fun p : ℕ × ι => w p.2 p.1)
      (fun p => sq_nonneg _)).1 hswap).2
  have hcolumn (n : ℕ) :
      (∑' i : ι, w i n) =
        ‖SummableRowsCompact.row T n‖ ^ 2 :=
    (functional_basis_energy (SummableRowsCompact.row T n) b).2
  exact hreverse.congr (fun n => hcolumn n)

/-- EXACT infinite-dimensional S₂ equivalence for bounded
T:E → ℓ², uniformly over an arbitrary complete source Hilbert basis.
This is a genuine converse to `summableRows_iff_sourceBasis_energy`. -/
theorem sourceBasis_HS_iff_summableRows
    (T : E →L[ℂ] InfiniteAnalysis.FockCoefficients)
    {ι : Type*} (b : HilbertBasis ι ℂ E) :
    Summable (fun i : ι => ‖T (b i)‖ ^ 2) ↔
      Summable (fun n : ℕ =>
        ‖SummableRowsCompact.row T n‖ ^ 2) := by
  constructor
  · exact summableRows_of_sourceBasis_energy T b
  · intro hrows
    exact (summableRows_iff_sourceBasis_energy T hrows b).1

/-- Equality of the two Schatten-Hilbert–Schmidt energies,
whenever source summability is established rather than assumed
at the canonical ℓ² output rows. -/
theorem sourceBasis_HS_energy_eq_rows
    (T : E →L[ℂ] InfiniteAnalysis.FockCoefficients)
    {ι : Type*} (b : HilbertBasis ι ℂ E)
    (hb : Summable (fun i : ι => ‖T (b i)‖ ^ 2)) :
    (∑' i : ι, ‖T (b i)‖ ^ 2) =
      ∑' n : ℕ, ‖SummableRowsCompact.row T n‖ ^ 2 :=
  (summableRows_iff_sourceBasis_energy T
    (summableRows_of_sourceBasis_energy T b hb) b).2

/-- True basis independence of the infinite-dimensional Schatten-S₂
condition: finite squared energy for one complete source Hilbert basis
implies finite squared energy for EVERY other complete Hilbert basis,
and their sums agree exactly, even when their index types differ. -/
theorem sourceBasis_HS_basis_independent
    (T : E →L[ℂ] InfiniteAnalysis.FockCoefficients)
    {ι κ : Type*}
    (b : HilbertBasis ι ℂ E) (c : HilbertBasis κ ℂ E)
    (hb : Summable (fun i : ι => ‖T (b i)‖ ^ 2)) :
    Summable (fun j : κ => ‖T (c j)‖ ^ 2) ∧
    (∑' i : ι, ‖T (b i)‖ ^ 2) =
      ∑' j : κ, ‖T (c j)‖ ^ 2 := by
  have hrows := summableRows_of_sourceBasis_energy T b hb
  have hb_eq := (summableRows_iff_sourceBasis_energy T hrows b).2
  have hc := summableRows_iff_sourceBasis_energy T hrows c
  exact ⟨hc.1, hb_eq.trans hc.2.symm⟩

#print axioms GegenbauerFock.FockEnergy.summableRows_of_sourceBasis_energy
#print axioms GegenbauerFock.FockEnergy.sourceBasis_HS_iff_summableRows
#print axioms GegenbauerFock.FockEnergy.sourceBasis_HS_energy_eq_rows
#print axioms GegenbauerFock.FockEnergy.sourceBasis_HS_basis_independent

end GegenbauerFock.FockEnergy
