import GegenbauerFock.HSRightIdeal
import GegenbauerFock.GramNuclearTrace

/-!
# V007 — general source-basis / Fock-row Hilbert–Schmidt equivalence

For arbitrary complete complex Hilbert source E and a bounded operator
T : E → ℓ²(ℕ,ℂ), genuinely summable squared norms of all its
canonical coordinate rows imply *actual* Hilbert–Schmidt summability
over every complete Hilbert source basis.

This promotes V007's verified right-composition-of-rows result to a
basis-independent, infinite-dimensional S₂ right-ideal result, without
assuming an abstract Schatten API or finite-dimensionality.
-/

noncomputable section

namespace GegenbauerFock.FockEnergy

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Riesz–Parseval for EVERY bounded complex-linear scalar functional
on an arbitrary (possibly infinite-dimensional) complete Hilbert
space, with both genuine summability and the exact squared norm. -/
theorem functional_basis_energy
    (r : E →L[ℂ] ℂ)
    {ι : Type*} (b : HilbertBasis ι ℂ E) :
    Summable (fun i : ι => ‖r (b i)‖ ^ 2) ∧
    (∑' i : ι, ‖r (b i)‖ ^ 2) = ‖r‖ ^ 2 := by
  let m : E := (InnerProductSpace.toDual ℂ E).symm r
  have heq (i : ι) :
      ‖r (b i)‖ ^ 2 = ‖inner ℂ (b i) m‖ ^ 2 := by
    have hm : inner ℂ m (b i) = r (b i) := by
      simpa [m] using
        (InnerProductSpace.toDual_symm_apply (x := b i) (y := r))
    rw [← hm, norm_inner_symm]
  have hb :
      Summable (fun i : ι => ‖(b.repr m) i‖ ^ 2) := by
    simpa using (lp.memℓp (b.repr m)).summable
      (by norm_num : 0 < (2 : ENNReal).toReal)
  have hs : Summable (fun i : ι => ‖inner ℂ (b i) m‖ ^ 2) := by
    simpa only [HilbertBasis.repr_apply_apply] using hb
  constructor
  · exact hs.congr (fun i => (heq i).symm)
  · calc
      (∑' i : ι, ‖r (b i)‖ ^ 2) =
          ∑' i : ι, ‖inner ℂ (b i) m‖ ^ 2 := tsum_congr heq
      _ = ‖m‖ ^ 2 := hilbertBasis_parseval b m
      _ = ‖r‖ ^ 2 := by
        have hmnorm : ‖m‖ = ‖r‖ := by
          exact (InnerProductSpace.toDual ℂ E).symm.norm_map r
        rw [hmnorm]

/-- General Fock-row characterization of the infinite-dimensional
Hilbert–Schmidt class: every complete source Hilbert basis has a
summable squared image-norm series equal to the canonical row energy.
No probability, ultraspherical, or Kummer assumptions are required. -/
theorem summableRows_iff_sourceBasis_energy
    (T : E →L[ℂ] InfiniteAnalysis.FockCoefficients)
    (hrows : Summable (fun n : ℕ =>
      ‖SummableRowsCompact.row T n‖ ^ 2))
    {ι : Type*} (b : HilbertBasis ι ℂ E) :
    Summable (fun i : ι => ‖T (b i)‖ ^ 2) ∧
    (∑' i : ι, ‖T (b i)‖ ^ 2) =
      ∑' n : ℕ, ‖SummableRowsCompact.row T n‖ ^ 2 := by
  let w : ℕ → ι → ℝ := fun n i => ‖(T (b i)) n‖ ^ 2
  have hinner (n : ℕ) : Summable (w n) := by
    exact (functional_basis_energy (SummableRowsCompact.row T n) b).1.congr
      (fun i => rfl)
  have hrow (n : ℕ) :
      (∑' i : ι, w n i) =
        ‖SummableRowsCompact.row T n‖ ^ 2 := by
    exact (functional_basis_energy (SummableRowsCompact.row T n) b).2
  have houter : Summable (fun n : ℕ => ∑' i : ι, w n i) :=
    hrows.congr (fun n => (hrow n).symm)
  have hdouble : Summable (Function.uncurry w) := by
    exact (summable_prod_of_nonneg
      (f := Function.uncurry w) (fun p => sq_nonneg _)).2
        ⟨hinner, houter⟩
  have hswap : Summable (fun p : ι × ℕ => w p.2 p.1) := by
    simpa [Function.uncurry] using hdouble.prod_symm
  have hreverse : Summable (fun i : ι => ∑' n : ℕ, w n i) :=
    ((summable_prod_of_nonneg
      (f := fun p : ι × ℕ => w p.2 p.1)
      (fun p => sq_nonneg _)).1 hswap).2
  have hin (i : ι) :
      ‖T (b i)‖ ^ 2 = ∑' n : ℕ, w n i := by
    simpa [w] using
      (lp.norm_rpow_eq_tsum
        (by norm_num : 0 < (2 : ENNReal).toReal) (T (b i))).symm
  constructor
  · exact hreverse.congr (fun i => (hin i).symm)
  · calc
      (∑' i : ι, ‖T (b i)‖ ^ 2) =
          ∑' i : ι, ∑' n : ℕ, w n i := tsum_congr hin
      _ = ∑' n : ℕ, ∑' i : ι, w n i := hdouble.tsum_comm
      _ = ∑' n : ℕ, ‖SummableRowsCompact.row T n‖ ^ 2 :=
        tsum_congr hrow

#print axioms GegenbauerFock.FockEnergy.functional_basis_energy
#print axioms GegenbauerFock.FockEnergy.summableRows_iff_sourceBasis_energy

end GegenbauerFock.FockEnergy
