import Mathlib

open Filter Topology
namespace M16KreinOperator

-- Proposition 9.12: actual Hilbert topology and dense domains.
theorem dense_transport {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    (u : E ≃ₜ F) (s : Set E) (hs : Dense s) : Dense (u '' s) := by
  have h : Set.univ ⊆ closure (u '' s) := by
    intro z hz
    have hm : u.symm z ∈ closure s := hs (u.symm z)
    have hi : u (u.symm z) ∈ u '' closure s := ⟨u.symm z, hm, rfl⟩
    have hc := u.continuous.image_closure_subset_closure_image hi
    simpa only [Homeomorph.apply_symm_apply] using hc
  intro z
  exact h (Set.mem_univ z)

-- If the two closed graphs are the closure of one common core graph,
-- they coincide; the application to a concrete Dirac core is separate.
theorem core_closure_unique {E : Type*} [TopologicalSpace E]
    (G G' C : Set (E × E)) (h : closure C = G) (h' : closure C = G') :
    G = G' := h.symm.trans h'

-- Heat smoothing: finite spectral cutoffs are compact and their norm
-- limit is compact. The geometric spectral decomposition supplies the
-- cutoffs and the estimate in the application.
theorem heat_limit_compact {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    (H : E →L[ℝ] E) (cut : ℕ → E →L[ℝ] E)
    (hc : ∀ n, IsCompactOperator (cut n : E → E))
    (hl : Tendsto cut atTop (𝓝 H)) :
    IsCompactOperator (H : E → E) := by
  exact isCompactOperator_of_tendsto hl (Filter.Eventually.of_forall hc)

-- Finite-dimensional factorization of each cutoff.
theorem cutoff_compact {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (p : E →L[ℝ] F) (j : F →L[ℝ] E) :
    IsCompactOperator (j.comp p : E → E) := by
  have hp : IsCompactOperator (p : E → F) := by
    first | exact isCompactOperator_of_locallyCompactSpace_rng p
          | exact isCompactOperator_of_locallyCompactSpace_dom p
  exact hp.clm_comp j

-- The two opposite orderings of heat smoothing and bounded maps.
theorem smoothed_couplings_compact {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (H : E →L[ℝ] E) (m : E →L[ℝ] F) (n : F →L[ℝ] E)
    (hH : IsCompactOperator (H : E → E)) :
    IsCompactOperator (m.comp H : E → F) ∧
      IsCompactOperator (H.comp n : F → E) :=
  ⟨hH.clm_comp m, hH.comp_clm n⟩

-- Uniform smallness of the heat multipliers above a spectral cutoff.
theorem heat_tail (eps cutoff lam : ℝ) (he : 0 ≤ eps) (hl : cutoff ≤ lam) :
    Real.exp (-eps * lam) ≤ Real.exp (-eps * cutoff) := by
  apply Real.exp_le_exp.mpr
  nlinarith only [mul_nonneg he (sub_nonneg.mpr hl)]

-- Real-pairing version of the physical factor -2 in Proposition 9.13.
theorem physical_pairing {E F : Type*}
    (pE : E → E → ℝ) (pF : F → F → ℝ)
    (X : F → E) (Y : E → F) (J : F → E) (e : ℝ)
    (hX : ∀ v a, pE (X v) a = -2*e*pE (J v) a)
    (hY : ∀ v a, pF v (Y a) = e*pE (J v) a) :
    ∀ v a, pE (X v) a = -2*pF v (Y a) := by
  intro v a
  rw [hX, hY]
  ring

-- Weighted adjoint on full block graphs.  The exact diagonal-adjoint
-- graph equivalences are the assumptions of Proposition 9.13.
theorem weighted_block_graph {E F : Type*}
    [AddCommGroup E] [AddCommGroup F]
    (pE : E → E → ℝ) (pF : F → F → ℝ)
    (GA : Set (E × E)) (GD : Set (F × F))
    (X : F → E) (Y : E → F)
    (ha : ∀ a b c, pE (a+b) c = pE a c + pE b c)
    (hd : ∀ a b c, pF (a+b) c = pF a c + pF b c)
    (hsE : ∀ a b, pE a b = pE b a)
    (hsF : ∀ a b, pF a b = pF b a)
    (hX : ∀ v a, pE (X v) a = -2*pF v (Y a))
    (u v : E) (s t : F)
    (hu : (u,v) ∈ GA) (hs : (s,t) ∈ GD)
    (hA : ∀ a b, (a,b) ∈ GA → pE b u = pE a v)
    (hD : ∀ a b, (a,b) ∈ GD → pF b s = pF a t) :
    ∀ a b c d, (a,b) ∈ GA → (c,d) ∈ GD →
      pE (b+X c) u - 2*pF (d+Y a) s =
        pE a (v+X s) - 2*pF c (t+Y u) := by
  intro a b c d hab hcd
  rw [ha, hd, hX, hA a b hab, hD c d hcd]
  rw [hsE a (v+X s), ha, hsE v a, hX, hsF s (Y a),
      hsF c (t+Y u), hd, hsF t c, hsF (Y u) c]
  ring

-- Banach-algebra Neumann inversion and explicit norm bound.
theorem neumann_inverse {R : Type*} [NormedRing R] [CompleteSpace R]
    [NormOneClass R] (k : R) (hk : ‖k‖ < 1) :
    ∃ v : R, (1-k)*v = 1 ∧ v*(1-k) = 1 ∧
      ‖v‖ ≤ 1/(1-‖k‖) := by
  let u : Rˣ := Units.oneSub k hk
  have hu : (u : R) = 1-k := by rfl
  let v : R := ↑u⁻¹
  have h1 : (1-k)*v = 1 := by rw [← hu]; simp [v]
  have h2 : v*(1-k) = 1 := by rw [← hu]; simp [v]
  have hv : v = 1+k*v := by
    calc
      v = (1-k)*v + k*v := by noncomm_ring
      _ = 1+k*v := by rw [h1]
  have hn : ‖v‖ ≤ 1 + ‖k‖*‖v‖ := by
    calc
      ‖v‖ = ‖1+k*v‖ := congrArg norm hv
      _ ≤ ‖(1:R)‖+‖k*v‖ := norm_add_le _ _
      _ ≤ 1+‖k‖*‖v‖ := by rw [norm_one]; exact add_le_add_left (norm_mul_le _ _) _
  refine ⟨v,h1,h2,?_⟩
  apply (le_div_iff₀ (sub_pos.mpr hk)).2
  nlinarith only [hn]

-- Scalar bridge from resolvent norm estimates to the Neumann condition
-- and the explicit bound printed in (173).
theorem schur_bound (a d c : ℝ) (ha : 0<a) (hd : 0<d)
    (hc : 0 ≤ c) (hgap : 2*c^2<a*d) :
    2*c^2/(a*d)<1 ∧
    (1/a)/(1-2*c^2/(a*d)) = d/(a*d-2*c^2) := by
  have had : 0<a*d := mul_pos ha hd
  have hh : a*d-2*c^2 ≠ 0 := ne_of_gt (sub_pos.mpr hgap)
  have hq : 2*c^2/(a*d)<1 := (div_lt_iff₀ had).2 (by simpa using hgap)
  refine ⟨hq,?_⟩
  field_simp [ne_of_gt ha,ne_of_gt hd, hh]
  <;> ring

-- Explicit bounded block inverse on the underlying Hilbert spaces.
-- ra and rd represent the inverses of the shifted diagonal realizations;
-- no total extension of the unbounded diagonal operators is needed.
theorem block_resolvent_of_factor {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (ra : E →L[ℂ] E) (rd : F →L[ℂ] F)
    (x : F →L[ℂ] E) (y : E →L[ℂ] F)
    (v : E →L[ℂ] E)
    (hleft : ∀ a, v (a-ra (x (rd (y a)))) = a)
    (hright : ∀ a, v a-ra (x (rd (y (v a)))) = a)
    (f : E) (g : F) :
    ∃! w : E × F,
      w.1 = ra (f-x w.2) ∧ w.2 = rd (g-y w.1) := by
  let a := v (ra (f-x (rd g)))
  let c := rd (g-y a)
  have he : a-ra (x (rd (y a))) = ra (f-x (rd g)) :=
    hright (ra (f-x (rd g)))
  have ha : a = ra (f-x c) := by
    calc
      a = (a-ra (x (rd (y a))))+ra (x (rd (y a))) := by abel
      _ = _ := by rw [he]; simp only [c, map_sub]; abel
  refine ⟨(a,c), ⟨ha,rfl⟩, ?_⟩
  rintro ⟨b,d⟩ ⟨hb,hd⟩
  change b = ra (f-x d) at hb
  change d = rd (g-y b) at hd
  rw [hd] at hb
  have hb' : b-ra (x (rd (y b))) = ra (f-x (rd g)) := by
    calc
      b-ra (x (rd (y b))) =
        ra (f-x (rd (g-y b)))-ra (x (rd (y b))) :=
          congrArg (fun u => u-ra (x (rd (y b)))) hb
      _ = _ := by simp only [map_sub]; abel
  have hab : b = a := by
    dsimp [a]
    rw [← hb', hleft]
  exact Prod.ext hab (by simpa only [hab] using hd)

-- The continuous linear maps that realize the Schur solution, as an
-- actual bounded map on the product, not merely pointwise solvability.
noncomputable def blockInverse {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (ra : E →L[ℂ] E) (rd : F →L[ℂ] F)
    (x : F →L[ℂ] E) (y : E →L[ℂ] F) (v : E →L[ℂ] E) :
    E × F →L[ℂ] E × F :=
  let p := ContinuousLinearMap.fst ℂ E F
  let q := ContinuousLinearMap.snd ℂ E F
  let a := v.comp (ra.comp (p-x.comp (rd.comp q)))
  a.prod (rd.comp (q-y.comp a))

theorem blockInverse_first {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (ra : E →L[ℂ] E) (rd : F →L[ℂ] F)
    (x : F →L[ℂ] E) (y : E →L[ℂ] F) (v : E →L[ℂ] E)
    (f : E) (g : F) :
    (blockInverse ra rd x y v (f,g)).1 = v (ra (f-x (rd g))) := by
  rfl

theorem blockInverse_second {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (ra : E →L[ℂ] E) (rd : F →L[ℂ] F)
    (x : F →L[ℂ] E) (y : E →L[ℂ] F) (v : E →L[ℂ] E)
    (f : E) (g : F) :
    (blockInverse ra rd x y v (f,g)).2 =
      rd (g-y (v (ra (f-x (rd g))))) := by
  rfl

-- The numerical hypothesis produces an invertible bounded Schur
-- factor on the actual pair of different Hilbert spaces.
theorem schur_factor_inverse {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] [Nontrivial E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (ra : E →L[ℂ] E) (rd : F →L[ℂ] F)
    (x : F →L[ℂ] E) (y : E →L[ℂ] F)
    (ha : ‖ra‖*‖x‖*‖rd‖*‖y‖ < 1) :
    ∃ v : E →L[ℂ] E,
      (∀ a, v (a-ra (x (rd (y a)))) = a) ∧
      (∀ a, v a-ra (x (rd (y (v a)))) = a) := by
  let k := ((ra.comp x).comp rd).comp y
  have hk : ‖k‖ < 1 := by
    apply lt_of_le_of_lt _ ha
    dsimp [k]
    calc
      _ ≤ ‖(ra.comp x).comp rd‖ * ‖y‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (‖ra.comp x‖*‖rd‖)*‖y‖ := by
        gcongr <;> exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (‖ra‖*‖x‖)*‖rd‖*‖y‖ := by
        gcongr <;> exact ContinuousLinearMap.opNorm_comp_le _ _
  obtain ⟨v, h1, h2, hn⟩ := neumann_inverse k hk
  refine ⟨v, ?_, ?_⟩
  · intro a
    have hh := congrArg (fun w : E →L[ℂ] E => w a) h2
    simpa [k] using hh
  · intro a
    have hh := congrArg (fun w : E →L[ℂ] E => w a) h1
    simpa [k] using hh

-- Full existence/uniqueness of the bounded block inverse when the
-- product of the four relevant operator norms is below one.
theorem block_resolvent_small_coupling {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] [Nontrivial E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (ra : E →L[ℂ] E) (rd : F →L[ℂ] F)
    (x : F →L[ℂ] E) (y : E →L[ℂ] F)
    (ha : ‖ra‖*‖x‖*‖rd‖*‖y‖ < 1) :
    ∃ inv : E × F →L[ℂ] E × F, ∀ f g, 
      (inv (f,g)).1 = ra (f-x (inv (f,g)).2) ∧
      (inv (f,g)).2 = rd (g-y (inv (f,g)).1) ∧
      ∀ w : E × F, (w.1 = ra (f-x w.2) ∧ w.2 = rd (g-y w.1)) →
        w = inv (f,g) := by
  obtain ⟨v, hleft, hright⟩ := schur_factor_inverse ra rd x y ha
  refine ⟨blockInverse ra rd x y v, ?_⟩
  intro f g
  let a := v (ra (f-x (rd g)))
  let c := rd (g-y a)
  have he : a-ra (x (rd (y a))) = ra (f-x (rd g)) :=
    hright (ra (f-x (rd g)))
  have ha' : a = ra (f-x c) := by
    calc
      a = (a-ra (x (rd (y a))))+ra (x (rd (y a))) := by abel
      _ = _ := by rw [he]; simp only [c, map_sub]; abel
  have hi : blockInverse ra rd x y v (f,g) = (a,c) := by
    exact Prod.ext (blockInverse_first ra rd x y v f g)
      (blockInverse_second ra rd x y v f g)
  rw [hi]
  refine ⟨ha',rfl,?_⟩
  intro w hw
  obtain ⟨u, hu, huniq⟩ := block_resolvent_of_factor ra rd x y v hleft hright f g
  exact (huniq w hw).trans (huniq (a,c) ⟨ha',rfl⟩).symm

#print axioms schur_factor_inverse
#print axioms block_resolvent_small_coupling
#print axioms block_resolvent_of_factor
#print axioms blockInverse_first
#print axioms blockInverse_second
#print axioms dense_transport
#print axioms core_closure_unique
#print axioms heat_limit_compact
#print axioms cutoff_compact
#print axioms smoothed_couplings_compact
#print axioms heat_tail
#print axioms physical_pairing
#print axioms weighted_block_graph
#print axioms neumann_inverse
#print axioms schur_bound
end M16KreinOperator
