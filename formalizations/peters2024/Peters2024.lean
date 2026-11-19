import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.Ball.Action
import Mathlib.Analysis.Normed.Group.BallSphere
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.SetTheory.Cardinal.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Audit of Peters, Alfano, Smith, Tozzi and Vergili, Filomat 38 (2024), 793–802.
The classical Borsuk–Ulam theorem is a named proposition, NOT an added axiom.
Every result depending on it carries an explicit hypothesis. -/

namespace Peters2024
open Set Metric
noncomputable section

abbrev Sphere (n : ℕ) := sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1
abbrev Coordinates (n : ℕ) := Fin n → ℝ

/-- Theorem 1.1, stated with the usual finite-dimensional Euclidean topology. -/
def BorsukUlam (n : ℕ) : Prop :=
  ∀ f : Sphere n → Coordinates n, Continuous f → ∃ p, f p = f (-p)

/-- A genuine theorem independent of Borsuk–Ulam. -/
theorem sphere_pathConnected (n : ℕ) (hn : 1 ≤ n) : PathConnectedSpace (Sphere n) := by
  apply isPathConnected_iff_pathConnectedSpace.mp
  apply isPathConnected_sphere _ _ (by norm_num)
  rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
  exact_mod_cast (show 1 < n+1 by omega)

/-- Theorem 1.4, reduced to the exact statement of 1.1 in dimension n.
The constant 1 handles empty cover members, whose infDist is otherwise zero. -/
theorem thm_1_4 (n : ℕ) (but : BorsukUlam n)
    (C : Fin (n+1) → Set (Sphere n)) (hc : ∀ i, IsClosed (C i))
    (cover : ∀ p, ∃ i, p ∈ C i) : ∃ i p, p ∈ C i ∧ -p ∈ C i := by
  classical
  let g (p : Sphere n) (i : Fin n) : ℝ :=
    if (C i.castSucc).Nonempty then infDist p (C i.castSucc) else 1
  have hg : Continuous g := by
    apply continuous_pi
    intro i
    by_cases h : (C i.castSucc).Nonempty
    · simpa [g, h] using continuous_infDist_pt (C i.castSucc)
    · simpa [g, h] using (continuous_const : Continuous (fun _ : Sphere n => (1 : ℝ)))
  have hz (p : Sphere n) (i : Fin n) : g p i = 0 ↔ p ∈ C i.castSucc := by
    by_cases h : (C i.castSucc).Nonempty
    · simpa [g, h] using ((hc i.castSucc).mem_iff_infDist_zero h (x := p)).symm
    · have h' : p ∉ C i.castSucc := fun hp => h ⟨p, hp⟩
      simp [g, h, h']
  obtain ⟨p, hp⟩ := but g hg
  by_cases ha : ∃ i : Fin n, p ∈ C i.castSucc
  · obtain ⟨i, hi⟩ := ha
    refine ⟨i.castSucc, p, hi, (hz (-p) i).mp ?_⟩
    rw [← congrFun hp i]
    exact (hz p i).mpr hi
  · have hb : ¬ ∃ i : Fin n, -p ∈ C i.castSucc := by
      rintro ⟨i, hi⟩
      apply ha
      refine ⟨i, (hz p i).mp ?_⟩
      rw [congrFun hp i]
      exact (hz (-p) i).mpr hi
    have last_mem (q : Sphere n) (h : ¬ ∃ i : Fin n, q ∈ C i.castSucc) :
        q ∈ C (Fin.last n) := by
      obtain ⟨i, hi⟩ := cover q
      rcases i.eq_castSucc_or_eq_last with ⟨j, rfl⟩ | rfl
      · exact False.elim (h ⟨j, hi⟩)
      · exact hi
    exact ⟨Fin.last n, p, last_mem p ha, last_mem (-p) hb⟩

section SampledPaths
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Samples of a continuous path on a countable subset of the unit interval.
This records the underlying witness, not a claim that arbitrary samples are continuous. -/
structure DiscreteArc (a b : X) where
  carrier : Set unitInterval
  countable : carrier.Countable
  zero_mem : 0 ∈ carrier
  one_mem : 1 ∈ carrier
  path : Path a b

def DiscreteArc.sample {a b : X} (d : DiscreteArc a b) (t : d.carrier) : X := d.path t

theorem sample_source {a b : X} (d : DiscreteArc a b) :
    d.sample ⟨0, d.zero_mem⟩ = a := d.path.source

theorem sample_target {a b : X} (d : DiscreteArc a b) :
    d.sample ⟨1, d.one_mem⟩ = b := d.path.target

def samplePath {a b : X} (γ : Path a b) (D : Set unitInterval)
    (hc : D.Countable) (h0 : 0 ∈ D) (h1 : 1 ∈ D) : DiscreteArc a b :=
  ⟨D, hc, h0, h1, γ⟩

/-- A finite sampling, valid also for a constant loop. No distinct-neighbour assumption. -/
def endpointSample {a b : X} (γ : Path a b) : DiscreteArc a b :=
  samplePath γ {0, 1} (by simp) (by simp) (by simp)

/-- Proposition 2.9 with the necessary path-connectedness hypothesis. -/
theorem prop_2_9 [PathConnectedSpace X] (a b : X) : Nonempty (DiscreteArc a b) :=
  ⟨endpointSample (PathConnectedSpace.somePath a b)⟩

/-- Any two samples can be joined, using a restricted part of the original path. -/
theorem samples_joined {a b : X} (d : DiscreteArc a b) (s t : d.carrier) :
    Joined (d.sample s) (d.sample t) := by
  change Joined (d.path s.val) (d.path t.val)
  by_cases h : s.val ≤ t.val
  · exact ⟨(d.path.truncateOfLE h).cast (d.path.extend_extends' s.val).symm
      (d.path.extend_extends' t.val).symm⟩
  · have h' : t.val ≤ s.val := le_of_lt (lt_of_not_ge h)
    exact ⟨((d.path.truncateOfLE h').cast (d.path.extend_extends' t.val).symm
      (d.path.extend_extends' s.val).symm).symm⟩

/-- Lemma 3.1: the sampled path has traversable connecting subpaths. -/
theorem lemma_3_1 {a b : X} (γ : Path a b) (D : Set unitInterval)
    (hc : D.Countable) (h0 : 0 ∈ D) (h1 : 1 ∈ D) :
    ∃ d : DiscreteArc a b, d.carrier = D ∧ d.path = γ ∧
      ∀ s t : d.carrier, Joined (d.sample s) (d.sample t) := by
  exact ⟨samplePath γ D hc h0 h1, rfl, rfl, samples_joined _⟩

/-- Theorem 3.2: traverse a path and its reverse. -/
def halfTime : unitInterval := ⟨1/2, by constructor <;> norm_num⟩

def thm_3_2 {a b : X} (d : DiscreteArc a b) : DiscreteArc a a :=
  samplePath (d.path.trans d.path.symm) {0, halfTime, 1} (by simp) (by simp) (by simp)

theorem loop_visits_turning_point {a b : X} (d : DiscreteArc a b) :
    (thm_3_2 d).sample ⟨halfTime, by simp [thm_3_2, samplePath]⟩ = b := by
  change (d.path.trans d.path.symm) halfTime = b
  rw [Path.trans_apply, dif_pos (by norm_num [halfTime])]
  have he : (⟨2 * (halfTime : ℝ), by constructor <;> norm_num [halfTime]⟩ : unitInterval) = 1 := by
    ext
    norm_num [halfTime]
  rw [he, d.path.target]

/-- Map the entire underlying path and preserve every sampling parameter. -/
def DiscreteArc.map {a b : X} (d : DiscreteArc a b) {f : X → Y} (hf : Continuous f) :
    DiscreteArc (f a) (f b) :=
  ⟨d.carrier, d.countable, d.zero_mem, d.one_mem, d.path.map hf⟩

theorem sample_map {a b : X} (d : DiscreteArc a b) {f : X → Y} (hf : Continuous f)
    (t : d.carrier) : (d.map hf).sample t = f (d.sample t) := rfl

/-- Theorem 3.8, with an explicit common image value. -/
theorem thm_3_8 [PathConnectedSpace X] (f : X → Y) (hf : Continuous f)
    (a b : X) (he : f a = f b) :
    ∃ d : DiscreteArc a b, ∃ k : DiscreteArc (f a) (f a),
      ∀ t : unitInterval, k.path t = f (d.path t) := by
  let d := endpointSample (PathConnectedSpace.somePath a b)
  let k := d.map hf
  exact ⟨d, ⟨k.carrier, k.countable, k.zero_mem, k.one_mem,
    k.path.cast rfl he⟩, fun _ => rfl⟩

/-- Lemma 4.5 under a precise continuous trajectory interpretation of Defs 4.2, 4.4. -/
theorem lemma_4_5 {a b : X} (γ : Path a b) : Nonempty (DiscreteArc a b) :=
  ⟨endpointSample γ⟩

/-- The entire continuous trajectory is path-connected, not merely its endpoints. -/
theorem trajectory_trace_pathConnected {a b : X} (γ : Path a b) :
    IsPathConnected (range γ) := by
  letI : PathConnectedSpace unitInterval := isPathConnected_iff_pathConnectedSpace.mp
    ((convex_Icc (𝕜 := ℝ) (0 : ℝ) 1).isPathConnected ⟨0, by norm_num⟩)
  exact isPathConnected_range γ.continuous

/-- Lemma 4.8, with continuity recorded as part of the trajectory definition. -/
theorem lemma_4_8 {a b : X} (γ : Path a b) : Continuous γ := γ.continuous

/-- Lemma 5.2 as the literal projection in Definition 5.1. -/
theorem lemma_5_2 : Continuous (Prod.snd : X × Y → Y) := continuous_snd

/-- Projection of a genuinely continuous trajectory is continuous. -/
theorem trajectory_projection {Z : Type*} [TopologicalSpace Z]
    (h : Z → X × Y) (hh : Continuous h) : Continuous (Prod.snd ∘ h) :=
  continuous_snd.comp hh

end SampledPaths

/-- Theorem 3.3: position vectors sampled from the embedded sphere.
This is not a tangent vector field; the base position has nonzero radial component. -/
def thm_3_3 (n : ℕ) {a b : Sphere n} (d : DiscreteArc a b) :
    d.carrier → EuclideanSpace ℝ (Fin (n+1)) := fun t => (d.sample t).val

theorem position_norm (n : ℕ) {a b : Sphere n} (d : DiscreteArc a b) (t : d.carrier) :
    ‖thm_3_3 n d t‖ = 1 := by
  simpa only [sub_zero] using mem_sphere_iff_norm.mp (d.sample t).property

theorem position_not_orthogonal (n : ℕ) {a b : Sphere n} (d : DiscreteArc a b)
    (t : d.carrier) : @inner ℝ _ _ (thm_3_3 n d t) (thm_3_3 n d t) ≠ 0 := by
  rw [real_inner_self_eq_norm_sq, position_norm]
  norm_num

/-- Lemma 3.4, without a Borsuk–Ulam assumption. -/
theorem lemma_3_4 (n : ℕ) (hn : 1 ≤ n) (p : Sphere n) :
    Nonempty (DiscreteArc p (-p)) := by
  letI := sphere_pathConnected n hn
  exact prop_2_9 p (-p)

/-- Theorem 3.5: the image of a sampled antipodal path is a loop.
The only unresolved classical dependency is explicitly provided as `but`. -/
theorem thm_3_5 (n : ℕ) (hn : 1 ≤ n) (but : BorsukUlam n)
    (f : Sphere n → Coordinates n) (hf : Continuous f) :
    ∃ p : Sphere n, f p = f (-p) ∧
      ∃ d : DiscreteArc p (-p), ∃ k : DiscreteArc (f p) (f p),
        ∀ t : unitInterval, k.path t = f (d.path t) := by
  letI := sphere_pathConnected n hn
  obtain ⟨p, hp⟩ := but f hf
  exact ⟨p, hp, thm_3_8 f hf p (-p) hp⟩

/-- Theorems 5.4, 5.5 and 6.2, when the observable really is continuous. -/
theorem thm_5_4 (but : BorsukUlam 2) (α : Sphere 2 → Coordinates 2)
    (hα : Continuous α) : ∃ p, α p = α (-p) := but α hα

theorem thm_5_5 (but : BorsukUlam 2) (H : Sphere 2 → Coordinates 2)
    (hH : Continuous H) : ∃ p, H p = H (-p) := but H hH

/-- Conditional repair of 5.6: if a fixed-endpoint kernel is a continuous map
on S², Borsuk–Ulam supplies antipodal inputs of equal value. A path through
any prescribed intermediate point exists independently of that equality. -/
theorem thm_5_6_continuous_kernel (but : BorsukUlam 2)
    (K : Sphere 2 → Sphere 2 → Coordinates 2) (b : Sphere 2)
    (hK : Continuous (K b)) : ∃ a : Sphere 2,
      K b a = K b (-a) ∧ Nonempty (Path a b) ∧ Nonempty (Path b (-a)) := by
  letI := sphere_pathConnected 2 (by decide)
  obtain ⟨a, ha⟩ := but (K b) hK
  exact ⟨a, ha, PathConnectedSpace.joined a b, PathConnectedSpace.joined b (-a)⟩

theorem thm_6_2 (but : BorsukUlam 2) (Φ : Sphere 2 → Coordinates 2)
    (hΦ : Continuous Φ) : ∃ p, Φ p = Φ (-p) := but Φ hΦ

/-- Corollary 6.3, at the required dimension. -/
theorem cor_6_3 (but : BorsukUlam 2) (Φ : Sphere 2 → Coordinates 2)
    (hΦ : Continuous Φ) : ∃ p : Sphere 2, Φ p = Φ (-p) ∧
      ∃ d : DiscreteArc p (-p), ∃ k : DiscreteArc (Φ p) (Φ p),
        ∀ t : unitInterval, k.path t = Φ (d.path t) := thm_3_5 2 (by decide) but Φ hΦ

/-- An arbitrary normalized cumulative two-coordinate observable need not admit
an equal-value split, even for a smooth map. Coordinate functions t and t^2
arise from integrating 1 and 2t. This refutes the general bisection inference,
not a separately specified Woodhouse integral with extra restrictions. -/
theorem complex_bisection_counterexample :
    ¬ ∃ t : ℝ, (t, t^2) = (1-t, 1-t^2) := by
  rintro ⟨t, ht⟩
  have h1 := congrArg Prod.fst ht
  have h2 := congrArg Prod.snd ht
  change t = 1-t at h1
  change t^2 = 1-t^2 at h2
  have h : t = 1/2 := by linarith
  rw [h] at h2
  norm_num at h2

/-- Equal spatial lengths do not entail equal free-particle actions (§5.6). -/
theorem equal_length_unequal_action :
    (1 : ℝ)^2 / (2*1) ≠ 1^2 / (2*2) := by norm_num

/-- On the unit-circle contour from 1 to i with integrand f(z)=z in
f(z) dz/z, equality of the two subarc integrals would force the splitting
point to be the chord midpoint, which is not on the circle. -/
theorem unit_circle_contour_no_equal_split :
    ¬ ∃ x y : ℝ, x^2 + y^2 = 1 ∧ (x-1, y) = (-x, 1-y) := by
  rintro ⟨x, y, hs, he⟩
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  change x-1 = -x at hx
  change y = 1-y at hy
  have hx' : x = 1/2 := by linarith
  have hy' : y = 1/2 := by linarith
  rw [hx', hy'] at hs
  norm_num at hs

/-- The continuity hypothesis in the printed 5.4 cannot be omitted.
A well-order selects exactly one representative from each antipodal pair. -/
theorem arbitrary_map_counterexample :
    ∃ f : Sphere 2 → Coordinates 2, ∀ p, f p ≠ f (-p) := by
  classical
  let f (p : Sphere 2) (_ : Fin 2) : ℝ := if WellOrderingRel p (-p) then 0 else 1
  refine ⟨f, ?_⟩
  intro p hp
  have h0 := congrFun hp (0 : Fin 2)
  rcases trichotomous_of WellOrderingRel p (-p) with h | h | h
  · have hn := asymm_of WellOrderingRel h
    simp [f, h, hn] at h0
  · exact ne_neg_of_mem_unit_sphere ℝ p h
  · have hn := asymm_of WellOrderingRel h
    simp [f, h, hn] at h0

/-- A valid scalar repair of the bisection assertion in §§5.6 and 6.5.
For a real-valued additive integral with a continuous cumulative function,
one can split its value in half; monotonicity is not required. -/
theorem real_bisection (F : ℝ → ℝ) (hF : Continuous F) (h0 : F 0 = 0) :
    ∃ t ∈ Icc (0 : ℝ) 1, F t = F 1 - F t := by
  have h : F 1 / 2 ∈ uIcc (F 0) (F 1) := by
    rw [h0]
    rcases le_total 0 (F 1) with h | h
    · rw [uIcc_of_le h]
      exact ⟨by linarith, by linarith⟩
    · rw [uIcc_of_ge h]
      exact ⟨by linarith, by linarith⟩
  obtain ⟨t, ht, he⟩ := intermediate_value_uIcc hF.continuousOn h
  rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
  exact ⟨t, ht, by linarith⟩

/-- Counterexample to inferring continuity solely from the dense time domain. -/
theorem density_does_not_imply_continuity :
    ∃ f : ℝ → ℝ, ¬ ContinuousOn f (Icc (0 : ℝ) 1) := by
  let f : ℝ → ℝ := fun t => if t = 0 then 0 else 1
  refine ⟨f, fun hf => ?_⟩
  have hmid : (1/2 : ℝ) ∈ Icc (f 0) (f 1) := by norm_num [f]
  obtain ⟨t, _, ht⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hf hmid
  by_cases h : t = 0 <;> norm_num [f, h] at ht

end

end Peters2024

#print axioms Peters2024.thm_1_4
#print axioms Peters2024.prop_2_9
#print axioms Peters2024.lemma_3_1
#print axioms Peters2024.thm_3_2
#print axioms Peters2024.loop_visits_turning_point
#print axioms Peters2024.thm_3_3
#print axioms Peters2024.position_not_orthogonal
#print axioms Peters2024.lemma_3_4
#print axioms Peters2024.thm_3_5
#print axioms Peters2024.thm_3_8
#print axioms Peters2024.lemma_4_5
#print axioms Peters2024.trajectory_trace_pathConnected
#print axioms Peters2024.lemma_4_8
#print axioms Peters2024.lemma_5_2
#print axioms Peters2024.thm_5_4
#print axioms Peters2024.thm_5_5
#print axioms Peters2024.thm_5_6_continuous_kernel
#print axioms Peters2024.thm_6_2
#print axioms Peters2024.cor_6_3
#print axioms Peters2024.complex_bisection_counterexample
#print axioms Peters2024.unit_circle_contour_no_equal_split
#print axioms Peters2024.arbitrary_map_counterexample
#print axioms Peters2024.real_bisection
#print axioms Peters2024.density_does_not_imply_continuity
#print axioms Peters2024.equal_length_unequal_action
#print axioms Peters2024.position_norm
#print axioms Peters2024.sample_map
#print axioms Peters2024.sample_source
#print axioms Peters2024.sample_target
#print axioms Peters2024.samples_joined
#print axioms Peters2024.sphere_pathConnected
#print axioms Peters2024.trajectory_projection
