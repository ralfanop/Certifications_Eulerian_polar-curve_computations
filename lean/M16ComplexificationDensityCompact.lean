import M16IntrinsicBridge

/-!
# M16 §9.5: dense graph domains and compact operators on the genuine complexification

This module uses the Hilbert norm constructed in #713, not the max norm
on a product. It proves density and compactness without assuming a
geometric eigenbasis or a compact geometric inverse.
-/

open Filter Topology Set
open M16ComplexHilbert.Complexification
open M16IntrinsicBridge

namespace M16ComplexificationDensityCompact

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem continuous_real_part :
    Continuous (fun u : Complexification E => u.1) :=
  (LipschitzWith.of_dist_le_mul (K := 1) (fun u v : Complexification E => by
    simp only [dist_eq_norm, NNReal.coe_one, one_mul]
    exact norm_fst_le (u - v))).continuous

theorem continuous_imag_part :
    Continuous (fun u : Complexification E => u.2) :=
  (LipschitzWith.of_dist_le_mul (K := 1) (fun u v : Complexification E => by
    simp only [dist_eq_norm, NNReal.coe_one, one_mul]
    exact norm_snd_le (u - v))).continuous

theorem continuous_pair :
    Continuous (fun p : E × E => mk p.1 p.2) := by
  have h : (fun p : E × E => mk p.1 p.2) =
      (fun p : E × E => ofReal p.1 + Complex.I • ofReal p.2) := by
    funext p
    apply Prod.ext <;> simp [Complex.I_re, Complex.I_im]
  rw [h]
  have hc : Continuous (ofReal : E → Complexification E) :=
    (ofRealLi : E →ₗᵢ[ℝ] Complexification E).continuous
  exact (hc.comp continuous_fst).add (continuous_const.smul (hc.comp continuous_snd))

/-- A dense real domain yields a dense domain in the actual complex Hilbert norm. -/
theorem dense_complex_domain (s : Set E) (hs : Dense s) :
    Dense {u : Complexification E | u.1 ∈ s ∧ u.2 ∈ s} := by
  intro z
  have hm : (z.1, z.2) ∈ closure (s ×ˢ s) := (hs.prod hs) (z.1, z.2)
  have hi : z ∈ (fun p : E × E => mk p.1 p.2) '' closure (s ×ˢ s) :=
    ⟨(z.1,z.2), hm, rfl⟩
  have hc := image_closure_subset_closure_image
    (continuous_pair (E := E)) hi
  apply closure_mono ?_ hc
  rintro _ ⟨p, hp, rfl⟩
  exact hp

/-- Domain of the complexified graph: both real components must be in the original domain. -/
theorem graph_domain_eq (G : Set (E × E)) :
    {u : Complexification E | ∃ v, (u,v) ∈ hilbertGraph G} =
    {u : Complexification E | (∃ a, (u.1,a) ∈ G) ∧ (∃ b, (u.2,b) ∈ G)} := by
  ext u
  change (∃ v : Complexification E, (u.1,v.1) ∈ G ∧ (u.2,v.2) ∈ G) ↔
    (∃ a : E, (u.1,a) ∈ G) ∧ (∃ b : E, (u.2,b) ∈ G)
  constructor
  · rintro ⟨v, ha, hb⟩
    exact ⟨⟨v.1,ha⟩,⟨v.2,hb⟩⟩
  · rintro ⟨⟨a,ha⟩,⟨b,hb⟩⟩
    exact ⟨mk a b,ha,hb⟩

theorem dense_hilbertGraph_domain (G : Set (E × E))
    (hG : Dense {x : E | ∃ y, (x,y) ∈ G}) :
    Dense {u : Complexification E | ∃ v, (u,v) ∈ hilbertGraph G} := by
  rw [graph_domain_eq]
  exact dense_complex_domain _ hG

/-- Compactness is preserved by complexification: the product of two compact
image bounds is compact and its image in the complex Hilbert norm is compact. -/
theorem compact_complexify (S : E →L[ℝ] F)
    (hS : IsCompactOperator (S : E → F)) :
    IsCompactOperator (complexify S : Complexification E → Complexification F) := by
  obtain ⟨V,hV,K,hK,hVK⟩ :=
    (isCompactOperator_iff_exists_mem_nhds_image_subset_compact (S : E → F)).mp hS
  apply (isCompactOperator_iff_exists_mem_nhds_image_subset_compact
    (complexify S : Complexification E → Complexification F)).mpr
  let U : Set (Complexification E) :=
    (fun u : Complexification E => u.1) ⁻¹' V ∩
    (fun u : Complexification E => u.2) ⁻¹' V
  have h1 : Tendsto (fun u : Complexification E => u.1)
      (𝓝 (0 : Complexification E)) (𝓝 (0 : E)) := by
    simpa only [zero_fst] using
      (continuous_real_part (E := E)).continuousAt (x := (0 : Complexification E))
  have h2 : Tendsto (fun u : Complexification E => u.2)
      (𝓝 (0 : Complexification E)) (𝓝 (0 : E)) := by
    simpa only [zero_snd] using
      (continuous_imag_part (E := E)).continuousAt (x := (0 : Complexification E))
  have hU : U ∈ 𝓝 (0 : Complexification E) :=
    Filter.inter_mem (h1 hV) (h2 hV)
  refine ⟨U,hU,(fun p : F × F => mk p.1 p.2) '' (K ×ˢ K),
    (hK.prod hK).image (continuous_pair (E := F)), ?_⟩
  rintro _ ⟨u,hu,rfl⟩
  change u.1 ∈ V ∧ u.2 ∈ V at hu
  refine ⟨(S u.1,S u.2), ?_, rfl⟩
  exact ⟨hVK ⟨u.1,hu.1,rfl⟩,hVK ⟨u.2,hu.2,rfl⟩⟩

/-- Conversely, the real operator is compact by restriction to the isometric
real subspace and projection onto the real component of the compact image. -/
theorem compact_of_complexify (S : E →L[ℝ] F)
    (hS : IsCompactOperator (complexify S : Complexification E → Complexification F)) :
    IsCompactOperator (S : E → F) := by
  obtain ⟨V,hV,K,hK,hVK⟩ :=
    (isCompactOperator_iff_exists_mem_nhds_image_subset_compact
      (complexify S : Complexification E → Complexification F)).mp hS
  apply (isCompactOperator_iff_exists_mem_nhds_image_subset_compact (S : E → F)).mpr
  have hc : Continuous (ofReal : E → Complexification E) :=
    (ofRealLi : E →ₗᵢ[ℝ] Complexification E).continuous
  have ht : Tendsto (ofReal : E → Complexification E) (𝓝 (0 : E))
      (𝓝 (0 : Complexification E)) := by
    have hz : ofReal (0 : E) = 0 := rfl
    simpa only [hz] using hc.continuousAt (x := (0 : E))
  refine ⟨ofReal ⁻¹' V, ht hV, (fun u : Complexification F => u.1) '' K,
    hK.image (continuous_real_part (E := F)), ?_⟩
  rintro _ ⟨x,hx,rfl⟩
  refine ⟨complexify S (ofReal x), hVK ⟨ofReal x,hx,rfl⟩, ?_⟩
  simp

theorem compact_complexify_iff (S : E →L[ℝ] F) :
    IsCompactOperator (complexify S : Complexification E → Complexification F) ↔
    IsCompactOperator (S : E → F) :=
  ⟨compact_of_complexify S,compact_complexify S⟩

end

end M16ComplexificationDensityCompact

#print axioms M16ComplexificationDensityCompact.continuous_real_part
#print axioms M16ComplexificationDensityCompact.continuous_imag_part
#print axioms M16ComplexificationDensityCompact.continuous_pair
#print axioms M16ComplexificationDensityCompact.dense_complex_domain
#print axioms M16ComplexificationDensityCompact.graph_domain_eq
#print axioms M16ComplexificationDensityCompact.dense_hilbertGraph_domain
#print axioms M16ComplexificationDensityCompact.compact_complexify
#print axioms M16ComplexificationDensityCompact.compact_of_complexify
#print axioms M16ComplexificationDensityCompact.compact_complexify_iff
