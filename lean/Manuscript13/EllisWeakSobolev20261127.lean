import Mathlib
import Manuscript13.EllisSobolevDomain20261127

open MeasureTheory Set Filter SchwartzMap FourierTransform
open scoped FourierTransform LineDeriv ContDiff
namespace Manuscript13.EllisWeakSobolev20261127
noncomputable section
open Manuscript13.EllisComplexResolvent20261127
open Manuscript13.EllisSobolevDomain20261127

abbrev TD := TemperedDistribution ℝ ℂ
def embed (u : H) : TD := Lp.toTemperedDistribution u
def weakD (u : TD) : TD := ∂_{(1 : ℝ)} u

/-- Weak derivatives defined in distributions (Schwartz tests); not a Fourier definition. -/
def weakH2 (u : H) : Prop :=
  ∃ v w : H, weakD (embed u) = embed v ∧ weakD (embed v) = embed w

def dSymbol (x : ℝ) : ℂ := (2 * (Real.pi : ℂ) * Complex.I) * (x : ℂ)
def dSquare (x : ℝ) : ℂ := dSymbol x * dSymbol x

theorem dSquare_eq (x : ℝ) : dSquare x = -(frequencySquare x : ℂ) := by
  unfold dSquare dSymbol frequencySquare
  push_cast
  ring_nf
  simp [Complex.I_sq]
  <;> ring

theorem dSymbol_growth : dSymbol.HasTemperateGrowth := by unfold dSymbol; fun_prop
theorem dSquare_growth : dSquare.HasTemperateGrowth := by
  unfold dSquare
  exact dSymbol_growth.mul dSymbol_growth

theorem fourier_embed (u : H) : 𝓕 (embed u) = embed (EllisComplexResolvent20261127.fourier u) :=
  Lp.fourier_toTemperedDistribution_eq u

theorem fourier_weakD (u : TD) :
    𝓕 (weakD u) = TemperedDistribution.smulLeftCLM ℂ dSymbol (𝓕 u) := by
  unfold weakD
  rw [TemperedDistribution.fourier_lineDerivOp_eq]
  have h : (fun x : ℝ => ((inner ℝ x (1:ℝ) : ℝ) : ℂ)).HasTemperateGrowth := by fun_prop
  rw [← ContinuousLinearMap.smul_apply, ← TemperedDistribution.smulLeftCLM_smul h]
  congr 2
  funext x
  simp [dSymbol, Real.inner_apply, mul_assoc]

theorem fourier_weakD_twice (u : TD) :
    𝓕 (weakD (weakD u)) = TemperedDistribution.smulLeftCLM ℂ dSquare (𝓕 u) := by
  rw [fourier_weakD, fourier_weakD,
    TemperedDistribution.smulLeftCLM_smulLeftCLM_apply dSymbol_growth dSymbol_growth]
  rfl

/-- Unbounded temperate multiplication, identified against compactly supported smooth tests. -/
theorem distribution_mul_ae (g : ℝ → ℂ) (hg : g.HasTemperateGrowth) (hc : Continuous g)
    (u v : H) (h : TemperedDistribution.smulLeftCLM ℂ g (embed u) = embed v) :
    (fun x => g x * u x) =ᵐ[volume] (fun x => v x) := by
  have hu : LocallyIntegrable (fun x : ℝ => u x) volume := (Lp.memLp u).locallyIntegrable (by norm_num)
  have hv : LocallyIntegrable (fun x : ℝ => v x) volume := (Lp.memLp v).locallyIntegrable (by norm_num)
  apply ae_eq_of_integral_contDiff_smul_eq (LocallyIntegrable.continuous_mul hc hu) hv
  intro t ht hs
  have hs' : HasCompactSupport (Complex.ofRealCLM ∘ t) := hs.comp_left rfl
  have ht' : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ t) := by fun_prop
  let φ := hs'.toSchwartzMap ht'
  have he := congrArg (fun z : TD => z φ) h
  simp only [TemperedDistribution.smulLeftCLM_apply_apply, embed, Lp.toTemperedDistribution_apply] at he
  convert he using 1 <;> apply integral_congr_ae <;> filter_upwards [] with x
  · rw [SchwartzMap.smulLeftCLM_apply_apply hg]
    change (t x : ℂ) * (g x * u x) = (g x * (t x : ℂ)) * u x
    ring
  · rfl

theorem distribution_mul_of_ae (g : ℝ → ℂ) (hg : g.HasTemperateGrowth) (u v : H)
    (h : (fun x => g x * u x) =ᵐ[volume] (fun x => v x)) :
    TemperedDistribution.smulLeftCLM ℂ g (embed u) = embed v := by
  ext φ
  simp only [TemperedDistribution.smulLeftCLM_apply_apply, embed, Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [h] with x hx
  rw [SchwartzMap.smulLeftCLM_apply_apply hg, ← hx]
  change (g x * φ x) * u x = φ x * (g x * u x)
  ring

theorem first_mem_of_bessel (u : H) (h : besselH2 u) :
    MemLp (fun x => dSymbol x * EllisComplexResolvent20261127.fourier u x) 2 volume := by
  unfold besselH2 at h
  apply h.of_le
  · exact (dSymbol_growth.1.continuous.aestronglyMeasurable).mul (Lp.memLp (EllisComplexResolvent20261127.fourier u)).aestronglyMeasurable
  · filter_upwards [] with x
    rw [norm_mul, norm_mul]
    have hb : ‖dSymbol x‖ ≤ 1 + frequencySquare x := by
      have he : ‖dSymbol x‖ = |2 * Real.pi * x| := by
        unfold dSymbol
        simp [norm_mul, Real.norm_eq_abs, abs_mul, abs_of_nonneg Real.pi_pos.le]
        <;> ring
      rw [he]
      unfold frequencySquare
      nlinarith [sq_abs (2 * Real.pi * x), sq_nonneg (|2 * Real.pi * x| - 1)]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by unfold frequencySquare; positivity)]
    exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)

theorem second_mem_of_bessel (u : H) (h : besselH2 u) :
    MemLp (fun x => dSquare x * EllisComplexResolvent20261127.fourier u x) 2 volume := by
  have h' := (secondFrequency_iff_bessel u).2 h
  have hm : MemLp (fun x => -((frequencySquare x : ℂ) * EllisComplexResolvent20261127.fourier u x)) 2 volume := h'.neg
  refine MemLp.ae_eq ?_ hm
  filter_upwards [] with x
  simp [dSquare_eq]

theorem weakH2_iff_bessel (u : H) : weakH2 u ↔ besselH2 u := by
  constructor
  · rintro ⟨v,w,hv,hw⟩
    have hD : weakD (weakD (embed u)) = embed w := by rw [hv,hw]
    have he := congrArg (fun z : TD => 𝓕 z) hD
    rw [fourier_weakD_twice, fourier_embed, fourier_embed] at he
    have hae := distribution_mul_ae dSquare dSquare_growth
      (by unfold dSquare dSymbol; fun_prop) (EllisComplexResolvent20261127.fourier u) (EllisComplexResolvent20261127.fourier w) he
    have hm : MemLp (fun x => dSquare x * EllisComplexResolvent20261127.fourier u x) 2 volume :=
      MemLp.ae_eq hae.symm (Lp.memLp (EllisComplexResolvent20261127.fourier w))
    apply (secondFrequency_iff_bessel u).1
    have hn := hm.neg
    refine MemLp.ae_eq ?_ hn
    filter_upwards [] with x
    simp [dSquare_eq]
  · intro h
    let vF := (first_mem_of_bessel u h).toLp _
    let wF := (second_mem_of_bessel u h).toLp _
    let v := EllisComplexResolvent20261127.fourier.symm vF
    let w := EllisComplexResolvent20261127.fourier.symm wF
    have hvF : EllisComplexResolvent20261127.fourier v = vF := EllisComplexResolvent20261127.fourier.apply_symm_apply _
    have hwF : EllisComplexResolvent20261127.fourier w = wF := EllisComplexResolvent20261127.fourier.apply_symm_apply _
    have h1 : weakD (embed u) = embed v := by
      apply (fourierEquiv ℂ TD).injective
      change 𝓕 (weakD (embed u)) = 𝓕 (embed v)
      rw [fourier_weakD, fourier_embed, fourier_embed, hvF]
      exact distribution_mul_of_ae dSymbol dSymbol_growth _ _ (first_mem_of_bessel u h).coeFn_toLp.symm
    have h2 : weakD (weakD (embed u)) = embed w := by
      apply (fourierEquiv ℂ TD).injective
      change 𝓕 (weakD (weakD (embed u))) = 𝓕 (embed w)
      rw [fourier_weakD_twice, fourier_embed, fourier_embed, hwF]
      exact distribution_mul_of_ae dSquare dSquare_growth _ _ (second_mem_of_bessel u h).coeFn_toLp.symm
    exact ⟨v,w,h1,by simpa only [h1] using h2⟩

theorem graph_iff_weakH2 (κ : ℝ) (u : H) :
    (∃ f : H, shiftedGraph κ u f) ↔ weakH2 u :=
  (graph_iff_besselH2 κ u).trans (weakH2_iff_bessel u).symm

end
end Manuscript13.EllisWeakSobolev20261127
#print axioms Manuscript13.EllisWeakSobolev20261127.embed
#print axioms Manuscript13.EllisWeakSobolev20261127.weakD
#print axioms Manuscript13.EllisWeakSobolev20261127.weakH2
#print axioms Manuscript13.EllisWeakSobolev20261127.dSymbol
#print axioms Manuscript13.EllisWeakSobolev20261127.dSquare
#print axioms Manuscript13.EllisWeakSobolev20261127.dSquare_eq
#print axioms Manuscript13.EllisWeakSobolev20261127.dSymbol_growth
#print axioms Manuscript13.EllisWeakSobolev20261127.dSquare_growth
#print axioms Manuscript13.EllisWeakSobolev20261127.fourier_embed
#print axioms Manuscript13.EllisWeakSobolev20261127.fourier_weakD
#print axioms Manuscript13.EllisWeakSobolev20261127.fourier_weakD_twice
#print axioms Manuscript13.EllisWeakSobolev20261127.distribution_mul_ae
#print axioms Manuscript13.EllisWeakSobolev20261127.distribution_mul_of_ae
#print axioms Manuscript13.EllisWeakSobolev20261127.first_mem_of_bessel
#print axioms Manuscript13.EllisWeakSobolev20261127.second_mem_of_bessel
#print axioms Manuscript13.EllisWeakSobolev20261127.weakH2_iff_bessel
#print axioms Manuscript13.EllisWeakSobolev20261127.graph_iff_weakH2
