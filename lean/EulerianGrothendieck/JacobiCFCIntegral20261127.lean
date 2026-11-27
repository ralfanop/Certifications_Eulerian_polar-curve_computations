import EulerianGrothendieck.JacobiFourier20261127
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Normed.Algebra.Spectrum

/-! The Bochner Fourier representation of Mathlib's actual normal
continuous functional calculus. Scalar Fourier inversion is a separate
classical analytic input, not an assumed operator inversion formula. -/
noncomputable section
open MeasureTheory NormedSpace
open scoped InnerProductSpace ENNReal
namespace M12JacobiCFCIntegral
open M12BilateralJacobi

abbrev Spec (u : Bonds) := spectrum ℂ (J u)

local instance (u : Bonds) : CompactSpace (Spec u) :=
  isCompact_iff_compactSpace.mp (spectrum.isCompact (𝕜 := ℂ) (J u))

def specId (u : Bonds) : C(Spec u, ℂ) :=
  (ContinuousMap.id ℂ).restrict (Spec u)

def hom (u : Bonds) : C(Spec u, ℂ) →⋆ₐ[ℂ] Op :=
  cfcHom (J_selfAdjoint u).isStarNormal

def homL (u : Bonds) : C(Spec u, ℂ) →L[ℂ] Op :=
  { toLinearMap := (hom u).toAlgHom.toLinearMap
    cont := cfcHom_continuous (J_selfAdjoint u).isStarNormal }

theorem homL_apply (u : Bonds) (g : C(Spec u, ℂ)) :
    homL u g = hom u g := rfl

theorem hom_id (u : Bonds) : hom u (specId u) = J u :=
  cfcHom_id (J_selfAdjoint u).isStarNormal

theorem spectrum_real (u : Bonds) (z : Spec u) : star (z:ℂ) = (z:ℂ) := by
  have he : star (specId u) = specId u := by
    apply cfcHom_injective (J_selfAdjoint u).isStarNormal
    change hom u (star (specId u)) = hom u (specId u)
    rw [map_star,hom_id,(J_selfAdjoint u).star_eq]
  exact congrArg (fun f : C(Spec u,ℂ) => f z) he

def evalL (u : Bonds) (z : Spec u) : C(Spec u,ℂ) →L[ℂ] ℂ :=
  (show C(Spec u,ℂ) →ₗ[ℂ] ℂ from (ContinuousMap.evalAlgHom ℂ ℂ z).toLinearMap).mkContinuous 1
    (fun (f : C(Spec u,ℂ)) => by
      change ‖f z‖ ≤ 1 * ‖f‖
      simpa only [one_mul] using ContinuousMap.norm_coe_le_norm f z)

theorem evalL_apply (u : Bonds) (z : Spec u) (g : C(Spec u,ℂ)) :
    evalL u z g = g z := rfl

def phase (u : Bonds) (t : ℝ) : C(Spec u,ℂ) :=
  exp (((t:ℂ)*Complex.I) • specId u)

theorem phase_apply (u : Bonds) (t : ℝ) (z : Spec u) :
    phase u t z = Complex.exp (((t:ℂ)*Complex.I)*(z:ℂ)) := by
  unfold phase
  change (ContinuousMap.evalAlgHom ℂ ℂ z).toRingHom (exp _) = _
  rw [NormedSpace.map_exp (ContinuousMap.evalAlgHom ℂ ℂ z).toRingHom (evalL u z).continuous]
  rw [← Complex.exp_eq_exp_ℂ]
  congr 1

theorem hom_phase (u : Bonds) (t : ℝ) :
    hom u (phase u t) = exp (((t:ℂ)*Complex.I) • J u) := by
  unfold phase
  change (hom u).toAlgHom.toRingHom (exp _) = _
  rw [NormedSpace.map_exp (hom u).toAlgHom.toRingHom (homL u).continuous]
  change exp (hom u (((t:ℂ)*Complex.I) • specId u)) = _
  rw [map_smul,hom_id]

theorem phase_continuous (u : Bonds) : Continuous (phase u) := by
  unfold phase
  have hc : Continuous (fun t : ℝ => ((t:ℂ)*Complex.I) • specId u) :=
    (Complex.continuous_ofReal.mul (continuous_const : Continuous (fun _ : ℝ => Complex.I))).smul continuous_const
  exact (M12ExpFrechet.exp_cont : Continuous (exp : C(Spec u,ℂ) → C(Spec u,ℂ))).comp hc

theorem phase_norm_le (u : Bonds) (t : ℝ) : ‖phase u t‖ ≤ 1 := by
  apply (ContinuousMap.norm_le _ zero_le_one).2
  intro z
  rw [phase_apply,Complex.norm_exp]
  have hz : (z:ℂ).im = 0 := by
    have h := congrArg Complex.im (spectrum_real u z)
    simp [Complex.star_def] at h
    linarith
  simp [Complex.mul_re,Complex.mul_im,hz]

theorem phase_integrable (u : Bonds) (w : ℝ → ℂ) (hw : Integrable w) :
    Integrable (fun t => w t • phase u t) := by
  have hm : AEStronglyMeasurable (fun t => w t • phase u t) volume :=
    hw.aestronglyMeasurable.smul (phase_continuous u).aestronglyMeasurable
  apply hw.norm.mono' hm
  filter_upwards [] with t
  rw [norm_smul]
  simpa using mul_le_mul_of_nonneg_left (phase_norm_le u t) (norm_nonneg (w t))

/-- Exact transport of the scalar Fourier inversion formula through the
actual CFC of J. Only the scalar inversion identity on the spectrum and
the integrability of the scalar Fourier density are hypotheses. -/
theorem cfc_fourier (u : Bonds) (w : ℝ → ℂ) (hw : Integrable w)
    (g : C(Spec u,ℂ))
    (hinv : ∀ z : Spec u, g z = ∫ t : ℝ, w t*Complex.exp (((t:ℂ)*Complex.I)*(z:ℂ))) :
    hom u g = ∫ t : ℝ, w t • exp (((t:ℂ)*Complex.I) • J u) := by
  have hi := phase_integrable u w hw
  have hg : g = ∫ t : ℝ, w t • phase u t := by
    ext z
    change g z = evalL u z (∫ t : ℝ, w t • phase u t)
    rw [← (evalL u z).integral_comp_comm hi,hinv z]
    apply integral_congr_ae
    filter_upwards [] with t
    rw [map_smul,evalL_apply,phase_apply,smul_eq_mul]
  rw [hg,← homL_apply]
  have hh := (homL u).integral_comp_comm hi
  rw [← hh]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [map_smul,homL_apply,hom_phase]

end M12JacobiCFCIntegral
#print axioms M12JacobiCFCIntegral.homL_apply
#print axioms M12JacobiCFCIntegral.hom_id
#print axioms M12JacobiCFCIntegral.spectrum_real
#print axioms M12JacobiCFCIntegral.evalL_apply
#print axioms M12JacobiCFCIntegral.phase_apply
#print axioms M12JacobiCFCIntegral.hom_phase
#print axioms M12JacobiCFCIntegral.phase_continuous
#print axioms M12JacobiCFCIntegral.phase_norm_le
#print axioms M12JacobiCFCIntegral.phase_integrable
#print axioms M12JacobiCFCIntegral.cfc_fourier
