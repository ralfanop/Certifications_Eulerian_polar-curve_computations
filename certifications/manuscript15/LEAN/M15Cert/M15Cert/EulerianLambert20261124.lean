import M15Cert.CarliniLaplace

/-!
# Manuscript 15, 24 November 2026: Eulerian–Lambert critical threshold

Source: Manuscript_15_20261124_EDITORIALE_EQUAZIONI_COMPLETE(1).zip
ZIP SHA256 e9dea5546bca52a3a88001c3e29c4caa7ac62325446a30c3b0fa54a2aa9d2acd
15.tex SHA256 e3b6632886cf881c46decf051f19169486229b4168fe97fb011398e38ee4b396

This independent module reuses the certified critical root uStar and constant
lambdaCL from M15Cert.CarliniLaplace. It establishes exact scalar identities
in Proposition "Eulerian–Lambert representation of the catenoidal threshold".
The general logarithmic derivative and uniqueness of the generalized Lambert
branch are separate proof obligations, not silently assumed here.
-/

namespace M15

open Filter

/-- The removable real Eulerian profile r_E(2 i u). -/
noncomputable def eulerianPhi (u : ℝ) : ℝ :=
  if u = 0 then 1 else Real.sinh u / u

/-- The restriction to the imaginary axis of the entire Eulerian kernel. -/
theorem eulerianPhi_eq_rEc (u : ℝ) :
    (eulerianPhi u : ℂ) = rEc (2 * Complex.I * u) := by
  exact (rEc_two_I_mul u).symm

/-- The true critical constant is the reciprocal of uStar times the
Eulerian profile, not an unverified numerical approximation. -/
theorem lambdaCL_eulerian_critical :
    lambdaCL = 1 / (uStar * eulerianPhi uStar) := by
  have hu : uStar ≠ 0 := uStar_pos.ne'
  have hs : Real.sinh uStar ≠ 0 := sinh_uStar_pos.ne'
  rw [lambdaCL_eq.1]
  simp only [eulerianPhi, hu, ↓reduceIte]
  field_simp

/-- Real Langevin function on the punctured positive axis. -/
noncomputable def langevinReal (u : ℝ) : ℝ :=
  Real.cosh u / Real.sinh u - 1 / u

/-- Critical Eulerian–Langevin identity of the new proposition. -/
theorem langevin_critical_identity :
    uStar * langevinReal uStar = lambdaCL ^ 2 := by
  have hu : uStar ≠ 0 := uStar_pos.ne'
  have hs : Real.sinh uStar ≠ 0 := sinh_uStar_pos.ne'
  have hpos : 0 ≤ uStar ^ 2 - 1 := by
    have hb := uStar_bounds.1
    nlinarith [sq_nonneg (uStar - 1)]
  have hsq : lambdaCL ^ 2 = uStar ^ 2 - 1 := by
    rw [lambdaCL_eq.2, Real.sq_sqrt hpos]
  rw [hsq]
  unfold langevinReal
  rw [cosh_uStar]
  field_simp

/-- The generalized Lambert relation at wStar = 2 * uStar. -/
theorem lambert_at_threshold :
    ((2 * uStar - 2) / (2 * uStar + 2)) * Real.exp (2 * uStar) = 1 := by
  have he : Real.exp uStar = Real.cosh uStar + Real.sinh uStar := by
    rw [Real.cosh_eq, Real.sinh_eq]
    ring
  have hn : Real.exp (-uStar) = Real.cosh uStar - Real.sinh uStar := by
    rw [Real.cosh_eq, Real.sinh_eq]
    ring
  have hsplit : (uStar - 1) * Real.exp uStar =
      (uStar + 1) * Real.exp (-uStar) := by
    rw [he, hn, cosh_uStar]
    ring
  have hm : Real.exp (-uStar) * Real.exp uStar = 1 := by
    rw [← Real.exp_add]
    simp
  have h2 : Real.exp (2 * uStar) = Real.exp uStar * Real.exp uStar := by
    rw [show 2 * uStar = uStar + uStar by ring, Real.exp_add]
  have hroot : (uStar - 1) * Real.exp (2 * uStar) = uStar + 1 := by
    calc
      (uStar - 1) * Real.exp (2 * uStar) =
          ((uStar - 1) * Real.exp uStar) * Real.exp uStar := by rw [h2]; ring
      _ = ((uStar + 1) * Real.exp (-uStar)) * Real.exp uStar := by rw [hsplit]
      _ = uStar + 1 := by rw [mul_assoc, hm, mul_one]
  have hden : (2 * uStar + 2 : ℝ) ≠ 0 := by linarith [uStar_pos]
  calc
    ((2 * uStar - 2) / (2 * uStar + 2)) * Real.exp (2 * uStar) =
        ((2 * uStar - 2) * Real.exp (2 * uStar)) / (2 * uStar + 2) := by ring
    _ = 1 := by
      apply (div_eq_iff hden).2
      nlinarith [hroot]

/-- The positive generalized Lambert parameter lies strictly above two. -/
theorem lambert_parameter_gt_two : (2 : ℝ) < 2 * uStar := by
  nlinarith [uStar_bounds.1]

/-- Reconstruction of lambdaCL from the generalized Lambert parameter. -/
theorem lambdaCL_from_lambert_parameter :
    lambdaCL = Real.sqrt ((2 * uStar) ^ 2 / 4 - 1) := by
  rw [lambdaCL_eq.2]
  congr 1
  ring


/-- Conversely, any real solution of the generalized Lambert equation
above two is the original Carlini–Laplace critical point. This uses
the already certified uniqueness of u*tanh u = 1, rather than making
an unjustified appeal to a named branch of Lambert W. -/
theorem lambert_branch_unique (w : ℝ) (hw : 2 < w)
    (hroot : ((w - 2) / (w + 2)) * Real.exp w = 1) :
    w = 2 * uStar := by
  have hd : w + 2 ≠ 0 := by linarith
  have hquot : ((w - 2) * Real.exp w) / (w + 2) = 1 := by
    calc
      ((w - 2) * Real.exp w) / (w + 2) =
          ((w - 2) / (w + 2)) * Real.exp w := by ring
      _ = 1 := hroot
  have hb : (w - 2) * Real.exp w = w + 2 := by
    have hh := (div_eq_iff hd).mp hquot
    nlinarith
  let u : ℝ := w / 2
  have hu : 0 < u := by dsimp [u]; linarith
  have hw' : w = 2 * u := by dsimp [u]; ring
  have hcrit : (u - 1) * Real.exp (2 * u) = u + 1 := by
    rw [← hw']
    dsimp [u]
    nlinarith [hb]
  have he : Real.exp (2 * u) = Real.exp u * Real.exp u := by
    rw [show 2 * u = u + u by ring, Real.exp_add]
  have hm : Real.exp (-u) * Real.exp u = 1 := by
    rw [← Real.exp_add]
    simp
  have heq : (u - 1) * (Real.exp u * Real.exp u) = u + 1 := by
    rw [← he]
    exact hcrit
  have hf0 : fCL u * Real.exp u = 0 := by
    unfold fCL
    rw [Real.sinh_eq, Real.cosh_eq]
    linear_combination (1 / 2) * heq - ((u + 1) / 2) * hm
  have hf : fCL u = 0 :=
    (mul_eq_zero.mp hf0).resolve_right (Real.exp_pos u).ne'
  have ht : u * Real.tanh u = 1 := (tanh_eq_iff u).2 hf
  have huniq : u = uStar := uStar_unique hu ht
  calc
    w = 2 * u := hw'
    _ = 2 * uStar := by rw [huniq]

/-- The generalized Lambert equation has exactly one real solution on
(2, infinity): w=2uStar. No analytic continuation or branch
identification is silently assumed. -/
theorem lambert_unique_above_two :
    ∃! w : ℝ, (2 : ℝ) < w ∧
      ((w - 2) / (w + 2)) * Real.exp w = 1 := by
  refine ⟨2 * uStar, ⟨lambert_parameter_gt_two, lambert_at_threshold⟩, ?_⟩
  intro w hw
  exact lambert_branch_unique w hw.1 hw.2


/-- On the punctured real axis, the Eulerian kernel
Φ(u)=sinh(u)/u has its ordinary quotient-rule derivative.
The proof first removes the artificial if-branch locally,
using eventual equality in a neighbourhood of u. -/
theorem eulerianPhi_hasDerivAt_of_ne_zero (u : ℝ) (hu : u ≠ 0) :
    HasDerivAt eulerianPhi
      ((Real.cosh u * u - Real.sinh u) / u ^ 2) u := by
  have hd := (Real.hasDerivAt_sinh u).div (hasDerivAt_id u) hu
  have heq :
      eulerianPhi =ᶠ[𝓝 u] (fun v : ℝ => Real.sinh v / v) := by
    filter_upwards [eventually_ne_nhds hu] with v hv
    simp [eulerianPhi, hv]
  simpa only [id_eq, mul_one] using hd.congr_of_eventuallyEq heq

/-- Eq. cl-eulerian-langevin: exact logarithmic derivative,
not only the special value at the critical root.
For u>0 it is coth(u)-1/u, the Langevin function. -/
theorem eulerianPhi_log_derivative (u : ℝ) (hu : 0 < u) :
    deriv (fun v : ℝ => Real.log (eulerianPhi v)) u =
      langevinReal u := by
  have hu0 : u ≠ 0 := hu.ne'
  have hs : Real.sinh u ≠ 0 := (Real.sinh_pos_iff.mpr hu).ne'
  have hp : eulerianPhi u ≠ 0 := by
    simp only [eulerianPhi, hu0, ↓reduceIte]
    exact div_ne_zero hs hu0
  have hbase := (Real.hasDerivAt_log hp).comp u
    (eulerianPhi_hasDerivAt_of_ne_zero u hu0)
  have hid :
      (eulerianPhi u)⁻¹ *
        ((Real.cosh u * u - Real.sinh u) / u ^ 2) =
          langevinReal u := by
    unfold langevinReal eulerianPhi
    simp only [hu0, ↓reduceIte]
    field_simp [hu0, hs]
  exact hbase.deriv.trans hid

#print axioms M15.eulerianPhi_hasDerivAt_of_ne_zero
#print axioms M15.eulerianPhi_log_derivative

#print axioms M15.lambert_branch_unique
#print axioms M15.lambert_unique_above_two

#print axioms M15.eulerianPhi_eq_rEc
#print axioms M15.lambdaCL_eulerian_critical
#print axioms M15.langevin_critical_identity
#print axioms M15.lambert_at_threshold
#print axioms M15.lambert_parameter_gt_two
#print axioms M15.lambdaCL_from_lambert_parameter

end M15
