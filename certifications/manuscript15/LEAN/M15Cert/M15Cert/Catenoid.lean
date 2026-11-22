/-
Manuscript 15, Section 7.11, Proposition 7.25 -- Eulerian reconstruction of the catenoid.

* (287)  R_a(u) := a - Y(iu) = a cosh u, where Y(t) = a(1 - cos t) is the cycloidal
         ordinate of Theorem 3.2, Eq. (60), continued to complex t;
* (288)  R_a(u) = a (1 + (u²/2) r_E(iu)²);
* (289)  the catenoid Σ_a(u,v) = a(cosh u cos v, cosh u sin v, u);
* (290)  first fundamental form g_a = a² cosh² u (du² + dv²);
* (291)  Gaussian curvature K_a(u) = -1/(a² cosh⁴ u);
* the mean curvature vanishes identically, and the principal curvatures are opposite.

The fundamental forms are computed from the actual partial derivatives of Σ_a
(`deriv`), with the Euclidean inner product of ℝ³ and the unit normal.
-/
import M15Cert.Kernel

open Complex Real

namespace M15

/-- The cycloidal ordinate Y(t) = a(1 - cos t), continued to complex t. -/
noncomputable def cycY (a : ℝ) (t : ℂ) : ℂ := a * (1 - Complex.cos t)

/-- Eq. (287): R_a(u) := a - Y(iu) = a cosh u. -/
theorem catenoid_radius (a u : ℝ) : (a : ℂ) - cycY a (I * u) = ((a * Real.cosh u : ℝ) : ℂ) := by
  unfold cycY
  rw [show I * (u : ℂ) = (u : ℂ) * I by ring, Complex.cos_mul_I]
  push_cast; ring

/-- Eq. (288): R_a(u) = a(1 + (u²/2) r_E(iu)²), with the entire kernel `rEc`. -/
theorem catenoid_radius_eulerian (a u : ℝ) :
    ((a * Real.cosh u : ℝ) : ℂ) = (a : ℂ) * (1 + (u : ℂ) ^ 2 / 2 * rEc (I * u) ^ 2) := by
  rw [rEc_I_mul]
  have h := sq_mul_rEi_sq u
  have : ((u : ℂ) ^ 2 / 2 * (rEi u : ℂ) ^ 2) = ((Real.cosh u - 1 : ℝ) : ℂ) := by
    rw [← h]; push_cast; ring
  rw [this]; push_cast; ring

/-! ### The catenoid and its fundamental forms -/

/-- Euclidean inner product on ℝ³ = ℝ × ℝ × ℝ. -/
def dot3 (p q : ℝ × ℝ × ℝ) : ℝ := p.1 * q.1 + p.2.1 * q.2.1 + p.2.2 * q.2.2

/-- Eq. (289): the catenoid Σ_a(u, v) = a (cosh u cos v, cosh u sin v, u). -/
noncomputable def catenoid (a u v : ℝ) : ℝ × ℝ × ℝ :=
  (a * Real.cosh u * Real.cos v, a * Real.cosh u * Real.sin v, a * u)

/-- Its circumferential radius is R_a(u) = a cosh u (for a ≥ 0). -/
theorem catenoid_circle_radius (a u v : ℝ) (ha : 0 ≤ a) :
    Real.sqrt ((catenoid a u v).1 ^ 2 + (catenoid a u v).2.1 ^ 2) = a * Real.cosh u := by
  unfold catenoid
  have h : (a * Real.cosh u * Real.cos v) ^ 2 + (a * Real.cosh u * Real.sin v) ^ 2 =
      (a * Real.cosh u) ^ 2 := by
    have := Real.sin_sq_add_cos_sq v; nlinarith [this]
  simp only
  rw [h, Real.sqrt_sq (mul_nonneg ha (Real.cosh_pos u).le)]

noncomputable def catU (a u v : ℝ) : ℝ × ℝ × ℝ :=
  (a * Real.sinh u * Real.cos v, a * Real.sinh u * Real.sin v, a)
noncomputable def catV (a u v : ℝ) : ℝ × ℝ × ℝ :=
  (-(a * Real.cosh u * Real.sin v), a * Real.cosh u * Real.cos v, 0)
noncomputable def catUU (a u v : ℝ) : ℝ × ℝ × ℝ :=
  (a * Real.cosh u * Real.cos v, a * Real.cosh u * Real.sin v, 0)
noncomputable def catUV (a u v : ℝ) : ℝ × ℝ × ℝ :=
  (-(a * Real.sinh u * Real.sin v), a * Real.sinh u * Real.cos v, 0)
noncomputable def catVV (a u v : ℝ) : ℝ × ℝ × ℝ :=
  (-(a * Real.cosh u * Real.cos v), -(a * Real.cosh u * Real.sin v), 0)

theorem hasDerivAt_catenoid_u (a u v : ℝ) :
    HasDerivAt (fun u => catenoid a u v) (catU a u v) u := by
  unfold catenoid catU
  refine HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ ?_)
  · simpa using ((Real.hasDerivAt_cosh u).const_mul a).mul_const (Real.cos v)
  · simpa using ((Real.hasDerivAt_cosh u).const_mul a).mul_const (Real.sin v)
  · simpa using (hasDerivAt_id u).const_mul a

theorem hasDerivAt_catenoid_v (a u v : ℝ) :
    HasDerivAt (fun v => catenoid a u v) (catV a u v) v := by
  unfold catenoid catV
  refine HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ ?_)
  · simpa using (Real.hasDerivAt_cos v).const_mul (a * Real.cosh u)
  · simpa using (Real.hasDerivAt_sin v).const_mul (a * Real.cosh u)
  · exact hasDerivAt_const v (a * u)

theorem hasDerivAt_catU_u (a u v : ℝ) : HasDerivAt (fun u => catU a u v) (catUU a u v) u := by
  unfold catU catUU
  refine HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ ?_)
  · simpa using ((Real.hasDerivAt_sinh u).const_mul a).mul_const (Real.cos v)
  · simpa using ((Real.hasDerivAt_sinh u).const_mul a).mul_const (Real.sin v)
  · exact hasDerivAt_const u a

theorem hasDerivAt_catU_v (a u v : ℝ) : HasDerivAt (fun v => catU a u v) (catUV a u v) v := by
  unfold catU catUV
  refine HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ ?_)
  · simpa using (Real.hasDerivAt_cos v).const_mul (a * Real.sinh u)
  · simpa using (Real.hasDerivAt_sin v).const_mul (a * Real.sinh u)
  · exact hasDerivAt_const v a

theorem hasDerivAt_catV_u (a u v : ℝ) : HasDerivAt (fun u => catV a u v) (catUV a u v) u := by
  unfold catV catUV
  refine HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ ?_)
  · have h := (((Real.hasDerivAt_cosh u).const_mul a).mul_const (Real.sin v)).neg
    exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => by simp)
  · simpa using ((Real.hasDerivAt_cosh u).const_mul a).mul_const (Real.cos v)
  · exact hasDerivAt_const u (0 : ℝ)

theorem hasDerivAt_catV_v (a u v : ℝ) : HasDerivAt (fun v => catV a u v) (catVV a u v) v := by
  unfold catV catVV
  refine HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ ?_)
  · have h := ((Real.hasDerivAt_sin v).const_mul (a * Real.cosh u)).neg
    have h' : HasDerivAt (fun y => -(a * Real.cosh u * Real.sin y))
        (-(a * Real.cosh u * Real.cos v)) v :=
      h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => by simp)
    simpa [neg_mul] using h'
  · simpa using (Real.hasDerivAt_cos v).const_mul (a * Real.cosh u)
  · exact hasDerivAt_const v (0 : ℝ)

/-- The partial derivatives of Σ_a, as Fréchet derivatives (`deriv`). -/
theorem deriv_catenoid_u (a u v : ℝ) : deriv (fun u => catenoid a u v) u = catU a u v :=
  (hasDerivAt_catenoid_u a u v).deriv
theorem deriv_catenoid_v (a u v : ℝ) : deriv (fun v => catenoid a u v) v = catV a u v :=
  (hasDerivAt_catenoid_v a u v).deriv
theorem deriv_deriv_catenoid_uu (a u v : ℝ) :
    deriv (fun u => deriv (fun u => catenoid a u v) u) u = catUU a u v := by
  simp only [deriv_catenoid_u]; exact (hasDerivAt_catU_u a u v).deriv
theorem deriv_deriv_catenoid_uv (a u v : ℝ) :
    deriv (fun v => deriv (fun u => catenoid a u v) u) v = catUV a u v := by
  simp only [deriv_catenoid_u]; exact (hasDerivAt_catU_v a u v).deriv
theorem deriv_deriv_catenoid_vu (a u v : ℝ) :
    deriv (fun u => deriv (fun v => catenoid a u v) v) u = catUV a u v := by
  simp only [deriv_catenoid_v]; exact (hasDerivAt_catV_u a u v).deriv
theorem deriv_deriv_catenoid_vv (a u v : ℝ) :
    deriv (fun v => deriv (fun v => catenoid a u v) v) v = catVV a u v := by
  simp only [deriv_catenoid_v]; exact (hasDerivAt_catV_v a u v).deriv

/-- The unit normal (cos v, sin v, -sinh u)/cosh u. -/
noncomputable def catNormal (u v : ℝ) : ℝ × ℝ × ℝ :=
  (Real.cos v / Real.cosh u, Real.sin v / Real.cosh u, -Real.sinh u / Real.cosh u)

/-- First fundamental form E, F, G. -/
noncomputable def firstE (a u v : ℝ) : ℝ := dot3 (deriv (fun u => catenoid a u v) u) (deriv (fun u => catenoid a u v) u)
noncomputable def firstF (a u v : ℝ) : ℝ := dot3 (deriv (fun u => catenoid a u v) u) (deriv (fun v => catenoid a u v) v)
noncomputable def firstG (a u v : ℝ) : ℝ := dot3 (deriv (fun v => catenoid a u v) v) (deriv (fun v => catenoid a u v) v)

/-- Second fundamental form L, M, N with respect to the unit normal. -/
noncomputable def secondL (a u v : ℝ) : ℝ :=
  dot3 (deriv (fun u => deriv (fun u => catenoid a u v) u) u) (catNormal u v)
noncomputable def secondM (a u v : ℝ) : ℝ :=
  dot3 (deriv (fun v => deriv (fun u => catenoid a u v) u) v) (catNormal u v)
noncomputable def secondN (a u v : ℝ) : ℝ :=
  dot3 (deriv (fun v => deriv (fun v => catenoid a u v) v) v) (catNormal u v)

/-- Gaussian and mean curvature from the two fundamental forms. -/
noncomputable def gaussK (a u v : ℝ) : ℝ :=
  (secondL a u v * secondN a u v - secondM a u v ^ 2) /
    (firstE a u v * firstG a u v - firstF a u v ^ 2)
noncomputable def meanH (a u v : ℝ) : ℝ :=
  (firstE a u v * secondN a u v - 2 * firstF a u v * secondM a u v + firstG a u v * secondL a u v) /
    (2 * (firstE a u v * firstG a u v - firstF a u v ^ 2))

/-- Eq. (290): E = G = a² cosh² u and F = 0, i.e. g_a = a² cosh² u (du² + dv²). -/
theorem catenoid_first_form (a u v : ℝ) :
    firstE a u v = a ^ 2 * Real.cosh u ^ 2 ∧ firstF a u v = 0 ∧
      firstG a u v = a ^ 2 * Real.cosh u ^ 2 := by
  unfold firstE firstF firstG
  rw [deriv_catenoid_u, deriv_catenoid_v]
  unfold catU catV dot3
  have hc := Real.cosh_sq u
  have hs := Real.sin_sq_add_cos_sq v
  refine ⟨?_, ?_, ?_⟩
  · simp only; linear_combination (a ^ 2 * Real.sinh u ^ 2) * hs - a ^ 2 * hc
  · simp only; ring
  · simp only; linear_combination (a ^ 2 * Real.cosh u ^ 2) * hs

/-- The metric g_a as a quadratic form: g_a(du, dv) = a² cosh² u (du² + dv²). -/
theorem catenoid_metric (a u v du dv : ℝ) :
    firstE a u v * du ^ 2 + 2 * firstF a u v * du * dv + firstG a u v * dv ^ 2 =
      a ^ 2 * Real.cosh u ^ 2 * (du ^ 2 + dv ^ 2) := by
  obtain ⟨hE, hF, hG⟩ := catenoid_first_form a u v
  rw [hE, hF, hG]; ring

/-- The normal is a unit vector orthogonal to both coordinate tangent vectors. -/
theorem catNormal_unit_orthogonal (a u v : ℝ) :
    dot3 (catNormal u v) (catNormal u v) = 1 ∧
      dot3 (deriv (fun u => catenoid a u v) u) (catNormal u v) = 0 ∧
      dot3 (deriv (fun v => catenoid a u v) v) (catNormal u v) = 0 := by
  rw [deriv_catenoid_u, deriv_catenoid_v]
  unfold catNormal catU catV dot3
  have hc : Real.cosh u ≠ 0 := (Real.cosh_pos u).ne'
  have hc2 := Real.cosh_sq u
  have hs := Real.sin_sq_add_cos_sq v
  refine ⟨?_, ?_, ?_⟩
  · simp only
    have e : Real.cos v / Real.cosh u * (Real.cos v / Real.cosh u) +
        Real.sin v / Real.cosh u * (Real.sin v / Real.cosh u) +
        -Real.sinh u / Real.cosh u * (-Real.sinh u / Real.cosh u) =
        (Real.sin v ^ 2 + Real.cos v ^ 2 + Real.sinh u ^ 2) / Real.cosh u ^ 2 := by ring
    rw [e, hs, add_comm, ← hc2, div_self (pow_ne_zero 2 hc)]
  · simp only
    have e : a * Real.sinh u * Real.cos v * (Real.cos v / Real.cosh u) +
        a * Real.sinh u * Real.sin v * (Real.sin v / Real.cosh u) +
        a * (-Real.sinh u / Real.cosh u) =
        a * Real.sinh u * (Real.sin v ^ 2 + Real.cos v ^ 2 - 1) / Real.cosh u := by ring
    rw [e, hs]; simp
  · simp only; ring

/-- The second fundamental form: L = a, M = 0, N = -a. -/
theorem catenoid_second_form (a u v : ℝ) :
    secondL a u v = a ∧ secondM a u v = 0 ∧ secondN a u v = -a := by
  unfold secondL secondM secondN
  rw [deriv_deriv_catenoid_uu, deriv_deriv_catenoid_uv, deriv_deriv_catenoid_vv]
  unfold catUU catUV catVV catNormal dot3
  have hc : Real.cosh u ≠ 0 := (Real.cosh_pos u).ne'
  have hs := Real.sin_sq_add_cos_sq v
  refine ⟨?_, ?_, ?_⟩
  · simp only
    have e : a * Real.cosh u * Real.cos v * (Real.cos v / Real.cosh u) +
        a * Real.cosh u * Real.sin v * (Real.sin v / Real.cosh u) +
        0 * (-Real.sinh u / Real.cosh u) =
        a * (Real.sin v ^ 2 + Real.cos v ^ 2) * (Real.cosh u / Real.cosh u) := by ring
    rw [e, hs, div_self hc]; ring
  · simp only; ring
  · simp only
    have e : -(a * Real.cosh u * Real.cos v) * (Real.cos v / Real.cosh u) +
        -(a * Real.cosh u * Real.sin v) * (Real.sin v / Real.cosh u) +
        0 * (-Real.sinh u / Real.cosh u) =
        -a * (Real.sin v ^ 2 + Real.cos v ^ 2) * (Real.cosh u / Real.cosh u) := by ring
    rw [e, hs, div_self hc]; ring

/-- Eq. (291): K_a(u) = -1/(a² cosh⁴ u), for a ≠ 0. -/
theorem catenoid_gaussian_curvature (a u v : ℝ) (ha : a ≠ 0) :
    gaussK a u v = -1 / (a ^ 2 * Real.cosh u ^ 4) := by
  unfold gaussK
  obtain ⟨hE, hF, hG⟩ := catenoid_first_form a u v
  obtain ⟨hL, hM, hN⟩ := catenoid_second_form a u v
  rw [hE, hF, hG, hL, hM, hN]
  have hc : Real.cosh u ≠ 0 := (Real.cosh_pos u).ne'
  field_simp
  ring

/-- The mean curvature vanishes identically (a ≠ 0): the catenoid is minimal. -/
theorem catenoid_mean_curvature (a u v : ℝ) : meanH a u v = 0 := by
  unfold meanH
  obtain ⟨hE, hF, hG⟩ := catenoid_first_form a u v
  obtain ⟨hL, hM, hN⟩ := catenoid_second_form a u v
  rw [hE, hF, hG, hL, hM, hN]
  ring

/-- The principal curvatures L/E and N/G (F = M = 0) are opposite, ±1/(a cosh² u),
and their product is K_a. -/
theorem catenoid_principal_curvatures (a u v : ℝ) (ha : a ≠ 0) :
    secondL a u v / firstE a u v = 1 / (a * Real.cosh u ^ 2) ∧
      secondN a u v / firstG a u v = -(1 / (a * Real.cosh u ^ 2)) ∧
      secondL a u v / firstE a u v * (secondN a u v / firstG a u v) = gaussK a u v := by
  obtain ⟨hE, hF, hG⟩ := catenoid_first_form a u v
  obtain ⟨hL, hM, hN⟩ := catenoid_second_form a u v
  have hc : Real.cosh u ≠ 0 := (Real.cosh_pos u).ne'
  refine ⟨?_, ?_, ?_⟩
  · rw [hL, hE]; field_simp
  · rw [hN, hG]; field_simp
  · rw [catenoid_gaussian_curvature a u v ha, hL, hE, hN, hG]; field_simp

end M15
