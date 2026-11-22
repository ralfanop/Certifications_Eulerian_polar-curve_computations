/-
Manuscript 15, Section 7.11, Proposition 7.27 -- Eulerian metric and proper radial length.

* (297)  the signed meridional arclength from the neck is ℓ = a sinh u = a u r_E(2iu);
* a² + ℓ² = a² cosh² u and dℓ = a cosh u du;
* (298)→(299)  the Ellis line element -c²dt² + dℓ² + (a² + ℓ²) dΩ² becomes
         -c²dt² + a²(1 + u² r_E(2iu)²)(du² + dΩ²), as an identity of quadratic forms in
         the tangent components (dt, du, dϑ, dφ), dΩ² = dϑ² + sin²ϑ dφ²;
* the equatorial section (dt = 0, ϑ = π/2) is the catenoid metric of Eq. (290), with the
         coefficients computed from the catenoid of Proposition 7.25 (isometry);
* (300)  the proper radial length between the critical boundary circles is
         L_* = ℓ(u_*) - ℓ(-u_*) = 2a u_* r_E(2iu_*) = 2a/λ_CL; it is also the integral of
         the meridional line element a cosh u du over [-u_*, u_*].
-/
import M15Cert.Catenoid
import M15Cert.CarliniLaplace

open Complex Real

namespace M15

/-- The signed meridional arclength from the neck. -/
noncomputable def ellL (a u : ℝ) : ℝ := a * Real.sinh u

/-- r_E(2iu) as a real number: sinh u / u, with the removable value 1 at u = 0. -/
noncomputable def rE2i (u : ℝ) : ℝ := if u = 0 then 1 else Real.sinh u / u

lemma rEc_two_I_mul' (u : ℝ) : rEc (2 * I * u) = (rE2i u : ℂ) := rEc_two_I_mul u

/-- Eq. (297): ℓ = a sinh u = a u r_E(2iu). -/
theorem ellL_eulerian (a u : ℝ) :
    ((ellL a u : ℝ) : ℂ) = (a : ℂ) * u * rEc (2 * I * u) := by
  rw [rEc_two_I_mul']
  unfold ellL rE2i
  by_cases h : u = 0
  · simp [h]
  · simp only [h, ↓reduceIte]
    have hu : (u : ℂ) ≠ 0 := by exact_mod_cast h
    push_cast; field_simp

theorem ellL_eq_mul_rE2i (a u : ℝ) : ellL a u = a * u * rE2i u := by
  unfold ellL rE2i
  by_cases h : u = 0
  · simp [h]
  · simp only [h, ↓reduceIte]; field_simp

/-- dℓ = a cosh u du. -/
theorem hasDerivAt_ellL (a u : ℝ) : HasDerivAt (ellL a) (a * Real.cosh u) u := by
  unfold ellL; exact (Real.hasDerivAt_sinh u).const_mul a

/-- The meridian u ↦ (a cosh u, a u) of the catenoid has speed a cosh u (a ≥ 0),
so ℓ is its signed arclength from the neck u = 0. -/
theorem meridian_speed (a u : ℝ) (ha : 0 ≤ a) :
    Real.sqrt ((a * Real.sinh u) ^ 2 + a ^ 2) = a * Real.cosh u := by
  have h : (a * Real.sinh u) ^ 2 + a ^ 2 = (a * Real.cosh u) ^ 2 := by
    have := Real.cosh_sq u; nlinarith [this]
  rw [h, Real.sqrt_sq (mul_nonneg ha (Real.cosh_pos u).le)]

theorem ellL_eq_integral (a u : ℝ) : ellL a u = ∫ t in (0 : ℝ)..u, a * Real.cosh t := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_ellL a t)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  simp [ellL]

/-- a² + ℓ² = a² cosh² u. -/
theorem sq_add_ellL_sq (a u : ℝ) : a ^ 2 + ellL a u ^ 2 = a ^ 2 * Real.cosh u ^ 2 := by
  unfold ellL; have := Real.cosh_sq u; nlinarith [this]

/-- 1 + u² r_E(2iu)² = cosh² u. -/
theorem one_add_sq_rE2i_sq (u : ℝ) : 1 + u ^ 2 * rE2i u ^ 2 = Real.cosh u ^ 2 := by
  have := sq_mul_rEi_two_sq u
  unfold rE2i; rw [this, Real.cosh_sq]; ring

/-- The Ellis line element (298) in the coordinates (t, ℓ, ϑ, φ). -/
noncomputable def ellisOriginal (a c ℓ ϑ dt dℓ dϑ dφ : ℝ) : ℝ :=
  -c ^ 2 * dt ^ 2 + dℓ ^ 2 + (a ^ 2 + ℓ ^ 2) * (dϑ ^ 2 + Real.sin ϑ ^ 2 * dφ ^ 2)

/-- Eq. (299): with ℓ = a sinh u and dℓ = ℓ'(u) du, the Ellis line element becomes
-c²dt² + a²(1 + u² r_E(2iu)²)(du² + dΩ²), for all tangent components. -/
theorem ellis_eulerian (a c u ϑ dt du dϑ dφ : ℝ) :
    ellisOriginal a c (ellL a u) ϑ dt (deriv (ellL a) u * du) dϑ dφ =
      -c ^ 2 * dt ^ 2 +
        a ^ 2 * (1 + u ^ 2 * rE2i u ^ 2) * (du ^ 2 + (dϑ ^ 2 + Real.sin ϑ ^ 2 * dφ ^ 2)) := by
  unfold ellisOriginal
  rw [(hasDerivAt_ellL a u).deriv, sq_add_ellL_sq, one_add_sq_rE2i_sq]
  ring

/-- The same identity with the complex kernel r_E(2iu) of Eq. (1). -/
theorem ellis_eulerian_rEc (a c u ϑ dt du dϑ dφ : ℝ) :
    ((ellisOriginal a c (ellL a u) ϑ dt (deriv (ellL a) u * du) dϑ dφ : ℝ) : ℂ) =
      -(c : ℂ) ^ 2 * dt ^ 2 + (a : ℂ) ^ 2 * (1 + (u : ℂ) ^ 2 * rEc (2 * I * u) ^ 2) *
        (du ^ 2 + (dϑ ^ 2 + Real.sin ϑ ^ 2 * dφ ^ 2)) := by
  rw [ellis_eulerian, rEc_two_I_mul']; push_cast; ring

/-- The equatorial spatial section (dt = 0, ϑ = π/2, dϑ = 0) of the Ellis metric is the
first fundamental form of the catenoid Σ_a of Proposition 7.25, with v = φ: the catenoid
is isometric to this section. -/
theorem ellis_equatorial_eq_catenoid (a c u v du dv : ℝ) :
    ellisOriginal a c (ellL a u) (Real.pi / 2) 0 (deriv (ellL a) u * du) 0 dv =
      firstE a u v * du ^ 2 + 2 * firstF a u v * du * dv + firstG a u v * dv ^ 2 := by
  rw [catenoid_metric, ellis_eulerian, one_add_sq_rE2i_sq, Real.sin_pi_div_two]
  ring

/-- Eq. (300): L_* = ℓ(u_*) - ℓ(-u_*) = 2a u_* r_E(2iu_*) = 2a/λ_CL. -/
theorem critical_length (a : ℝ) :
    ellL a uStar - ellL a (-uStar) = 2 * a * uStar * rE2i uStar ∧
      ellL a uStar - ellL a (-uStar) = 2 * a / lambdaCL := by
  have hs := sinh_uStar_pos
  refine ⟨?_, ?_⟩
  · rw [ellL_eq_mul_rE2i, ellL_eq_mul_rE2i]
    unfold rE2i
    have hu := uStar_pos.ne'
    simp only [hu, neg_eq_zero, ↓reduceIte, Real.sinh_neg]
    field_simp; ring
  · unfold ellL
    rw [Real.sinh_neg, bicone_tangent.2]
    ring

/-- The same proper length as the integral of the meridional line element. -/
theorem critical_length_integral (a : ℝ) :
    ∫ u in (-uStar)..uStar, a * Real.cosh u = 2 * a / lambdaCL := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_ellL a t)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  exact (critical_length a).2

/-- In units of a: L_*/a = 2/λ_CL = 2 sinh u_* (the quantity certified in Arb). -/
theorem critical_length_over_a (a : ℝ) (ha : a ≠ 0) :
    (ellL a uStar - ellL a (-uStar)) / a = 2 / lambdaCL ∧ 2 / lambdaCL = 2 * Real.sinh uStar := by
  refine ⟨?_, ?_⟩
  · rw [(critical_length a).2]; field_simp
  · rw [bicone_tangent.2]; ring

end M15
