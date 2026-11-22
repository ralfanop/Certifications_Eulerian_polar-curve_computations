import PrivateApex.SlopeAllOrders

/-!
PRIVATE.  Manuscript 15, Corollary 7.7: the two representations of the even-order coefficients.

The even-order coefficients are defined in `SlopeAllOrders` by the transfer from the odd orders,
`eC = evenTransfer dC`, that is `Q(z) = D(z/(1+z)) / ((1+z)^(3/2) (1+3z))`.  Here the even slopes
are expanded a second time, directly from their own Fourier integral, which gives the coefficients
`eDirect`, that is `Q(z) = (1+3z)^(-5/2) C(z/(1+3z))` (`even_slope_direct_hasExp`).  Uniqueness
of asymptotic coefficients then yields the identity of the two formal series at every order:

  `eDirect_eq_eC : eDirect = eC`.

This is an identity between formal power series with rational coefficients.  It is obtained
here from two asymptotic expansions of the same sequence; no convergence is involved.
-/

namespace PrivateApex
open Real Finset MeasureTheory

theorem eDirect_cast (i : ℕ) : ((eDirect i : ℚ) : ℝ) =
    cmul (cmul (cmul (fun i => (-3 : ℝ) ^ i) (fun i => (-3 : ℝ) ^ i))
      (fun i => (binQ i : ℝ) * 3 ^ i)) (ccomp (fun i => (cC i : ℝ)) (fun i => (-3 : ℝ) ^ i)) i := by
  have h0 : (fun i => ((cmul (geoQ 3) (geoQ 3) i : ℚ) : ℝ)) =
      cmul (fun i => ((geoQ 3 i : ℚ) : ℝ)) (fun i => ((geoQ 3 i : ℚ) : ℝ)) :=
    funext fun i => map_cmul (Rat.castHom ℝ) _ _ i
  have h1 : (fun i => ((cmul (cmul (geoQ 3) (geoQ 3)) (binQc 3) i : ℚ) : ℝ)) =
      cmul (fun i => ((cmul (geoQ 3) (geoQ 3) i : ℚ) : ℝ)) (fun i => ((binQc 3 i : ℚ) : ℝ)) :=
    funext fun i => map_cmul (Rat.castHom ℝ) _ _ i
  have h2 : (fun i => ((ccomp cC (geoQ 3) i : ℚ) : ℝ)) =
      ccomp (fun i => (cC i : ℝ)) (fun i => ((geoQ 3 i : ℚ) : ℝ)) :=
    funext fun i => map_ccomp (Rat.castHom ℝ) _ _ i
  have h3 : ((eDirect i : ℚ) : ℝ) =
      cmul (fun i => ((cmul (cmul (geoQ 3) (geoQ 3)) (binQc 3) i : ℚ) : ℝ))
        (fun i => ((ccomp cC (geoQ 3) i : ℚ) : ℝ)) i := map_cmul (Rat.castHom ℝ) _ _ i
  rw [h3, h1, h0, h2, geoQ_cast, binQc_cast]
  simp only [Rat.cast_ofNat]

theorem even_direct_identity {N W H σ r p : ℝ} (hN : 0 < N) (hσ : 0 < σ) (hr : 0 < r)
    (hp : 0 < p) (hH : 4 * (N + 3) * H = σ * r * p) :
    (8 * N ^ 2 / (p * (N + 3)) * W) / (2 * σ) = N / (N + 3) * (N / (N + 3)) * r * (W / H) := by
  have hH' : H = σ * r * p / (4 * (N + 3)) := by
    rw [eq_div_iff (by positivity)]
    linarith
  rw [hH']
  field_simp
  ring

/-- The even slopes expanded directly from their Fourier integral: the coefficients are
`eDirect`. -/
theorem even_slope_direct_hasExp :
    HasExp {m : ℕ | 2 ≤ m} (fun m => 1 / ((2 * m + 1 : ℕ) : ℝ))
      (fun m => ((slopeQ (2 * m) : ℚ) : ℝ) / (2 * sig ((2 * m + 1 : ℕ) : ℝ)))
      (fun i => (eDirect i : ℝ)) := by
  have hw0 : ∀ m ∈ {m : ℕ | 2 ≤ m}, (0 : ℝ) ≤ 1 / ((2 * m + 1 : ℕ) : ℝ) :=
    fun m _ => by positivity
  have h5 : ∀ m ∈ {m : ℕ | 2 ≤ m}, (5 : ℝ) ≤ ((2 * m + 1 : ℕ) : ℝ) := fun m hm => by
    exact_mod_cast (show 5 ≤ 2 * m + 1 by have : 2 ≤ m := hm; omega)
  have hF := laplace_hasExp.comap (T := {m : ℕ | 2 ≤ m}) (fun m => 2 * m + 2)
    (fun m _ => (show 2 ≤ 2 * m + 2 by omega))
  have hy3 : HasExp {m : ℕ | 2 ≤ m} (fun m => 1 / ((2 * m + 1 : ℕ) : ℝ))
      (fun m => 1 / (1 + 3 * (1 / ((2 * m + 1 : ℕ) : ℝ)))) (fun i => (-3 : ℝ) ^ i) :=
    geo_hasExp 3 (by norm_num) hw0
  have hFw := hF.comp (w := fun m => 1 / ((2 * m + 1 : ℕ) : ℝ))
    (y := fun m => 1 / (1 + 3 * (1 / ((2 * m + 1 : ℕ) : ℝ))))
    (fun m _ => by
      show 1 / (((2 * m + 2 : ℕ) : ℝ) + 2) =
        1 / ((2 * m + 1 : ℕ) : ℝ) * (1 / (1 + 3 * (1 / ((2 * m + 1 : ℕ) : ℝ))))
      push_cast
      field_simp
      ring) hy3
  have hρ : HasExp {m : ℕ | 2 ≤ m} (fun m => 1 / ((2 * m + 1 : ℕ) : ℝ))
      (fun m => (1 + 3 * (1 / ((2 * m + 1 : ℕ) : ℝ))) ^ (-1 / 2 : ℝ))
      (fun i => (binQ i : ℝ) * 3 ^ i) :=
    bin_hasExp 3 (by norm_num) fun m hm => by
      have h := h5 m hm
      constructor
      · positivity
      · rw [mul_one_div, div_le_iff₀ (by linarith)]
        linarith
  have hprod := ((hy3.mul hy3).mul hρ).mul hFw
  refine (hprod.congr fun m hmem => ?_).congr_coeff fun i => eDirect_cast i
  have hm' : 2 ≤ m := hmem
  have hN0 : (0 : ℝ) < ((2 * m + 1 : ℕ) : ℝ) := by positivity
  have hD : ((2 * m + 2 : ℕ) : ℝ) = ((2 * m + 1 : ℕ) : ℝ) + 1 := by
    push_cast
    ring
  have hy3e : 1 / (1 + 3 * (1 / ((2 * m + 1 : ℕ) : ℝ))) =
      ((2 * m + 1 : ℕ) : ℝ) / (((2 * m + 1 : ℕ) : ℝ) + 3) := by field_simp
  have hρe : (1 + 3 * (1 / ((2 * m + 1 : ℕ) : ℝ))) ^ (-1 / 2 : ℝ) =
      √(((2 * m + 1 : ℕ) : ℝ) / (((2 * m + 1 : ℕ) : ℝ) + 3)) := by
    rw [rpow_neg_half (by positivity), hy3e]
  have hfour := four_D_hm (D := ((2 * m + 1 : ℕ) : ℝ) + 1) (by linarith)
  rw [sig_succ hN0] at hfour
  have hr : √(((2 * m + 1 : ℕ) : ℝ) / (((2 * m + 1 : ℕ) : ℝ) + 1)) *
      √((((2 * m + 1 : ℕ) : ℝ) + 1) / (((2 * m + 1 : ℕ) : ℝ) + 1 + 2)) =
      √(((2 * m + 1 : ℕ) : ℝ) / (((2 * m + 1 : ℕ) : ℝ) + 3)) := by
    rw [← sqrt_mul (by positivity)]
    congr 1
    field_simp
    ring
  have hH : 4 * (((2 * m + 1 : ℕ) : ℝ) + 3) * hm (((2 * m + 1 : ℕ) : ℝ) + 1 + 2) 1 =
      sig ((2 * m + 1 : ℕ) : ℝ) *
        √(((2 * m + 1 : ℕ) : ℝ) / (((2 * m + 1 : ℕ) : ℝ) + 3)) * π := by
    have e : 4 * (((2 * m + 1 : ℕ) : ℝ) + 3) * hm (((2 * m + 1 : ℕ) : ℝ) + 1 + 2) 1 =
        (4 * (((2 * m + 1 : ℕ) : ℝ) + 1) / π * hm (((2 * m + 1 : ℕ) : ℝ) + 1 + 2) 1) *
          (π * (((2 * m + 1 : ℕ) : ℝ) + 3) / (((2 * m + 1 : ℕ) : ℝ) + 1)) := by
      field_simp
    rw [e, hfour, ← hr]
    field_simp
    ring
  show ((slopeQ (2 * m) : ℚ) : ℝ) / (2 * sig ((2 * m + 1 : ℕ) : ℝ)) =
    1 / (1 + 3 * (1 / ((2 * m + 1 : ℕ) : ℝ))) * (1 / (1 + 3 * (1 / ((2 * m + 1 : ℕ) : ℝ)))) *
      (1 + 3 * (1 / ((2 * m + 1 : ℕ) : ℝ))) ^ (-1 / 2 : ℝ) *
      ((∫ x in Set.Ioi (0 : ℝ), weight (2 * m + 2) x) / hm (((2 * m + 2 : ℕ) : ℝ) + 2) 1)
  rw [slopeQ_even_eq_integral hm', hD, hy3e, hρe]
  exact even_direct_identity hN0 (sig_pos' hN0) (sqrt_pos.2 (by positivity)) pi_pos hH

/-- **The two representations of the even-order coefficients coincide at every order.** -/
theorem eDirect_eq_eC : eDirect = eC := by
  have h := eC_unique (fun i => (eDirect i : ℝ)) even_slope_direct_hasExp
  funext i
  exact_mod_cast congrFun h i

theorem eDirect_apply (j : ℕ) : eDirect j = eC j := congrFun eDirect_eq_eC j

end PrivateApex
