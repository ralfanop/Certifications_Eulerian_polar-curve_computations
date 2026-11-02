import EulerianGrothendieck.ExactPolynomialAllOrders
import UniformLanczos
/-! Axiom audit of the 2 November 2026 additions for manuscript 12 (Lemma 9.8 at every order;
Lemma 5.5 joined to Lemma 5.7(b); Lemma 5.7(a); Corollary 5.10).
Run: `lake env lean AuditV12Remaining.lean` in this directory. -/
open EulerianGrothendieck.AllOrders
#print axioms euler
#print axioms Ppoly_rec
#print axioms pc_support
#print axioms coeff_eq_G
#print axioms uniformMomentRatio_eq_g_sum
#print axioms G_at_zero_pos
#print axioms gPoly_natDegree
#print axioms gPoly_eval
#print axioms qPoly_natDegree
#print axioms qPoly_eval
#print axioms UniformLanczos.Joined.w_even
#print axioms UniformLanczos.Joined.hP_actual
#print axioms UniformLanczos.Joined.endpoint_actual
#print axioms UniformLanczos.Profile.F_bounds
#print axioms UniformLanczos.Profile.F_strictMonoOn
#print axioms UniformLanczos.Profile.F_continuousOn
#print axioms UniformLanczos.Profile.F_tendsto
#print axioms UniformLanczos.Profile.F_series
#print axioms UniformLanczos.Profile.lemma_5_7a
#print axioms UniformLanczos.Profile.lemma_5_7a_one
#print axioms UniformLanczos.endpoint_concrete
#print axioms UniformLanczos.F_expansion7_explicit
