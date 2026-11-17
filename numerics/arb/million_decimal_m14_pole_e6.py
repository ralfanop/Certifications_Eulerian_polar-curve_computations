from million_decimal_common import arb, record, finish, exact

pi = arb.pi()
s2 = arb(2).sqrt()
s8 = arb(8).sqrt()
k = pi/s8
k2 = (pi/4)/(pi/4).sin()
k3 = pi*s2/4
assert k.overlaps(k2) and k.overlaps(k3) and k2.overlaps(k3)
record("kappa_pi_over_sqrt8",k)
record("kappa_trig_endpoint",k2)
record("kappa_pi_sqrt2_over_four",k3)
record("pole_positive_imaginary_realpart",pi/4)
record("pole_positive_imaginary_imagpart",-pi/4)
record("pole_negative_imaginary_imagpart",pi/4)
gap = 2*pi/s2
assert gap.overlaps(4*k)
record("minimum_right_semicircle_pole_separation",gap)
record("four_kappa",4*k)
# Exact rational coefficients in the local E6 polynomial decomposition:
for name,q in [("A_u4", "1/41472"), ("A_u2w", "-1/1728"),
               ("A_u2", "-1/108"), ("A_w2", "1/192"),
               ("A_w", "1/12"), ("B_u2", "1/48"), ("B_w", "-1/32")]:
    record(name,exact(q))
finish("m14polee6")
