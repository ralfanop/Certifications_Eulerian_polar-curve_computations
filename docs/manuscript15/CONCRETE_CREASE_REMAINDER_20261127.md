# M15 §12: concrete sixth-order crease remainder

Source: author-supplied FRENCH_YEN_1992_2002(4) ZIP, SHA256
60b2cdb28db0863e36e623f19cf62cf8f06364e3039f743024a4dce77fa96b5b;
15.tex SHA256 7226b511a439c972f08562c7754b9db910c70a0a1689ea97a875ac91ec651d06.
Labels cor:ridge-crease, prop:cross-crease15, eq:cross-creaseJet,
eq:cross-creaseSelf, eq:cross-creaseLim.

## Analytic proof (not a kernel certificate)

For real k in [1/2,3/2], let
F_k(u) = integral from 0 to u of k/sqrt(1+(1+k²)sinh² t) dt,
and D_k(u)=cosh(u) cos(F_k(u))-1. The derivative of the integrated
orbit angle in the manuscript, b/sqrt(cosh²(u)-b²), gives precisely this
density by k=b/sqrt(1-b²), b in (0,1), and the zero initial value.
Thus F_k(u)=Phi_b(sinh u).

Extend the density to the complex disk |z|≤1/4 with the principal
square root. The power series gives |sinh z|≤(1/4)/(1-1/16)=4/15<1/3.
Consequently |(1+k²)sinh² z|≤13/36, so the radicand is in the open
right half-plane and has modulus at least 23/36. The density is
holomorphic on a neighbourhood of the disk, and its modulus is
at most 9/sqrt(23)<2. Its primitive F_k vanishing at zero exists
on a disk containing this closed disk; radial integration gives
|F_k(z)|≤2|z|≤1/2. Since |cosh z|<2 and |cos(F_k(z))|<2
(by the absolute power series, bounded by geometric series),
|D_k(z)|≤5 uniformly. The density is even, its primitive odd, and
D_k is even with D_k(0)=0.

The cubic jet of F_k is k z - k(1+k²)z³/6; the even fourth-order
jet of D_k is J_k(z)=(1-k²)z²/2+(1-2k²+5k⁴)z⁴/24.
Cauchy's coefficient bound is |a_(2n)|≤5*4^(2n).
For real |u|≤1/8,
|D_k(u)-J_k(u)|≤5*4^6*|u|^6/(1-16u²)≤(81920/3)*|u|^6.

In particular k=1 yields the required self-dual expansion.
Set eps>0, k²=1-80 lambda eps², |lambda|≤L, |v|≤V,
80 L eps²≤3/4, eps V≤1/8, eps≤1, and take the nonnegative k.
Then k²∈[1/4,7/4], so k∈[1/2,3/2]. Apply the already merged
QuarticUniformTransfer20261127.scaled_error_uniform_box
with C=81920/3:
|3 D_k(eps v)/(20 eps^4)-(v^4/40+6 lambda v²)|
 ≤ eps²*(4096 V^6+4 L V^4+200 L² V^4).
Taking eps=M^(-1/4) proves the claimed locally uniform limit,
with effective O(M^(-1/2)) error on every bounded box.

## Lean checkpoint

The new module defines the concrete real density, phase, crease.
It proves candidate real prerequisites (reciprocal-square-root
second-order estimate, continuity, nonnegative bounded density,
and pointwise density quadratic error given elementary sinh bounds).
This is a possible alternative route to the Cauchy proof, via
interval integration and real Taylor estimates; it is not a
certificate of the full analytic proof. Remaining kernel obligations:
establish the sinh estimates, integrate the density error, obtain
the cosine and hyperbolic cosine remainder bounds and combine them,
identify the reparameterized phase with the original orbit integral,
then instantiate #670 without a remainder hypothesis.
No existing certified files or manuscript statements are modified.
