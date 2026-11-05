# Manuscript 14.1 — §§6–7 operator formalization: scope and dependency audit

**Manuscript source:** `Manuscript_14_v14.1_Cor3.6_Lean4_Arb_CERTIFIED(3).zip`, `Manuscript_14_v14.1/14.1.tex`, §§6–7.  
**GitHub branch:** `manuscript14-v141-gram-resolvent-20261104`, based on the isolated corrected Corollary 3.6 branch.  
**No merge** into main, V007, V097, manuscript 13, or the independent Section 11 workstream.

## Exact §6 mathematical statement

At `a = 1/sqrt(8)`, on `H=L²([-1,1], du/2;ℂ)`:
`(Sf)(u) = (1/2)∫[-1,1] exp(a*u*v) f(v) dv`.
Let `D P_n=n(n+1)P_n` be the nonnegative selfadjoint Legendre/Gegenbauer realization with the manuscript's **spectral domain**
`Dom(D)={Σf_nP_n: Σ n²(n+1)² |f_n|² < ∞}`.
Let `A_a=D-a²M_(u²)` on the same domain.

The **printed theorem** asserts: `S` is positive selfadjoint trace-class;
`S(H)⊂Dom(A_a)` and `A_a S f=S A_a f` for every `f∈Dom(A_a)`;
`(S1)(±1)=r_E(i/sqrt2)`;
`Tr(S)=(1/2)∫[-1,1]exp(a*u²)du={}_1F_1(1/2;3/2;a)`.
The manuscript expressly distinguishes this operator from the Dirichlet spectral determinant.

**Kernel algebra / boundary flux module**:
`lean/SpecialImaginaryPoint/GramKernelBispectral.lean`.
For arbitrary complex a,u,v it asserts the exact identity
`[-(1-u²)(a*v)²+2*u*(a*v)-a²*u²] e^(a*u*v)`
equals the u↔v expression; plus endpoint flux cancellation at ±1.
This algebra is already explicitly known from manuscript 13 and is
**not** by itself the novel domain-level theorem.

**Still needed for FULL §6 kernel verification**:
1. Identify the exact Hilbert-space normalization and construct actual bounded integral `S`.
2. Prove its positive, selfadjoint and trace-class properties in the same Lean operator type; re-use manuscript 13 only if matching theorem and parameters are already kernel-certified.
3. Define the spectral unbounded `D` and `A_a`, and prove polynomials form a graph core for `A_a`.
4. Prove both differentiated kernel identities and their Green integration-by-parts boundary identities on that core.
5. Pass to all of `Dom(A_a)` via the closed graph and boundedness of `S`; establish domain preservation, not merely an equality of formal differential expressions.
6. Prove endpoint evaluation separately. Arb cannot verify universal domain claims.

## Exact §7 statements and numerical checks

Let `A_D=-∂²` be the auxiliary positive Dirichlet Laplacian
on `H²(0,1)∩H¹₀(0,1)` with eigenvalues `π² n²` (n≥1).
Printed results include the Fredholm/zeta determinant ratio
`det_F(I+x² A_D^(-1))=sinh(x)/x`; the logarithmic derivative identity
`Langevin(x)=2x Tr((A_D+x²I)^(-1))`;
and the square-resolvent trace identity.

For `a²=1/8`, **independent exact-rational formulas**:
`c_m=ζ(2m)/π^(2m)=(-1)^(m+1)*2^(2m-1)B_(2m)/(2m)!`.
`Tr(R_a)=Σ_{k≥0}(-1)^k c_(k+1)/8^k`;
`Tr(R_a²)=Σ_{k≥0}(-1)^k (k+1)c_(k+2)/8^k`.
Using `π²>9`, `ζ(2m)<2` and
`r=1/72`, at K=34 a rational remainder majorant is:
`E1=(2/9)*r^34/(1-r)<10^(-60)`;
`E2=(2/81)*r^34*((35)/(1-r)+r/(1-r)^2)<10^(-60)`.
The scalar Arb script verifies the manuscript's 50/51-digit quoted
trace values, the Eulerian endpoint via positive Taylor fractions,
and that the **Gram diagonal trace is not equal** to the Eulerian value.

**Still needed for FULL §7 Lean certification**:
1. Concrete Dirichlet operator `A_D` with the stated Sobolev domain and certified spectrum.
2. Rigorous identification of the resolvent traces with these convergent spectral sums.
3. Trace-class inverse and Fredholm determinant as an operator-valued expression.
4. Infinite Euler product, differentiation with locally uniform convergence.
5. The zeta-regularized determinant ratio with its normalization.
6. Bounded perturbation / resolvent square norm on the exact Hilbert space.

**Crucial:** numerical scalar checks are not formal proofs of operator statements. The present new files must be separately CI-checked; do not claim a theorem certified before the corresponding run succeeds.
