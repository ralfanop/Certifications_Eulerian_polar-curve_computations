# M15 Lipschitz Extensions — 16 November 2026
Authoritative ZIP Manuscript_15_Lipschitz_Extensions_20261116(1).zip
SHA-256 245496a6fe9ad5ba20156c726d4b334451667c90c54078073c3a46bde651e64b
Library libfile_ea19eee716fc8191914a161f7a5c76c2
Direct diff 15.tex against Lipschitz Sources archive shows insertion of a 266-line temporary block after Figure 2. Existing obligations, including #334, remain in force. No manuscript/figure edits.

| LaTeX label | Current Lean candidates | Work remaining |
|---|---|---|
| thm:cusp-metric-exponent | polynomial power inequality (equivalent to the Jensen bound), cubed cross-branch estimate conditional on stated distance bounds | finite variance C² characteristic-function proof and derivative asymptotics; actual arc and intrinsic length; same-branch estimate; limiting coefficient and optimality via asymptotic powers |
| thm:reconstruction-inverse-no-holder | exact grid spacing, support separation, Pascal interior vertex identity and signed binomial polynomial for arbitrary N | construct actual probability measures/coupling, endpoints and mass, prove W1 equality, exact characteristic-function difference, superalgebraic decay, compactness and restricted Fourier uniqueness |
| prop:directed-transport-rigidity | pointwise identity, actual marginal integral equality, actual primal infimum equality, same-mean proportionality | symmetry from already developed W1 symmetry, audit CI |
| prop:dirichlet-product-channel | domain-aware conditional resolvent bridge given intertwining, inverse maps, and left inverse | construct actual closed Dirichlet forms, domains, tensor product isometry and reducing subspace, spectral sums, trace-class shifted channel; reuse interval determinant theorem where exact scope permits |

Numerics: exponents and rational coefficients documented exactly. The irrational universal cross-branch coefficient and normalized examples, including finite alternating Fourier differences and one shifted-channel determinant value, individually assert 3,400,000 relative bits at 3,600,000 working bits and 1,000,001 significant digits via strict exact dyadic endpoint inclusion. Exact finite normalized coupling examples N=2,4,...,64 use rational mass, marginals, cost and separation. They do not establish all-N analytic or operator theorems. Artifacts include exact endpoints, rounded digits and balls; pending exact-HEAD CI. 
Do not modify M11–14, V007/V097, figures or manuscript sources. No merge.
