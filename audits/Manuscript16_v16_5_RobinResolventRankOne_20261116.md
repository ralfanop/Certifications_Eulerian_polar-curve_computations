# M16 v16.5 §14.2 — Robin resolvent rank-one audit (analytic, NOT Lean certified)

Authoritative ZIP: `4bde685f7a340e45c43f413aea973db50feea7ba30023f84aefa5de042499c0e`.
Source: Proposition 14.2, equations (147)–(149) in author-approved `16.tex` (verify labels before cross-referencing). No manuscript source changed.

Let `c=|κ|²`, `β>0`, and `H_R=-d²/dz²+c` on `L²(0,∞)` with `u'(0)=-βu(0)`; let `H_D` be its Dirichlet counterpart. For real `t<c-β²`, define `a=√(c-t)>β`. The resolvent kernels are

`G_D(z,z';t)=[exp(-a|z-z'|)-exp(-a(z+z'))]/(2a)`,

`G_R(z,z';t)=[exp(-a|z-z'|)+((a+β)/(a-β))exp(-a(z+z'))]/(2a)`.

Consequently the **exact resolvent difference** is

`(H_R-tI)^(-1)-(H_D-tI)^(-1) = (1/(a-β)) |v_a⟩⟨v_a|`, where `v_a(z)=exp(-az)`.

In particular it is positive rank one and trace class, with

`Tr[(H_R-tI)^(-1)-(H_D-tI)^(-1)] = 1/[2a(a-β)]`.

Proof: both kernels solve `(-∂²+a²)G=δ` with derivative jump `-1`; the first vanishes at the boundary and the second obeys `∂_zG_R(0,z')=-βG_R(0,z')`. Subtraction cancels the free term and yields the separated kernel. Finally `∫₀∞ exp(-2az)dz=1/(2a)`. Since `a>β`, the coefficient is positive.

The Robin resolvent has a simple pole at `a=β`, corresponding to `t=c-β²`. The normalized eigenfunction is `√(2β)exp(-βz)`. The pole residue in the **spectral parameter** `t` equals minus the eigenprojection, consistently with `(H-tI)^(-1)`.

**Lean proof obligations (open):** half-line Sobolev trace and selfadjoint Robin domain; Green-kernel distributional jump; boundedness of resolvent operators; rank-one operator identity; trace formula; essential-spectrum preservation. The elementary scalar identity `((a+β)/(a-β)+1)/(2a)=1/(a-β)` is a separate algebraic Lean target. Avoid treating this scalar identity as the full operator theorem.

**Arb:** none required for the exact symbolic identities. No numerical certificate, no `ctx.prec=3600000` claim, no million-digit claim.

**Status:** independent analytic derivation checked symbolically; Lean **NOT RUN**; CI **NOT RUN**; axiom audit **NOT RUN**. No merge. Distinct from PR #339 (Maxwell resonance generating function).
