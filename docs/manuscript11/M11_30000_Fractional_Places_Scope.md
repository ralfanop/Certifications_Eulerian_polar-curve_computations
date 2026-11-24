# Manuscript 11, Eq. (50): exact 30,000 digits AFTER the decimal point

## Provenance and currently established results

* The complete Eulerian length `L_E` originates in independent 32-panel
  FLINT/Arb computation run **44359739062**, HEAD
  `6ddb354a85832bf5b35538996d7d619c63ac9a16`, with
  **100,031 reported relative bits**. The later SUCCESS run **45179196734**
  reaudited **20,000 fractional places**, but did NOT recompute the length.
  The original 100k combined manifest SHA256 is
  `a606d305f7d4c773695cee61cf56268022ec9cc5525f689f301e8822f22fe7b5`.
* New workflow `m11-30000-length-reaudit.yml` retrieves the original
  33 artifacts, exactly recombines all 32 rational panel intervals,
  verifies the original combined interval, reconstructs an enclosing Arb
  ball at **110,000 working bits**, requires at least **99,800 measured
  relative bits**, and proves that BOTH exact endpoints lie STRICTLY in
  ONE nearest-even rounding cell at **30,000 fractional places**.
  No arclength integration is repeated. The 30k claim is PENDING until
  this workflow has a successful exact-HEAD CI with preserved output.
* The original `D_kappa` 30k-bit half-integral CI 45157228615
  and later 12k-bit/checkpoint pilots are **not** 30k-decimal proofs.
  The successor 20k-decimal Draft PR #546 has two failed `push`
  runs, 45238560102 and 45239183594, both with **zero jobs**.
  Its embedded unindented Python heredocs make the YAML invalid;
  no costly 70k-bit integrations were carried out by those runs.

## Essential constraint for D_kappa at 30,000 decimal places

30,000 fractional places require roughly 99,658 binary digits of
resolution, plus proof margin. We adopt at least **100,100 measured
relative bits** and a strict exact-rational rounding cell; neither
a high `ctx.prec` nor a green smoke/Lean CI establishes this.

The *current* method in `m11_dk_adaptive_radius.py` constructs the
Eulerian inverse-ODE chart using a full-length interval with precision
at least `target + maxorder + 768` relative bits (see
`Local.build_chart` and `Local.order_for`). For target >=100,100 and
128 panels, this is on the order of **122,000+ length bits** (depending
on audited local inverse radii). Thus the historical 100,031-bit
length interval, although adequate to round `L_E` to 30,000 places,
is NOT a sufficient ODE chart input for the existing implementation.

Therefore the next sound stage is EITHER:

1. Obtain a genuinely new **at least 125,000-relative-bit** complete
   Eulerian length enclosure for the curvature ODE, while reusing all
   earlier independent panel evidence where mathematically compatible,
   with bounded-memory distributed higher-precision calculations only
   where indispensable; or
2. Derive and rigorously check a tighter interval propagation theorem
   for the nonlinear inverse-ODE jet which *proves* 100,031 historical
   length bits suffice without the current conservative guard.

Do not merely increase `--bits` in the curvature workflow to
150,000 and continue to pass the original historical length: its
`Local.build_chart` correctly fails the required-accuracy check.
Do not claim 30,000 decimals for curvature based on a 12k/30k-bit pilot.

## Production and acceptance

Once one of the two length-input stages is fully certified, produce
both independent curvature halves using rigorously outward Cauchy/Taylor
enclosures with exact restart checkpoints; keep SHA256 manifests of
all partial intervals and ODE parameters, and the source length
certificate. Start with 128 panels and approximately 150,000 operating
bits, raising either only when required by measured bounds or runtime.
The final strict acceptance program
`m11_30000_curvature_final_verify.py` requires:

* an independently verified high-precision full-length source;
* both separate complete half-integral manifests and their exact match
  to the two halves in the combined manifest;
* at least 100,100 **measured** Arb relative bits for `D_kappa`;
* exact rational square containment, agreement with all 24 printed
  Eq. (50) decimals, and both rational `D_kappa` endpoints strictly
  inside the same exact 30,000-place decimal rounding cell.

A successful test, syntax check, or preliminary CI is NOT a certificate.
Do not merge the PR or modify author manuscripts, graphics, or Lean 4.
