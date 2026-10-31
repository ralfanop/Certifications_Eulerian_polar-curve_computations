D_K CERTIFICATION SUPPLEMENT FOR V423
====================================

D_kappa = 0.203783759536049443826081 is correctly rounded to 24 decimal places.
The numerical value, quantity and certified interval bounds are unchanged.
The updated four-page note now identifies manuscript V423.

Both full-arc arclength parametrisations start at theta=-pi and follow increasing
theta. This scalar diagnostic excludes the Eulerian corner's concentrated turning.

CONTENTS
D_K_CERTIFICATION_NOTE.pdf/.tex: mathematical error argument and result.
D_K_CERTIFICATE_32_64.json: principal rigorous interval certificate.
D_K_CERTIFICATE_40_128.json: finer enclosure, contained in the principal interval.
certify_dk.py: unchanged rigorous program; core dependency python-flint==0.9.0.
verify_certificate.py: exact standard-library checker for the delivered records.
reference_direct.py and DIRECT_REFERENCE_CHECK.json: independent numerical check.
V423_INPUT_IDENTITY.json: hashes of the V423 sources and immutable input records.
VERIFICATION.json and MANIFEST_SHA256.txt: current delivery records.

REPRODUCTION
Install requirements.txt in an appropriate Python environment, then run:
  python3 certify_dk.py --order 32 --panels 64 --output D_K_CERTIFICATE_32_64.json
  python3 certify_dk.py --bits 320 --order 40 --panels 128 --output D_K_CERTIFICATE_40_128.json
  python3 verify_certificate.py

The original runs used Python 3.12.14 and python-flint 0.9.0. The optional direct
Gauss-Legendre comparison uses mpmath 1.4.1. The rigorous program fails if domain,
positivity or rounding conditions fail; its checks remain active under python -O.
The record checker checks rounding, nesting, program identity and the independent
comparison. It does not replace the proof of enclosure in the note.

This V423 revision reuses both certified interval records and the executable byte
for byte. The mathematical quantity is unchanged; no expensive recomputation was
necessary. The certificate checker was rerun successfully. All earlier proposal
wording and V422 identities are preserved under PROVENANCE/V422_DELIVERY_RECORDS/
in the parent manuscript package. The relevant accuracy wording is now integrated
into Sections 2 and 3.8 of V423.

Build the note with Tectonic or twice with pdfLaTeX; the package-root build.py
builds both manuscript editions and this note. This is a certificate based on
explicit mathematical error bounds and Arb arithmetic, not proof-assistant
formalisation or certification of the entire manuscript.
