HSTAR 80-DECIMAL CERTIFICATION

Files:
- certify_hstar_80.py: constructs a finite Arb certificate for the 80-decimal rounding cell.
- verify_hstar_80.py: replays the generated JSON certificate using Arb only.
- CERTIFICATION_RUN_OUTPUT.txt: terminal output from the successful user-run certification on Intel macOS x86_64.

Validated environment:
- Python 3.13.15
- python-flint 0.9.0
- mpmath 1.4.1 (used only to choose witness values in the constructor)
- Arb precision: 768 bits

The successful run generated HSTAR_80_CERTIFICATE.json (about 1.1 MB) and the Arb-only verifier passed all 2589 panels. The generated JSON should be retained with the public computational record because it contains the complete dyadic cover and boundary witnesses needed for an exact replay.
