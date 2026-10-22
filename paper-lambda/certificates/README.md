# Quarter certificate for 14.35

`chi3-quarter-1435.json` is the exact rational witness: 400 real atoms and 600 conjugate pairs, or 1600 physical atoms. Coordinates have denominator 2^24; each listed nonreal mass is repeated at its conjugate. The mass denominator is 2^32, total mass is one, and every point has modulus at most 16.

The sorted physical list is `CatalanCore/Cert/SigmaQuarter/Data.lean`, with coordinates rescaled to 2^40. Potential, energy, geometry and witness checks use `decide +kernel`. `chi3-quarter-1435-budget.json` records the exact ledger. The finite log-table energy allowance is slightly larger than the exploratory Arb bound; its stronger segment bound keeps the target at 14.35.

The geometry, smoothing radius 1/2048, sixteen-strip arithmetic price and characteristic-zero selector are unchanged. The witness adds positive real support and reallocates ray nodes. The public theorem is `CatalanHybridChallenge.chi3_hybrid_measure_1435`.

Run `python scripts/check-chi3-quarter-certificate.py` from the repository root to check the frozen input against the Lean data, rational budget, statement and paper sources. The Lean build checks the mathematical certificate.
