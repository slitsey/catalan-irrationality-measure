# Certificate scripts for the λ paper

- `arb/kcert.py` and `arb/sigma300.json`: the Arb (python-flint) certificate for the k_ρ energy step (D⁺ ≥ 3.11138, c ≤ 6.87180). Run: `python -I kcert.py sigma300.json 1.97180 -1.46410 K300 14000`. Requires python-flint (and mpmath) on `sys.path` (default `./pylibs`).
- `lean-cert/`: generators for the kernel-checked Lean certificate in `CatalanLambda/Cert/`, and exact-integer mirrors of the Lean definitions (`mirror*.py`). Paths are relative to the repository root.

The Lean certificate (`CatalanLambda.Cert.certFacts`) does not depend on these scripts. They document how its data were produced.
