# Certificate generator for the second energy dual

These scripts produce `CatalanMeasure/Dual/*.lean` (the data and kernel checks of
Proposition 5.6 of the paper) from the trial sequences in `k40t99_trial.json`.

    python3 gen_dual.py k40t99_trial.json ../../CatalanMeasure/Dual Dual module

They need Python 3 with NumPy. `polyq.py` mirrors the computable polynomial operations of
`CatalanMeasure/Cert/ListPoly.lean` exactly, so that every check the generator plans passes in
Lean; `isolate.py` isolates the roots of the derivative numerators; `fields.py` builds the
derivative fractions and evaluates the fields in floating point to choose the bounds.

The trial sequences themselves were found by numerical optimization of the dual value
(a cutting-plane method over sequences of the form `c_k + Re Σ r_j z_j^k`); only the final
rounded sequences are needed to reproduce the certificate.
