# scripts-hybrid: reproducing the hybrid (mu(lambda) <= 46.45) numerical certificate

These files accompany Part 1 ("The rectangular hybrid frame and mu(lambda) <= 46.45") of `lambda-irrationality.tex`.
They are copies of the audited originals in `DX-hybrid-decay/` (and `orig/` for the control), with ONE change:
the hard-coded `sys.path.insert(0, '.../work/pylibs')` line of `hcert.py` is replaced by an optional
`PYLIBS` environment variable.

## Files
- `hcert.py`          Arb (python-flint) certificate for the hybrid k_rho energy step. Computes m', S_cert, g_min, I_rho(sigma), I(nu_alpha) and
                      D_F = 2((1+a)m' + S_cert) - (1+a)^2 I_rho(sigma) + I(nu_a),  c_hyb = 2(m' - g_min).
- `sig_h500.json`     certificate measure that maximises D_F  (D_F >= 3.906269506610, c_hyb <= 7.654064744147).
- `sig_h500w.json`    second measure (maximises D - 0.04 c): D_F >= 3.9045139, c <= 7.5928685 (gives the worse exponent 46.468).
- `sigma300.json`     the plain (alpha = 0) certificate measure of the square frame: negative control.
- `expected_h500.log`, `expected_ctl0.log`   expected output of the two runs below (EF audit rerun for the control).
- `member2_content.py`  exact check (python-flint, gmpy2) of the content saving v_p(den_F) = tau_p - m at clean primes for the member with the
                      extra common node (C u {r+2m}); needs `chk_lib.py` (in this directory).

## Requirements
Python 3 with `python-flint` (Arb), `numpy`, (and `gmpy2` for `member2_content.py`). If they live in a non-standard directory, set
`PYLIBS=/path/to/dir` before running.

## Commands
```
python hcert.py sig_h500.json 1/8 2.2185 -1.6090 h500 14000 512     # hybrid: D_F, c_hyb      (~30 s)
python hcert.py sigma300.json 0 1.97180 -1.46410 ctl0 14000           # control alpha = 0: D >= 3.111379042, c <= 6.871799888
```
Arguments: measure file, alpha, target for m', target for g_min, output tag, number of segment cells, [number of cells on [1,1+2 alpha]].
The targets must lie *below* the float plateau minimum, otherwise adaptive splitting does not terminate.
Output files `hcells_<tag>.json` (the covers) are written to the current directory.

## Expected output (last lines of expected_h500.log)
```
I_rho(sigma) [2.0054859746906528728114023 +/- 6.20e-26]
tail lower [13.59541598085213377695378212 +/- 2.57e-27]
I(nu) [1.702445751143275337388293457 +/- 1.89e-28]  D_F cert >= [3.906269506610271171047664124 +/- 1.80e-29]  c_cert <= [7.654064744147045740163548544 +/- 6.72e-29]
```

## Status
The original `hcert.py` was re-run by an independent audit agent (EF) with identical output. The copy in this directory (with the `PYLIBS` change)
has since been re-run (Python 3.13 with python-flint and numpy from `PYLIBS`): identical final lines, D_F >= 3.906269506610271,
c <= 7.654064744147046, about 8 s.
Note: `member2_content.py`, `check_hE.py` (via `chk_lib.py`) need `gmpy2`; the gmpy2 build in work/pylibs is for CPython 3.12, so run them with a
Python 3.12 (e.g. miniforge 3.12.9) and `PYLIBS` set. `chk_lib.py` is in this directory (no sys.path edit needed).

## Exact checks added for Part 1 (python-flint / gmpy2 via `chk_lib.py`; set `PYLIBS` if needed)
- `check_hE.py`  : Lemma E (Theorem hE) in the Gauss valuation with formal X, for admissible (r,m,e), e in {0,1}, all primes meeting the hypotheses:
                   27 primes, 0 failures (`check_hE.expected.log`; several are equalities).
- `member2_content.py r` : v_p(den_F) = tau_p - m at clean primes for the extra-node member.
- `check_k.py`   : product formula k_{R,L}(theta) = const * prod (theta+c)^{e_c} (exact, 5 values of theta) for (K,m) in {(3,0),(3,1),(4,1),(4,2),(5,0),(5,2),(6,3)}.
- `sum_ec.py`    : sum_c e_c = D for K <= 200 and agreement of e_c with the min-formula for K < 80.
- `check_hE_member2.py r,m,e ...` : independent exact check (python-flint only) of the bounds of Theorem hE for both members and
                   m in {r/8-1, r/8, r/8+1}: 27 cases at r = 48, 64, 80, slack 0 in every case, 0 failures.
- `check_hB.py`  : the per-level bound B(q) <= r f_j(q/r; m/r) (C_0 = 0) for all odd q, 21 pairs (r,m), 97 <= r <= 10007: max excess 0.
- `bsum.py`      : sum over primes of the dual-certificate bound B(p) log p / r^2 (3.6497, 3.7227, 3.7418, 3.7458 at r = 1e3, 1e4, 1e5, 4e5 -> Lambda_trop = 3.7499).
