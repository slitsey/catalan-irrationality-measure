# Phase 0: explicit-primitive corner pilot

27 October 2026. Baseline: release commit 5e09e6f, approved by Sean for the new codex/uniform-lean branch. The release checkout was read only.

## Result

`CatalanCore.Uniform.Decay.PilotCorner` compiled successfully. Its own completion line is **Build completed successfully (2752 jobs).** This is a targeted module build with cached imports, not a whole-tree build. No retired atomic certificate tree was built.

New source: `CatalanCore/Uniform/Decay/PilotCorner.lean`.

The namespace is `CatalanCore.Uniform.Decay.PilotCorner`. Main declarations:

- `primitive_eq_radial`: the explicitly defined segment-integral primitive equals `(z-a) * integral_0^1 f(lineMap a z t)`.
- `primitive_hasDerivWithinAt`: this explicit primitive has derivative `f` on any convex domain where `f` is complex differentiable.
- `corner_add`: two finite segments through an interior corner have the same integral as the radial primitive between their endpoints.
- `shifted_sin_ne_zero` and `shiftedCot_differentiableAt`: arbitrary real-shift cotangent factors are holomorphic on the open upper half-plane.
- `chi3Source_differentiableOn`: the actual chi3 source integrand `-pi * (cot(pi(z+1/3))/18 - cot(pi(z+1/2))/12 + cot(pi(z+1))/36) / ((z-a)(z-b))` is holomorphic there for arbitrary natural row and column nodes, including `a=b`.
- `chi3_corner`: the selected chi3 polygon's interior corner `p1 -> p2 -> p3` can be removed for every such source integrand.

Vertices are reconstructed over the rationals from the saved decimal **height and lean strings** in scope-screen-2026-10-27/selected-candidates.json. They are not the separately rounded floating x-coordinates. There is no numerical analytic premise.

`#print axioms` for `primitive_hasDerivWithinAt` and `chi3_corner` reports exactly `propext`, `Classical.choice`, `Quot.sound`. No extra axiom, sorry or native_decide occurs in the accepted source.

## Reuse decision and precise scope

Reuse Mathlib's `Convex.hasFDerivWithinAt_curveIntegral_segment_of_hasFDerivWithinAt_symmetric` and its finite-segment addition theorem. The primitive is an explicit radial integral; no choice of an unknown primitive is supplied as a hypothesis. Mathlib's generic proof internally uses closed-form Poincare/homotopy machinery, so this is library reuse rather than a new differentiation-under-integral proof. This is an S10 simplification, not a new polygon Cauchy theorem developed in the project.

The pilot proves a genuine **strictly upper interior corner**, not the entire polygon deformation. It does not yet prove the pole-free disk/gluing bridge at the real initial endpoint, physical shifted/scaled path identification, improper connector decay, cotangent separation, or source-entry representation. Those remain Package D-Polygon obligations. Keep its 2500-5500 line estimate pending those constructions; a small interior-corner pilot is not evidence that the full analytic package is a thin wrapper.

## Measurements

Every build and preflight used `scripts/uniform-phase0/run_guarded.py`, which calls `work/tools/guard-proof-safe.ps1` with a 4 GiB reservation. One build ran at a time. Each listed dependency had its own `lake build <target> --no-build` preflight confirming that only that dependency was stale before its build.

Accepted pilot log: `phase0/logs/CatalanCore_Uniform_Decay_PilotCorner-build-20261027-123740.log`; matching JSON has the same stem.

| Quantity | Accepted pilot |
|---|---:|
| Lake module time | 10 s |
| Wrapper wall, including guard/Lake | 17.2593176 s |
| Synchronous cumulative profiler `type checking` | 196 ms |
| Observed Lean process peak working set | 1,700,171,776 bytes (about 1.583 GiB) |
| Sampled whole wrapper-tree peak | 2,326,147,072 bytes (about 2.167 GiB) |

`Elab.async` is false and `profiler.threshold` is zero. The 196 ms is Lean's cumulative reported type-checking category, not wall time or a cost for the import closure. The wrapper-tree measurement includes PowerShell/guard/Lake and must not be interpreted as private Lean RAM.

Targeted newly built Mathlib dependencies (their own success lines are in corresponding phase0/logs files):

| Module suffix | Module time | Observed Lean peak bytes |
|---|---:|---:|
| Analysis.Analytic.IteratedFDeriv | 56 s | 919,781,376 |
| Analysis.Calculus.AddTorsor.AffineMap | 7.0 s | 850,124,800 |
| Topology.Homotopy.Affine | 7.6 s | 712,409,088 |
| Analysis.Calculus.FDeriv.Symmetric | 12 s | 963,203,072 |
| MeasureTheory.Integral.CurveIntegral.Basic | 19 s | 1,074,356,224 |
| MeasureTheory.Integral.CurveIntegral.Poincare | 14 s | 1,097,003,008 |

Mathlib.Algebra.Order.Field.Pointwise was built by the parent before this lane acquired the build slot; its separate log supplies that measurement.

The first pilot compile failed on two unresolved polymorphic `smul_comm` calls and one misqualified convexity lemma. The repaired second compile passed. First failed log: `phase0/logs/CatalanCore_Uniform_Decay_PilotCorner-build.log` (136 s module, 142.414972 s wrapper, 1,693,704,192-byte Lean peak). It contained error-recovery sorryAx placeholders and is **not accepted evidence**. The accepted log's axiom output has none. The large first/second wall difference is not a claimed proof speedup: cold-import/I/O and source changes both intervene.

## Independent finite-input mirror

`scripts/uniform/corner_mirror.py` independently reconstructs all three vertices using Python `fractions.Fraction`, checks strict positive height and negative real part, distinct vertices, exact edge leans, and the exact chi3 balance `1/18 - 1/12 + 1/36 = 0`. It ran successfully under guard-proof-safe.ps1 with a 1 GiB Python reservation and printed `PASS exact finite geometry only`.

The mirror is input checking, not a substitute for the Lean analytic proof. The exact real coordinates it printed are:

- p1: -49079510722935975351197303919549/400000000000000000000000000000000
- p2: -32564914687557617332077176733567/200000000000000000000000000000000
- p3: -201365480153877831208135506929503/1000000000000000000000000000000000

## Engineering implication

No numeric block tuning is needed for this analytic corner proof. Use one declaration per finite structural step and reuse the generic convex primitive API. This pilot validates the interior-corner method and import closure; it provides no measured cost for the real endpoint or improper connector.
