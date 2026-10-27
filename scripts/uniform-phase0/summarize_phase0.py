"""Assemble accepted build evidence, excluding replayed dependency profiling."""
import json,re
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'phase0'; LOGS=OUT/'logs'
targets=['CatalanCore.Uniform.Decay.PilotCorner','CatalanMeasure.GenD.Uniform.PilotRank',
    'CatalanCore.Uniform.Decay.PilotArithmetic','CatalanCore.Uniform.Decay.PilotPotential',
    'CatalanCore.Uniform.Decay.PilotRemainder','CatalanCore.Uniform.Decay.PilotEnergy',
    'CatalanCore.Uniform.Decay.PilotAudit']
accepted=[]
for target in targets:
    candidates=[]
    for file in LOGS.glob(target.replace('.','_')+'-build*.json'):
        data=json.loads(file.read_text())
        log=Path(data.get('log',str(file.with_suffix('.log'))))
        text=log.read_text(encoding='utf-8')
        if data['rc']==0 and 'Build completed successfully' in text:
            candidates.append((file.stat().st_mtime,file,data,text))
    assert candidates, 'No accepted build for '+target
    _,file,data,text=max(candidates)
    # Lake replays old profiler messages; use only the freshly Built target's part.
    marker=re.search(r'Built '+re.escape(target)+r' \(([^)]+)\)',text)
    assert marker, 'No own Built line for '+target
    own=text[marker.end():]
    totals=re.findall(r'\n\ttype checking ([0-9.]+)(ms|s|µs)',own)
    kernel=None
    if totals:
        value,unit=totals[-1]; kernel=float(value)*{'s':1,'ms':.001,'µs':.000001}[unit]
    record=dict(target=target,module_wall=marker[1],kernel_typechecking_seconds=kernel,
        wrapper_wall_seconds=data['wrapper_wall_seconds'],
        lean_peak_bytes=max(map(int,data['lean_process_peak_working_sets_bytes'].values()),default=0),
        sampled_wrapper_tree_peak_bytes=data['sampled_wrapper_tree_peak_bytes'],
        log=str(file.with_suffix('.log').relative_to(ROOT)))
    accepted.append(record)
failures=[]
for file in LOGS.glob('*-build*.json'):
    data=json.loads(file.read_text())
    if data['rc']:
        failures.append(dict(target=data['target'],rc=data['rc'],file=str(file.relative_to(ROOT))))
leanfiles=sorted((ROOT/'CatalanCore/Uniform').rglob('*.lean'))+sorted((ROOT/'CatalanMeasure/GenD/Uniform').rglob('*.lean'))
lines={str(p.relative_to(ROOT)):len(p.read_text(encoding='utf-8').splitlines()) for p in leanfiles}
data=dict(accepted=accepted,failed_build_attempts=failures,lean_source_lines=lines,
    measurement_note='Synchronous profiler totals for own freshly built module only; cached replay excluded. Lean OS peak working set is separate from sampled wrapper/guard/Lake tree RSS. Warm copied imports; not cold replacements.')
(OUT/'METRICS.json').write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8')
table=['| Pilot | Own module wall | Synchronous kernel type checking | Lean peak GiB |',
       '|---|---:|---:|---:|']
for r in accepted:
    kernel='not profiled' if r['kernel_typechecking_seconds'] is None else f"{r['kernel_typechecking_seconds']:.4g} s"
    table.append(f"| `{r['target'].split('.')[-1]}` | {r['module_wall']} | {kernel} | {r['lean_peak_bytes']/2**30:.3f} |")
report='''# Phase 0 report — audits and pilots

27 October 2026. Phase 0 complete; stop before Phase 1 for Sean's review.
Branch `codex/uniform-lean`, worktree `work/catalan-uniform`, approved baseline
`5e09e6f`. The local commit is reported in the final handoff message and the
external copy of this report; this committed report cannot contain its own hash.

## Result and proved declarations

- `CatalanCore/Uniform/Decay/PilotCorner.lean`: `primitive_eq_radial`,
  `primitive_hasDerivWithinAt`, `corner_add`, `shifted_sin_ne_zero`,
  `shiftedCot_differentiableAt`, `chi3Source_differentiableOn`, `chi3_corner`.
  This proves the explicit radial primitive method at the selected interior
  chi3 corner for all natural row/column nodes, including the diagonal.
- `CatalanMeasure/GenD/Uniform/PilotRank.lean`: `rank_le_of_factorization`,
  `basis_check`, `basis_rank`, `factor0`–`factor9`, `image_rank0`–`image_rank9`,
  `euler_arithmetic`, `certificate_pack`. Real D58-L0203/right, x=26: dimension20,
  basis rank3, ten image bounds [1,0,0,2,1,0,2,2,1,0], weighted sum77 and Euler1.
- `PilotArithmetic.lean`: signed fixed-point evaluator and exact shared-table
  cons lemma. `PilotPotential.lean`: 466 individual input checks, table assembly,
  and eight `PotentialN_rows`/`PotentialN_check` arithmetic equalities.
- `PilotRemainder.lean`: `remainder_arithmetic`, the 698-term rational L1
  order8 tail workload. `PilotEnergy.lean`: 18 shared input checks and
  `Energy0_check`/`Energy1_check`, respectively a negative-density-piece
  self-energy and its mutual interaction with a positive piece.
- `PilotAudit.lean`: combined internal pilot import/axiom audit. All inspected
  proofs use at most propext, Classical.choice and Quot.sound. No sorry,
  native_decide or additional axiom was introduced.

The rational rank packet does not prove prefix transport, finite-characteristic
exception transfer or source-cover membership. The spline equalities are
arithmetic workloads, not analytic enclosure soundness or HasDecay. No new bound
is banked. The real-start pole-free disk and improper connector/tail are not
proved by the interior corner. Full theorem domains remain unchanged.

## Accepted measurements

'''+ '\n'.join(table)+'''

Each success is supported by its own `Build completed successfully` line.
`METRICS.json` links every accepted full log and contains wrapper/guard/Lake tree
memory separately. Kernel numbers are synchronous profiler `type checking`
totals for the newly built module only, excluding replayed dependency messages.
They are neither full analytic assembly costs nor a Palomar measurement.
Imports reused copied caches. Module wall and wrapper wall are distinct;
neither is interpreted as kernel CPU time. The audit module has no new
mathematical proof workload and is not separately profiled.

Seven stale Mathlib modules in the corner import closure and the small RawInts
elaborator were built serially after their own guarded preflights. Initial
corner and evaluator source errors were repaired before acceptance; failed
attempts are retained in METRICS.json/logs. No memory kill or timeout occurred.
No full-tree or retired atomic-certificate build ran.

## Reuse audit and revised estimates (C)

- **G Prefix: 4,000–7,000 new lines**, versus 3,000–7,000 in the plan. Reuse
  arbitrary-scale raw digits, physical row/reversal APIs and the generic
  injected-kernel dimension theorem. The all-quotient p-step, full signed tiling,
  Frobenius split, unique graphs, exact guards and coverage remain substantive.
  The N=p and no-carry APIs must not restrict the uniform theorem's domain.
- **Hybrid Next: 2,000–4,000 new lines**, versus 2,000–4,500. Reuse Gauss,
  rank/divisibility, partial two-level and Schur infrastructure. The arbitrary
  pole charts, stable leading kernels, actual elimination and exact M_next
  construction remain new. Quarter-specific regular-pole literals are not a
  generic source theorem. Combine competing same-prime prices by minimum;
  DefHyp.add requires disjoint prime supports.
- **Polygon:** reuse Mathlib's explicit convex segment-integral primitive
  theorem rather than reprove differentiation under the integral. Do not
  shrink the remaining 2,500–5,500-line package on this interior pilot alone.

Detailed statements and assumptions: PREFIX-AUDIT.md, HYBRID-AUDIT.md,
CORNER-PILOT.md, ARCHITECTURE-REVIEW.md and DECISIONS.md.

## Initial block policy

1. One signed potential cell per module; one declaration per Bernstein value.
   Check special-function inputs individually and share their exact literal
   table. This full 114-piece/466-input workload took substantially longer than
   the different old straight-ray sample; no speedup factor or production total
   is inferred. Its eight final row checks dominate current kernel cost.
2. One rank packet per source endpoint/cell; one factorization declaration per
   active map. The D58 packet's rational arithmetic is measurable, so do not
   merge all205 cells into one declaration or infer residue-C3 timing for it.
3. One energy interaction per arithmetic declaration initially. The two small
   interactions do not determine a safe production chunk size. The tested
   short-piece cross interaction has an approximately2.35e-6 interval width at
   scale1e36+39; weight-aware precision or better-conditioned exact formulas are
   required before granting it a production energy budget.
4. The potential microcell halfwidth is1e-7, with all eight jets independently
   checked and a grouped tail upper about4.08e-28. This is a real cell on the
   selected trial, not a completed production cover or an estimate of its size.
   Full log/atan semantics, expression integrity, cell geometry, mass/TV source
   proofs and semantic assembly remain future work. Block policy is provisional
   until those costs are measured.
5. Keep a4GiB reservation for comparable pilot builds initially. The largest
   observed Lean peak was the potential module (~2.13GiB); the wrapper tree
   metric includes guard/Lake overhead. This is not a universal budget for all
   later packages. Continue one heavy build at a time.

## Independent mirrors and controls

The guarded Fraction rank replay independently row-reduces the actual source
maps, verifies each factorization and records source/witness SHA256 hashes.
The guarded signed generator verifies exact mass-one repair and negative density
samples; all eight jet coefficients agree with the independently implemented
Arb jets; direct potential and self/mutual energy implementations agree. The
signed receipt pins selected-candidates.json. The rational corner mirror checks
the exact saved decimal height/lean reconstruction, strict upper vertices and
balanced frame coefficients. Python/Arb checks are not Lean proof premises.
All3757 rational numerator/denominator pairs were reduced; none has both low64
bits zero. Raw integer tapes avoid overloaded literal elaboration.

## Deviations, scope and next gate

Sean approved advancing the freshly created main-based branch to5e09e6f because
main was only the initial commit. No release checkout edits were made. New Lean
is confined to the requested Uniform paths. Public roots, comparator configs,
formalization YAML, README and papers have no new edits; nothing is pushed.

The corner covers an interior vertex; its real-start and infinity obligations
are explicitly retained. The signed trial was rationalized and mass-repaired;
its saved floating optimized ratio is not asserted for the repaired trial.
The remainder and opposite-sign interaction were added following independent
review. No theorem scope is reduced and no phase beyond0 has started.

Phase1 remains A, N, C-core and the G bank at the full proved generality.
Review the remaining source bridges and production-precision risks before its
implementation. Stop here for Sean's phase review.

## Source volume

Phase0 has no separate line estimate in the plan. New Lean file counts below
include generated numerical tapes and are not comparable to the programme's
26k–55k hand-written estimate. PilotCorner, PilotArithmetic, PilotAudit and the
small rank helper/assembly are hand-written; most remaining lines are generated.

'''+ '\n'.join(f'- `{name}`: {count} lines' for name,count in lines.items())+'\n'
for old,new in [('all205','all 205'),('dimension20','dimension 20'),('rank3','rank 3'),
    ('sum77','sum 77'),('Euler1','Euler 1'),('approximately2.35','approximately 2.35'),
    ('scale1e36','scale 1e36'),('is1e-7','is 1e-7'),('about4.08','about 4.08'),
    ('a4GiB','a 4 GiB'),('to5e09e6f','to 5e09e6f'),('beyond0','beyond 0'),
    ('All3757','All 3757'),('Phase1','Phase 1'),('Phase0','Phase 0'),('low64','low 64')]:
    report=report.replace(old,new)
(OUT/'REPORT.md').write_text(report,encoding='utf-8')
print(json.dumps(data,indent=2))
