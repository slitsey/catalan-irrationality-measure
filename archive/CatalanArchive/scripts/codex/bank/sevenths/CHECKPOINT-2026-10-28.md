# Sevenths bank — paused at user request, 28 October 2026

The work is NOT complete. The all-six measure theorem is still conditional on the
content and decay providers. User explicitly requested “Checkpoint and pause”.
No commits were made and no other lane's bank sources were edited.

## Locations and build contract

Actual repo: C:/Users/seanl/Documents/Codex/2026-10-11/plea/work/catalan-uniform
Owned sources: CatalanCore/Uniform/Bank/Sevenths and scripts/codex/bank/sevenths.
Generic reusable siblings were added under Content/BankShared and Content/RankProducer.
Before EVERY submission run scripts/claude/run_guarded.py <Module> preflight 3;
submit stale dependencies first. scripts/codex/bank/sevenths/admit.py enforces this.
Use the shared scripts/claude/lanes.py driver, never direct lake build. Cap actual
Lean peaks at 2.5 GiB. The earlier cover handoff allows budget 8 for cover roots,
but the newer HOLD below takes priority.

## Current handoff: decay HOLD

Reread the canonical handoff at outputs/Compatibility programme/lean-plan-2026-10-27/
HANDOFF-codex-2026-10-28-sevenths-bank.md on resume. Its latest update (~21:20) says:
HOLD decay builds; B6 is reconciling cover.py against the screen algorithm.
Do CONTENT now; generate only after a handoff announcement clears the generator.

The owned decay controller was stopped. Its restart guard requires an explicit
owned decay-generator-cleared.json marker, which does not exist. Only Cover/Env0
was emitted; the full trial-A cover was NOT generated. An earlier queued Sev1.Segs
prerequisite was caught when the driver admitted it after the hold and its exact
Lean process was stopped; native driver receipt rc 1 preserves this interruption.
Do not mistake this for a mathematical/certificate failure. Preserve trial A:
19 basis / 27 physical pieces; do not substitute trial B or a partial cover.

## Verified and prepared work

- Geom, Frame, NV, Final, conditional Members/Audit, SmallPrimes, Normalisation,
  exact Energy and Roots have successful own build evidence (check source freshness).
  Correct target is 3549.65 = 70993/20, never 3549.6.
- All 240 exact rank certificates are grouped in six unchanged root-class modules
  C1,C3,C5,C9,C11,C13. RankData root classes passed. Four palette roots passed;
  C11/C13 palettes were held in the queue at pause. Every certificate remains an
  independent kernel declaration. The superseded 480 individual data/palette
  sources are archived under archive/CatalanArchive/.../Sevenths.
- SawPrefix.exists_mass_slack passed (exact logarithmic limiting prefix); the
  repaired SawTemplate chain passed. RankProducer.Balance passed after adding Block.
- Exact finite profiles have 390 pieces using T/R/strictLP/M3D/UF. Their exact mass
  is Lam7. Computational source replay input-checks.json passed all 240 rank types,
  143 rank cells, 143 UF cells, 72 top extensions, 1092 wedges. This is computational
  evidence, not a substitute for physical Lean coverage.
- 143 RankSource and RankFibre files exist; only RankSource.C1S00 has qualified.
  First physical assignment C1S00 is the qualification gate before expanding.
- RankLoads are prepared in six grouped modules; original generated 240 individual
  load wrappers are archived. Counts/Facts/Matches/RankPrice generators are adapted
  to q7 and have only C1S00 outputs prepared so far. Counts errors use 48+8*depth;
  matching errors use 96+16*depth. Max physical runs is 8; max side kills per cell 4.
- PrimeBound is the explicit fixed bound for all recorded rational units and basis
  denominators. RankUnits proves integrality/nonzero reduction beyond it.
- New source modules awaiting qualification include PoleData, LPWindows, LP, UFWindow,
  Price, Tropical, TropicalLevels, Tail, Budget, Classes, Profile.Template/Limiting,
  RankSetup/RankFinish, M3D, generic LPPrice/LeastPrice/LineBound/CrudeLog/UFPrice.
  checkpoint-inventory.json is the source/hash/log/peak inventory, not an assertion
  that every drafted source compiles.

## Last repairs, still requiring guarded recheck

TwoTerm: the explicit thirdsFrame arguments now elaborate; the last errors were
Nat.cast numeral normalization. Added norm_num only [Nat.cast_ofNat] after both
Delta_eq and Dsq_eq rewrites.

BankShared.PoleTropical: explicitly typed every filter binder as Nat (untyped
ascriptions had inferred Int), fixed eq_empty_iff_forall_notMem, and simplified
both diagonal wt cases with simp [wt, hl]. Earlier off-diagonal integrality proofs
had no reported errors. All repaired sources must be rechecked before acceptance.

## Mathematical continuation plan

One epsilon-independent price is leastGLE for each actual member polynomial;
crude GLE proves existence at every prime. Nat.find_spec proves validity and
Nat.find_min' compares it with every independently proved layer. This removes
validity switches without assuming any layer conclusion. Exceptions are retained
and bounded by Ecrude. coefficientCut supplies a finite polynomial cutoff.

Prefix: Budget = fixedCrude on primes <= rankPrimeCutoff, plus sqrtLog(14,C), plus
unit rounding. CrudeLog generalizes the fifths logarithmic bound to arbitrary cFr.
For p^2 > 14r and p above the fixed cutoff, PoleTropical plus simple two-term poles
supplies the actual HW clearing table. SawPrice has q7 slope/rounding branches.
Tail is drafted using poleLevels=0 below the first pole, val_D6 and p>14r.

Rank: RankFinish transports all actual balanced kills and rational matching counts.
LineBound turns those counts into affine prices, accounting for EVERY discarded
kill. generate_rank_price.py emits actual RankMember existence bounds with error
1000*(r-s.card+1). It verifies each selected line is the raw or matching-density
line. Qualify C1S00 before generating/queuing all 143 cells. Then connect these
norm-one common-minor prices to actual family prices via PrimeNormalisation,
MemberIdentity, retainedFin/card_retainedFin and seventhsPrice_le.

LP: generic LPPrice proves natural slot sums/bounds. LP1 price <=
2*(r-(rho-(r-p)))+3m; LP2 price <=2*(r-rho)+3m. LPWindows uses the SHARP rounding
12m<r+6 to obtain the exact LP2 N<=p+rho frontier. LP1/LP2 wrappers are drafted.
For the LP2 boundary where p>=r+m, the D45 tropical bound yields the same
2*(r-rho)+3m bound; this fallback is still to implement.

M3D: M3D.lean drafts exact no-cut intervals (n*p+[0,rho] or n*p+[rho,p]), avoiding
core exits in [r,r+p), and actual family GLE via Wire.m3dLayer. Still implement
candidate window A=max r(start), B=min(r+2m)(min(r+p)(end)), central A'=max A(N-p).
If A'>B use the raw tropical bound (zero saved length); otherwise use M3D. Then
certify the 168 chosen leading M3D pieces with integer arithmetic. Use candidate
n=floor(r/p)+kappa, z in Bool, splitting floor cases. Merged profile pieces can
cross cut-order changes, so choose witnesses per floor/subinterval, not blindly
one midpoint witness over an entire merged piece.

UF: UFWindow drafts all ClosedHyp conditions for r>=12, p>=64, r<=6p. The first
selected UFPrice.C1P26 uses canonical closedPrice <= candPrice and exact integer
arithmetic with O(1) slack; qualify it before generating all 77 UF pieces. If a
merged interval changes the best relative candidate, split floor cases and choose
kappa/z per case (do not weaken source hypotheses).

Templates: Classes maps the six unit classes mod14 to exact physical roots.
Profile.Template appends a zero-leading tail to theta=14 and the finite sawtooth
prefix. Profile.Limiting drafts the exact class average and existence of a prefix
depth for every epsilon, independent of the additive coverage constant C.
Still connect all pointwise layer bounds, prove finite prefix piece coverage and
all full profile coverage, choose C_N paying bounded initial scales and fixed bad
primes on compact windows, and close hasScaledContent_budgeted_lim at exact Lam7.
Choose prefix depth at C=0 first; pieces_mass is independent of C, so choose C_N
later without circularity. Fixed bad primes in a compact window force bounded r;
likewise p^2<=14r above its positive left endpoint forces bounded r.

After unconditional content and cleared/verified full trial-A decay, discharge
ContourOK/floor/min-shift (drafted in Contour), geometry, Energy, and all source
hypotheses for all six actual norm-49 frames. Finish an UNCONDITIONAL all-six
sevenths_measure theorem and standard-axiom audit, with fresh own logs and peaks.

## Resume execution

pause-state.json records held bank jobs and checks in flight. paused-jobs contains
preserved requests; DO NOT move them straight back into the shared queue. Resubmit
through admit.ensure so every stale frontier is rechecked. Native content_campaign.py
runs three bounded qualification chains, adopts queued/running work, and writes
per-module source/hash/log/actual-peak receipts. Its current process was stopped.
Catalogue controller was also stopped. Existing shared generic jobs were preserved
because other lanes may consume them. No shared driver or other lane was stopped.

Old build-evidence.json is incomplete due to historical concurrent overwrite;
module-receipts, catalogue-receipts, own build JSON/logs and checkpoint-inventory
are authoritative. Content campaign validates source time before build start and
actual Lean peak <=2.5 GiB. Reconcile in-flight completion before replacements.

## Pause inventory result

At pause the conservative inventory recorded 44 fresh successful module checks,
one fresh failure (Classes.rootForClass_spec, omega; not repaired while paused),
and 331 generated/drafted modules requiring validation. The repaired TwoTerm and
PoleTropical sources still require their latest completion receipts to be reconciled.
See pause-state.json for final native rc values of checks admitted before pause.
