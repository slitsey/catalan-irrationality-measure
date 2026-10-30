# Coordinator note, 29 Oct 14:50: slice 1 cap stopped and rerun

- **What stopped:** on Sean's instruction, `job.Chi3Cdx1` (tree 27444 → 11496 → 9560) was stopped at 14:45. Its driver receipt therefore has a nonzero rc, and `continue.py`'s receipt assertion will refuse to proceed. That is intended.
- **What `gen_1.out` contains:**
  - tube edges 1, 3, 5, 7, which are complete and valid;
  - the first 2 cap cells (to −489/5000) under the old rule. The cap after them is missing.
- **Cause:** the χ₋₃ excess region ends about 3·10⁻⁶ past −r0. The old adaptive rule let the first cap cell spend almost the whole budget there, which left nothing for the slack of wide cells out to about −0.07.
- **Fix:** `greedyCap` in `scripts/claude/bank/cover/GenCover.lean.tmpl` now gives the excess region only about four times its own excess (at most 9/10 of R). The rest of R is spread evenly over [a, 0].
- **Rerun:** the cap alone (the same spec `CP 451517278827 125000000000000000`) is running as `job.Chi3Recap0`. Its output goes to `scratch/chi3-recap-2026-10-29/gen_0.out`.
- **To assemble the cover:**
  - take the T lines of `gen_1.out` (edges 1, 3, 5, 7);
  - drop its two old cap cells and use the C lines of `scratch/chi3-recap-2026-10-29/gen_0.out` instead;
  - take slice 0 unchanged.
  - Then relax the receipt check, so that the Chi3Cdx1 failure is accepted in place of a Chi3Recap0 receipt with rc 0.

**Update 15:20:** Sean stopped the cap rerun (`job.Chi3Recap0`) because of the generator hold. The cap for slice 1 is still missing and will be regenerated only after the generator speed-ups land. Keep the tube edges in `gen_1.out`. Do not use `scratch/chi3-recap-2026-10-29/gen_0.out`: it holds only 5 partial cap cells.

**Update 15:52:** at Sean's request, the coordinator ran the energy jobs (`cover.py genE Chi3 --eslices 1`). They read only `Env`, not the tube or cap cells. `gen2_0.out` is done (rc 0). `job.Chi3G0` is writing `gen2G_0.out`; check its receipt before using it.

**Update 16:50:** the slice-1 cap is done. Approved by Sean, it ran in uniform-rate CPU mode (same budget `451517278827/125000000000000000`) as `job.Chi3UCap0`: 26 cells, 0 FAIL, contiguous from -0.098 to 0, rc 0. Output is in `work/catalan-uniform/scratch/chi3-ucap-2026-10-29/gen_0.out`; the cell lines are the usual C/PL format. To assemble the cover, take slice 0 (`gen_0.out` here), the T lines of `gen_1.out` (edges 1, 3, 5, 7; drop its two old cap cells), this cap, and the energy outputs `gen2_0.out` and `gen2G_0.out`. The receipt check in `continue.py` must accept the Chi3Cdx1 failure in place of the Chi3UCap0 receipt (rc 0).

**Update 17:05 (close-out taken over at Sean's request):** the coordinator is running `closeout.py` in this folder. It archives the old cover, emits with the new cap (189 cells, Dt as required), builds the cover, swaps in Decay.draft.lean, builds RankFinal and Chi3.KContent.Bound, and audits. Events are in `closeout-events.jsonl`. Separately, the new k-shift content bound is proved and committed: `Chi3.KContent.Bound.chi3_measure_L2_k`, mu(L(2,chi_-3)) <= 13.7046 (ce465fc). Do not run `continue.py`.
