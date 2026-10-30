"""Record source hashes and latest shared-lane receipts; this does not run Lean."""
from pathlib import Path
import hashlib
import json

repo = Path(r'C:\Users\seanl\Documents\Codex\2026-10-11\plea\work\catalan-uniform')
bank = repo / 'CatalanCore/Uniform/Bank/Lambda'
out = repo / 'scripts/codex/bank/lambda'
lanes = repo.parent / 'tools/lanes'
canonical_paths = ['CatalanCore/Uniform/Content/RankProducer/Assignment.lean',
                   'CatalanCore/Uniform/Content/RankProducer/Lines.lean',
                   'CatalanCore/Uniform/Content/RankProducer/Counts.lean',
                   'CatalanCore/Uniform/Content/BankShared/FixedBudget.lean',
                   'CatalanCore/Uniform/Content/RankProducer/RationalLoads.lean',
                   'CatalanCore/Uniform/Content/RankProducer/LineWitness.lean',
                   'CatalanCore/Uniform/Content/BankShared/FrameEntry.lean',
                   'CatalanCore/Uniform/Content/BankShared/CrudeDet.lean',
                   'CatalanCore/Uniform/Content/BankShared/CrudeFamily.lean',
                   'CatalanCore/Uniform/Content/BankShared/AltCrude.lean']
canonical_paths += ['CatalanCore/Uniform/Content/RankProducer/FibreCounts.lean', 'CatalanCore/Uniform/Content/RankProducer/LineMember.lean', 'CatalanCore/Uniform/Content/RankProducer/LineCost.lean', 'CatalanCore/Uniform/Content/RankProducer/LineScores.lean', 'CatalanCore/Uniform/Content/RankProducer/TrimCost.lean', 'CatalanCore/Uniform/Content/RankProducer/RationalMatches.lean', 'CatalanCore/Uniform/Content/RankProducer/LineTrim.lean', 'CatalanCore/Uniform/Content/RankProducer/ActiveFibres.lean', 'CatalanCore/Uniform/Content/RankProducer/AffineCost.lean', 'CatalanCore/Uniform/Content/BankShared/NormaliseGLE.lean', 'CatalanCore/Uniform/Content/Wire/M3Windows.lean']
canonical_paths += ['CatalanCore/Uniform/Content/Wire/SawPrice.lean', 'CatalanCore/Uniform/Content/BankShared/CompactBudget.lean']
canonical_targets = {p[:-5].replace('/', '.') for p in canonical_paths}
receipts = {}
for p in (lanes / 'done').glob('*.json'):
    try:
        r = json.loads(p.read_text(encoding='utf-8-sig'))
    except (OSError, ValueError):
        continue
    t = r.get('target', '')
    if not (t.startswith('CatalanCore.Uniform.Bank.Lambda.') or t in canonical_targets):
        continue
    if t not in receipts or r.get('submitted', 0) > receipts[t].get('submitted', 0):
        receipts[t] = r
result = {'unconditional_target_proved': False,
          'reused_shared_support': ['CatalanCore/Uniform/Content/BankShared/LeastPrice.lean'],
          'sources': {p.relative_to(bank).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
                      for p in sorted(bank.rglob('*.lean'))},
          'canonical_support_sources': {p: hashlib.sha256((repo / p).read_bytes()).hexdigest() for p in canonical_paths},
          'latest_lane_receipts': receipts}
(out / 'build-evidence.json').write_text(json.dumps(result, indent=2), encoding='utf-8')
for t, r in sorted(receipts.items()):
    print(t, 'rc=', r.get('rc'))
