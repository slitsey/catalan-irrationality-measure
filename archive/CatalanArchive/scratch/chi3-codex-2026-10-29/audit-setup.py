from pathlib import Path
import re,json
r=Path.cwd(); s=r/'scratch/chi3-codex-2026-10-29'
# Read import declarations, including multiple imports on one line.
def imports(p):
    return [x for line in re.findall(r'^\s*(?:public\s+)?import\s+([^\n]+)',p.read_text(encoding='utf-8-sig'),re.M) for x in line.split() if not x.startswith('--')]
def closure(m):
    seen=set(); todo=[m]
    while todo:
        x=todo.pop()
        if x in seen: continue
        seen.add(x); p=r/(x.replace('.','/')+'.lean')
        if p.exists(): todo+=imports(p)
    return sorted(seen)
old=closure('CatalanCore.Uniform.Bank.Chi3Rank.RankFinal')
(s/'old-import-closure.json').write_text(json.dumps(old,indent=1))
print('Baseline source closure',len(old))
# This runner is used only after the theorem's dependencies have been built.
(s/'audit.lean').write_text('''import CatalanCore.Uniform.Bank.Chi3Rank.RankFinal
#print axioms CatalanCore.Uniform.Bank.Chi3New.chi3_decay
#print axioms CatalanCore.Uniform.Bank.Chi3Rank.chi3_measure_L2_rank
example : CatalanCore.Measure.MeasureLBAt CatalanFrames.P6.chi3L2
    ((137486 / 10000 : ℚ) : ℝ) :=
  CatalanCore.Uniform.Bank.Chi3Rank.chi3_measure_L2_rank
def main : IO Unit := IO.println "Chi3 final audit completed"
''',encoding='utf-8')
