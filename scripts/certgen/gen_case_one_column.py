from pathlib import Path
import sys
from fractions import Fraction as F
root=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(root/'scripts'/'certgen'))
from fields import Trial,col_fracs,frac_sum
from isolate import plan
from emit import q,qlist

v=Trial([-89913025,52874280,45168341,-30708629,-19269841,33922112,9819141,-16992389],[])
A,Q=frac_sum(col_fracs(v)+[([F(1)],[F(1),F(1)])])
ps=plan(A,F(0),F(1),excluded=())
piece=lambda p:f'({q(p[0])}, {q(p[1])}, {str(p[2]=="bracket").lower()})'
s=f'''module

public import CatalanMeasure.Cert.ModColumn

@[expose] public section

namespace CatalanMeasure.WeightedCaseOne

open CatalanMeasure.Cert OAI.InternalCatalan

def AY : List ℚ := {qlist(A,1)}
def QY : List ℚ := {qlist(Q,1)}
def MY : ℚ := -7586255 / 10000000
def planY : List Piece := [{', '.join(piece(p) for p in ps)}]

set_option maxRecDepth 1000000 in
theorem hAQ : fracSum (modColFracs barrierV1Finite []) = (AY, QY) := by decide +kernel

set_option maxRecDepth 1000000 in
theorem hchain : colCheck [] AY planY = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem hgaps : planY.all (gapOK AY) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem hbrackets : planY.all (modColBracketOK barrierV1Finite [] AY QY MY) = true := by decide +kernel

theorem column_bound : ∀ s ∈ Set.Ioo (0 : ℝ) 1,
    realEnergyColumnTrialField barrierV1 s + Real.log (1 + s) ≤ -7586255 / 10000000 := by
  have h := modColCheck_spec hAQ hchain hgaps hbrackets
  simpa [modColField, trialSeq, barrierV1, MY] using h

end CatalanMeasure.WeightedCaseOne
'''
(root/'CatalanMeasure'/'WeightedCaseOne.lean').write_text(s,encoding='utf-8')
print('case-one column certificate',len(ps),'pieces')
