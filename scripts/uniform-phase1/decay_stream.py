"""Literal-preserving baseline/streaming benchmark generator, no old certificates imported."""
import re,sys,json
sys.set_int_max_str_digits(0)
from pathlib import Path
ROOT=Path(r'C:\Users\seanl\Documents\Codex\2026-10-11\plea')
WORK=ROOT/'work/catalan-uniform';OUT=WORK/'CatalanCore/Uniform/Decay/Optimization'
EVID=ROOT/'outputs/Compatibility programme/lean-plan-2026-10-27/evidence/phase1/decay'
source=(WORK/'CatalanCore/Uniform/Decay/PilotPotential.lean').read_text(encoding='utf-8-sig')
start=source.index('def PotentialInput0Tape')
cut=source.index('def Potential0TermsTape')
pre=source[start:cut]
headers='''import CatalanCore.Uniform.Decay.Optimization.Arithmetic
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace CatalanCore.Uniform.Decay.Optimization.Pilot
open CatalanCore.Uniform.Decay.SignedPilot
'''
rows=[];data=headers+pre
for i in range(8):
    a=source.index(f'def Potential{i}TermsTape');b=source.index(f'theorem Potential{i}_rows',a)
    defs=source[a:b];data+=defs
    tape=list(map(int,re.search(r'raw_ints% \[(.*?)\]',defs).group(1).split(',')))
    triples=[tape[j:j+3]for j in range(0,len(tape),3)]
    assert [t[0]for t in triples]==list(range(len(triples)))
    weights=[x for _,n,d in triples for x in (n,d)]
    data+=f'def Potential{i}WeightTape : List Int := raw_ints% ['+', '.join(map(str,weights))+']\n'
    data+=f'def Potential{i}Weights : List (Int × Nat) := valueTape Potential{i}WeightTape\n'
    # valueTape accepts signed Int first coordinate, unlike the interval value convention.
    check=re.search(rf'theorem Potential{i}_rows : checkRows PotentialValues \[Potential{i}Expression\] \[\((\(?-?\d+\)?), (\(?-?\d+\)?)\)\]',source)
    assert check,i
    lo,hi=[int(v.replace('(','').replace(')',''))for v in check.groups()]
    const=list(map(int,re.search(rf'def Potential{i}Constant.*?raw_ints% \[(.*?)\]',defs).group(1).split(',')))
    rows.append((i,*const,lo,hi))
data+='end CatalanCore.Uniform.Decay.Optimization.Pilot\n';(OUT/'FullData.lean').write_text(data,encoding='utf-8')
indexed=headers.replace('Optimization.Arithmetic','Optimization.FullData')
stream=indexed
for i,num,den,lo,hi in rows:
    indexed+=f'theorem indexed{i} : checkRows PotentialValues [Potential{i}Expression] [({lo},{hi})] = true := by decide +kernel\n'
    stream+=f'theorem shape{i} : Potential{i}Expression = (Potential{i}Constant.getD 0 0,(Potential{i}Constant.getD 1 0).toNat,indexedTerms PotentialValues Potential{i}Weights) := by decide +kernel\n'
    stream+=f'theorem streamed{i} : streamCheck PotentialValues (Potential{i}Constant.getD 0 0) (Potential{i}Constant.getD 1 0).toNat Potential{i}Weights {lo} {hi} = true := by decide +kernel\n'
    stream+=f'theorem transferred{i} : checkRows PotentialValues [Potential{i}Expression] [({lo},{hi})] = true := by\n  rw [shape{i},checkRows_stream]\n  exact streamed{i}\n'
indexed+='end CatalanCore.Uniform.Decay.Optimization.Pilot\n';stream+='end CatalanCore.Uniform.Decay.Optimization.Pilot\n'
(OUT/'FullIndexed.lean').write_text(indexed,encoding='utf-8');(OUT/'FullStream.lean').write_text(stream,encoding='utf-8')
(EVID/'stream-benchmark-inputs.json').write_text(json.dumps(dict(source='PilotPotential.lean',physical_pieces=114,inputs=466,rows=8,identical_expected_bounds=True,generator='decay_stream.py',modules=['Arithmetic','FullData','FullIndexed','FullStream'],scope='exact computation equality, no new analytic soundness'),indent=2)+'\n')
print('STREAM_MODULES_GENERATED',len(data),len(indexed),len(stream),flush=True)



