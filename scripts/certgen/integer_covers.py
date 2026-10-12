"""Postprocess generated root covers into exact integer computations.

Run after gen_dual.py/gen_weighted_dual.py. This script preserves trial data,
bracket/value computations and endpoints. It changes only gap computations.
Every coefficient conversion and no-root certificate is subsequently checked in Lean.
"""
from pathlib import Path
from fractions import Fraction
import math,re

ROOT=Path(__file__).resolve().parents[2]

def convert(namespace):
    directory=ROOT/'CatalanMeasure'/namespace
    data=directory/'Data.lean'
    t=data.read_text(encoding='utf-8')
    out='''module
public import CatalanMeasure.Cert.IntegerGap
@[expose] public section
namespace CatalanMeasure.'''+namespace+'\n'
    for axis in ('X','Y'):
        part=t.split('def A'+axis+' : List ℚ := [',1)[1].split('\ndef Q'+axis,1)[0]
        qs=[Fraction(int(a),int(b) if b else 1) for a,b in re.findall(r'\((-?\d+)(?: / (\d+))? : ℚ\)',part)]
        D=math.lcm(*(q.denominator for q in qs)); zs=[int(q*D) for q in qs]
        G=math.gcd(*zs); zs=[z//G for z in zs]; scale=Fraction(G,D)
        out+='def A'+axis+'Z : List ℤ := ['+',\n'.join(map(str,zs))+']\n'
        out+=f'def scale{axis} : ℚ := ({scale.numerator} / {scale.denominator} : ℚ)\n'
        print(namespace,axis,'degree',len(zs)-1)
    out+='end CatalanMeasure.'+namespace+'\n'
    (directory/'IntegerData.lean').write_text(out,encoding='utf-8')
    import_line='public import CatalanMeasure.'+namespace+'.IntegerData'
    if import_line not in t:
        t=t.replace('public import CatalanMeasure.Cert.Norm','public import CatalanMeasure.Cert.Norm\n'+import_line)
    t=t.replace('gapOK AX p','integerGapOK AXZ p').replace('gapOK AY p','integerGapOK AYZ p')
    data.write_text(t,encoding='utf-8')
    p=directory/'AQ.lean'; t=p.read_text(encoding='utf-8')
    block=''
    for axis in ('X','Y'):
        block+=f'''set_option maxRecDepth 1000000 in
theorem hIntA{axis} : A{axis} = CatalanMeasure.Cert.lpSmul scale{axis} (A{axis}Z.map (fun (z : ℤ) => (z : ℚ))) := by decide +kernel
theorem hScale{axis} : scale{axis} ≠ 0 := by decide +kernel
'''
    if 'theorem hIntAX' not in t:
        t=t.replace('end CatalanMeasure.'+namespace,block+'\nend CatalanMeasure.'+namespace)
        p.write_text(t,encoding='utf-8')
    p=directory/'Sup.lean'; t=p.read_text(encoding='utf-8')
    col='modColBracketOK' if namespace=='WeightedDualTwo' else 'colBracketOK'
    for axis,g in (('X','rowBracketOK Pc Vc P V AX QX MX'),('Y',col+' Vc V AY QY MY')):
        old=f'(all_and_left (f := gapOK A{axis}) (g := {g}) all{axis})'
        new=f'(integerGaps_spec hScale{axis} hIntA{axis} (all_and_left (f := integerGapOK A{axis}Z) (g := {g}) all{axis}))'
        t=t.replace(old,new).replace('f := gapOK A'+axis,'f := integerGapOK A'+axis+'Z')
    for name in ('rowCheck_spec','colCheck_spec','modColCheck_spec'):
        t=re.sub(r'\b'+name+r'\b',name+'_of_noRoot',t)
    p.write_text(t,encoding='utf-8')

if __name__=='__main__':
    for namespace in ('Dual','WeightedDualTwo'): convert(namespace)
