"""After integer_covers.py, replace affine ratio coefficient arithmetic by integers.

Field approximations, covers, bounds and exact rational trial coefficients are preserved.
All conversions and computational certificates still require Lean kernel verification.
"""
from pathlib import Path
from fractions import Fraction
import math,re
ROOT=Path(__file__).resolve().parents[2]

def convert(namespace):
    directory=ROOT/'CatalanMeasure'/namespace
    data=directory/'Data.lean'; t=data.read_text(encoding='utf-8')
    ip=directory/'IntegerData.lean'; out=ip.read_text(encoding='utf-8')
    out=out.replace('public import CatalanMeasure.Cert.IntegerGap','public import CatalanMeasure.Cert.IntegerCover')
    if 'def QXZ' in out: out=out[:out.index('def QXZ')]
    else: out=out.split('end CatalanMeasure.'+namespace)[0]
    for axis in ('X','Y'):
        part=t.split('def Q'+axis+' : List ℚ := [',1)[1].split('\ndef ',1)[0]
        qs=[Fraction(int(a),int(b) if b else 1) for a,b in re.findall(r'\((-?\d+)(?: / (\d+))? : ℚ\)',part)]
        D=math.lcm(*(q.denominator for q in qs)); zs=[int(q*D) for q in qs]
        G=math.gcd(*zs); zs=[z//G for z in zs]; scale=Fraction(G,D)
        out+='def Q'+axis+'Z : List ℤ := ['+',\n'.join(map(str,zs))+']\n'
        out+=f'def scaleQ{axis} : ℚ := ({scale.numerator} / {scale.denominator} : ℚ)\n'
        print(namespace,'Q'+axis,'degree',len(zs)-1)
    out+='end CatalanMeasure.'+namespace+'\n'; ip.write_text(out,encoding='utf-8')
    oldnew=[('rowBracketOK Pc Vc P V AX QX MX','integerRowBracketOK Pc Vc P V AXZ QXZ scaleX scaleQX MX')]
    if namespace=='WeightedDualTwo':
        oldnew.append(('modColBracketOK Vc V AY QY MY','integerModColBracketOK Vc V AYZ QYZ scaleY scaleQY MY'))
    else: oldnew.append(('colBracketOK Vc V AY QY MY','integerColBracketOK Vc V AYZ QYZ scaleY scaleQY MY'))
    for a,b in oldnew: t=t.replace(a,b)
    data.write_text(t,encoding='utf-8')
    p=directory/'AQ.lean'; t=p.read_text(encoding='utf-8')
    if 'theorem hIntQX' not in t:
        block=''
        for axis in ('X','Y'):
            block+=f'''set_option maxRecDepth 1000000 in
theorem hIntQ{axis} : Q{axis} = CatalanMeasure.Cert.lpSmul scaleQ{axis} (Q{axis}Z.map (fun (z : ℤ) => (z : ℚ))) := by decide +kernel
'''
        t=t.replace('end CatalanMeasure.'+namespace,block+'\nend CatalanMeasure.'+namespace)
        p.write_text(t,encoding='utf-8')
    p=directory/'Sup.lean'; t=p.read_text(encoding='utf-8')
    for a,b in oldnew: t=t.replace(a,b)
    for name,axis in (('row','X'),('col','Y'),('modCol','Y')):
        t=t.replace(name+'Check_spec_of_noRoot hAQ'+axis,
                    name+'Check_spec_integer hIntA'+axis+' hIntQ'+axis+' hAQ'+axis)
    p.write_text(t,encoding='utf-8')

if __name__=='__main__':
    for namespace in ('Dual','WeightedDualTwo'): convert(namespace)
