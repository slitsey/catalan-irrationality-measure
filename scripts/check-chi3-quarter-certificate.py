"""Audit the exact public quarter witness, Lean enumeration and numeric ledger."""
from pathlib import Path
from fractions import Fraction as F
import json,re,hashlib
R=Path(__file__).resolve().parents[1]
P=R/'paper-lambda/certificates';witness=P/'chi3-quarter-1435.json';d=json.loads(witness.read_text(encoding='utf-8'));b=json.loads((P/'chi3-quarter-1435-budget.json').read_text(encoding='utf-8'))
assert d['pos_den']==2**24 and d['mass_den']==2**32 and d['rho']=='1/2048' and d['alpha']=='1/4'
assert d['r0']=='1/10' and d['eps']=='1/1000'
assert len(d['points'])==1000 and sum(y==0 for x,y,w in d['points'])==400
pts=[]
for x,y,w in d['points']:
 assert w>=0 and x*x+y*y<=256*d['pos_den']**2
 pts.append((x*2**16,y*2**16,w))
 if y:pts.append((x*2**16,-y*2**16,w))
pts.sort();assert len(pts)==1600 and sum(w for x,y,w in pts)==2**32
src=(R/'CatalanCore/Cert/SigmaQuarter/Data.lean').read_text(encoding='utf-8')
actual=[tuple(map(int,v)) for v in re.findall(r'\(\((-?\d+) : ℤ\),\((-?\d+) : ℤ\),\((\d+) : ℕ\)\)',src)]
assert actual==pts,'Frozen witness differs from Lean data'
assert all(pts[j][0]==pts[j+1][0] and pts[j][1]==-pts[j+1][1] and pts[j][2]==pts[j+1][2] for j in range(0,1200,2)) and all(y==0 for x,y,w in pts[1200:])
mp=F(231169,100000);gm=F(-143459,100000);sb=F(b['Sbase']);Ib=F(b['Ibound']);D=F(b['D']);c=F(b['c']);lam=F(b['Lambda']);E=F(b['E'])
assert E==F(287,20) and c==2*(mp-gm) and D<=2*(F(5,4)*mp+3*sb)-F(25,16)*Ib+F(46107,25000)
assert 0<D-lam<1 and E*(D-lam)-c>0
for name in ['FinalCore.lean','Energy.lean']:
 s=(R/'CatalanCore/Cert/SigmaQuarter'/name).read_text(encoding='utf-8');assert '1808029/1000000' in re.sub(r'\s','',s)
core=re.sub(r'\s','',(R/'CatalanCore/Cert/SigmaQuarter/FinalCore.lean').read_text(encoding='utf-8'))
for field,value in [('mprime',mp),('gmin',gm),('Sbase',sb),('Ibound',Ib),('ccert',c)]:assert field+':='+str(value) in core,('Lean budget differs',field)
assert str(D) in core and str(lam) in re.sub(r'\s','',(R/'CatalanFrames/P6Hybrid/QuarterAssembly.lean').read_text(encoding='utf-8'))
name='chi3_hybrid_measure_1435';a=(R/'ChallengeHybrid.lean').read_text(encoding='utf-8');s=(R/'SolutionHybrid.lean').read_text(encoding='utf-8');pattern=r'theorem '+name+r'\s*:(.*?)\s*:='
u=re.search(pattern,a,re.S);v=re.search(pattern,s,re.S);assert u and v and re.sub(r'\s','',u[1])==re.sub(r'\s','',v[1]) and '287/20' in re.sub(r'\s','',u[1])
conf=json.loads((R/'comparator-hybrid.json').read_text(encoding='utf-8'));assert 'CatalanHybridChallenge.'+name in conf['theorem_names']
main=(R/'paper-lambda/lambda-irrationality.tex').read_text(encoding='utf-8');single=(R/'paper-lambda/lambda-irrationality-hexagon.tex').read_text(encoding='utf-8')
for child in re.findall(r'\\input\{([^}]+)\}',main):
 text=(R/'paper-lambda'/(child+'.tex')).read_text(encoding='utf-8');m=re.search(r'% Begin '+re.escape(child)+r'\n(.*?)\n% End '+re.escape(child),single,re.S);assert m and m[1].strip()==text.strip(),('Single-file paper differs',child)
print(json.dumps({'exact_witness_matches_Lean':True,'physical_atoms':len(pts),'exact_budget_clears_14_35':True,'ratio':float(c/(D-lam)),'statements_match':True,'paper_inputs_match_single_file':True,'witness_sha256':hashlib.sha256(witness.read_bytes()).hexdigest()},indent=2))
