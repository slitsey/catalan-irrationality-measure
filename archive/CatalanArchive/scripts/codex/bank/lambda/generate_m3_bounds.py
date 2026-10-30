from pathlib import Path
from fractions import Fraction as Q
from math import lcm
import json,sys
R=Path(__file__).resolve().parents[4];S=R/'scripts/codex/bank/lambda';data=json.loads((S/'m3-profile-witnesses.json').read_text());out=R/'CatalanCore/Uniform/Bank/Lambda/M3Bounds';out.mkdir(exist_ok=True);manifest=[]
for c in data['witnesses']:
 name=f'C{c["root"]}P{c["piece"]:02}';manifest.append('CatalanCore.Uniform.Bank.Lambda.M3Bounds.'+name)
 if sys.argv[1:] and name not in sys.argv[1:]:continue
 lo,hi=Q(c['left']),Q(c['right']);alpha,beta=map(Q,c['line']);d=lcm(alpha.denominator,beta.denominator);a,b=int(alpha*d),int(beta*d);n0,n1,n3=c['gaps'];j=c['root']
 text=f'''import CatalanCore.Uniform.Bank.Lambda.M3
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.M3Bounds
/-- Exact rounded M3 gap price for this profile piece. -/
theorem {name}_bound (r m p k o : ℕ) (ho : o = 1 ∨ o = 3)
    (hk : 4 * k = {j} * p + o)
    (hm1 : 10 * m ≤ r + 5) (hm2 : r ≤ 10 * m + 5)
    (hleft : {lo.numerator} * r ≤ {lo.denominator} * p)
    (hright : {hi.denominator} * p ≤ {hi.numerator} * r) :
    ({d} : ℤ) * (((2 * r + 2 * m : ℕ) : ℤ) -
      ((m3Upper r m p k {n0} {n1} {n3} - m3Lower r m p k {n0} {n1} {n3} : ℕ) : ℤ)) ≤
      ({a} : ℤ) * r + ({b} : ℤ) * p + {10*d} := by
  unfold m3Upper m3Lower
  omega
#print axioms {name}_bound
end CatalanCore.Uniform.Bank.Lambda.M3Bounds
'''
 (out/(name+'.lean')).write_text(text,encoding='utf-8');print('Prepared rounded M3 bound',name)
(S/'m3-bounds-manifest.json').write_text(json.dumps(manifest,indent=2),encoding='utf-8')