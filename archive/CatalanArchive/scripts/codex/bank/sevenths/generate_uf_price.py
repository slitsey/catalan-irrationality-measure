from pathlib import Path
from fractions import Fraction as Q
from math import lcm
import json,sys
R=Path(__file__).resolve().parents[4];S=Path(__file__).parent
D=json.loads((S/'profile.json').read_text())
O=R/'CatalanCore/Uniform/Bank/Sevenths/UFPrice';O.mkdir(exist_ok=True)
def ov(r,R,a,b):return max(0,min(R,b+1)-max(r,a))
def cand(m,r,p,rho,k,z):
 B=p*(r//p)+(p if k else 0);ell=rho if z else 0;u=p-1 if z else rho-1
 ub=min(u,max(0,r%p-1)) if k else u;t0=max(r,B+ell);tv=B+ub;w0=B+ell
 if not(t0<r+2*m and t0<=tv and (not k or 1<=r%p)):return 2*(r+m)
 beta=ov(r,r+2*m,w0,tv)+ov(r,r+2*m,w0+p,tv+p)+ov(r,r+2*m,max(0,w0-p),max(0,tv-p))
 sigma=max(0,min(tv+1,r+2*m)-t0-m)
 uu=tv+1-w0+max(0,2*m-beta)
 return max(0,2*(r+m)-(m+sigma+max(0,sigma-max(0,p-uu))))
manifest=[]
for c in D['classes']:
 j=c['root']
 for i,v in enumerate(c['pieces']):
  if v['layer']!='UF':continue
  name=f'C{j}P{i:02}';manifest.append('CatalanCore.Uniform.Bank.Sevenths.UFPrice.'+name)
  if sys.argv[1:] and name not in sys.argv[1:]:continue
  u,vv=Q(v['left']),Q(v['right']);mid=(u+vv)/2;r=12000000;p=round(mid*r)
  if (j*p)%7==0:p+=1
  off=7-(j*p)%7;rho=(j*p+off)//7;m=(r+5)//12
  k,z=min(((k,z) for k in [False,True] for z in [False,True]),key=lambda kz:cand(m,r,p,rho,*kz))
  A,B=map(Q,v['line']);d=lcm(A.denominator,B.denominator);AA=int(A*d);BB=int(B*d)
  assert cand(m,r,p,rho,k,z)<=A*r+B*p+1000,(name,k,z,cand(m,r,p,rho,k,z),A*r+B*p)
  hmid=r//p;hs=sorted(set([int(1/vv),int(1/u)]))
  text=f"""import CatalanCore.Uniform.Content.BankShared.UFPrice
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace CatalanCore.Uniform.Bank.Sevenths.UFPrice
open CatalanCore.Uniform.Content.UFSimple CatalanCore.Uniform.Content.BankShared

theorem {name} (r m p ρ o : ℕ) (hp : 64 ≤ p) (hrp : r ≤ 6 * p)
    (hm1 : 12 * m ≤ r + 6) (hm2 : r ≤ 12 * m + 6)
    (hρ1 : 1 ≤ ρ) (hρp : ρ < p) (ho1 : 1 ≤ o) (ho6 : o ≤ 6)
    (hroot : 7 * ρ = {j} * p + o)
    (hleft : {u.numerator} * r ≤ {u.denominator} * p)
    (hright : {vv.denominator} * p ≤ {vv.numerator} * r) :
    ({d} : ℤ) * (closedPrice m r p ρ : ℤ) ≤ {AA} * (r : ℤ) + {BB} * (p : ℤ) + {1000*d} := by
  have hbound : r / p ≤ 6 := Nat.div_le_of_le_mul (by omega)
  have hd := Nat.div_add_mod r p
  have hrem := Nat.mod_lt r (by omega : 0 < p)
  have hc := closedPrice_le_cand m r p ρ {str(k).lower()} {str(z).lower()}
  have hci : (closedPrice m r p ρ : ℤ) ≤ (candPrice m r p ρ {str(k).lower()} {str(z).lower()} : ℤ) := by exact_mod_cast hc
  have hprice : ({d} : ℤ) * (candPrice m r p ρ {str(k).lower()} {str(z).lower()} : ℤ) ≤
      {AA} * (r : ℤ) + {BB} * (p : ℤ) + {1000*d} := by
    generalize hh : r / p = h at *
    interval_cases h <;>
      simp only [candPrice, CandOK, candB, candL, candU, candUb, hh,
        Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, Nat.mul_zero, Nat.zero_mul,
        zero_add, add_zero, mul_one] <;>
      unfold closedBound beta3 ovl <;> omega
  linarith
#print axioms {name}
end CatalanCore.Uniform.Bank.Sevenths.UFPrice
"""
  (O/(name+'.lean')).write_text(text,encoding='utf-8')
(S/'uf-price-manifest.json').write_text(json.dumps(manifest,indent=2))
print('Prepared selected closed-UF bounds',len(manifest))
