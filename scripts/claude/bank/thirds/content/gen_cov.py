"""Generate the thirds piece-cover lemmas (T and M3D layers) and validate them by brute force first.
usage: gen_cov.py check | emit"""
import json, math, sys
from fractions import Fraction as F
sys.dont_write_bytecode=True
HERE='C:/Users/seanl/Documents/Codex/2026-10-11/plea/work/catalan-uniform/'
AL=F(3,20); MARG=3; E0=300000000
prof=json.load(open(HERE+'scripts/claude/bank/thirds/content/nouf-profile.json'))
for _c in prof['classes']: _c['pieces'].append(dict(left='39/10',right='4',line=['0','0'],layer='T'))

class Line:
    def __init__(s,i,sl): s.i=F(i); s.s=F(sl)
    def __call__(s,x): return s.i+s.s*x
    def key(s): return (s.i,s.s)

# (a, cls) -> e, root index (0: kappa=1/3, 1: kappa=2/3)
CASES={(1,1):(2,0),(1,5):(2,1),(2,1):(1,1),(2,5):(1,0)}
def kappa_j(e,cls):   # 3 kq = J p + e
    return 1 if (cls%3+e)%3==0 else 2
def border(r):
    return min(math.ceil(F(3,10)*r/2), math.ceil((F(3,10)*r-1)/2))

def cutlines(ka,lo,hi):
    xs=set(); nmax=int((1+2*AL)/lo)+3
    for n in range(0,nmax+1):
        for x in (F(n),n+ka):
            if x>0: xs.add(x)
    return [('cut0',Line(0,x)) for x in sorted(xs)]+[('cutr',Line(1,j)) for j in range(0,3)]
LO=[('lo_r',Line(1,0)),('lo_p',Line(1+2*AL,-1))]
HI=[('hi_m',Line(1+2*AL,0)),('hi_p',Line(1,1))]
def candidates(ka,u,v):
    m=(u+v)/2; cuts=cutlines(ka,u,v)
    wl=max(LO,key=lambda t:t[1](m)); wh=min(HI,key=lambda t:t[1](m))
    inner=sorted([c for c in cuts if wl[1](m)<c[1](m)<wh[1](m)],key=lambda c:c[1](m))
    pts=[wl]+inner+[wh]; out=[]
    for A,B in zip(pts,pts[1:]):
        if B[1](m)>A[1](m):
            out.append((Line(2+2*AL-(B[1].i-A[1].i),-(B[1].s-A[1].s)),A,B))
    return out

def pos_expr(e,cls,key):
    i,s=key
    if i==1: return ('r + %d*p'%int(s), lambda r,m,p: r+int(s)*p)
    n=math.floor(s); fr=s-n
    if fr==0: return ('%d*p'%n, lambda r,m,p: n*p)
    J=kappa_j(e,cls)
    assert fr==F(J,3),(key,J)
    return ('%d*p + (%d*p + %d)/3'%(n,J,e), lambda r,m,p: n*p+(J*p+e)//3)

def m3_endpoints(e,cls,Atag,Akey,Btag,Bkey):
    K='G310.borderSize i.1'
    if Atag=='lo_r': a=('i.1',lambda r,m,p:r)
    elif Atag=='lo_p': a=('(i.1 + 2*%s - p)'%K,lambda r,m,p:r+2*m-p)
    else:
        ex,f=pos_expr(e,cls,Akey); a=('(%s + %d)'%(ex.replace('r','i.1') if False else ex.replace('r + ','i.1 + '),MARG),lambda r,m,p,f=f:f(r,m,p)+MARG)
    if Btag=='hi_m': b=('(i.1 + 2*%s)'%K,lambda r,m,p:r+2*m)
    elif Btag=='hi_p': b=('(i.1 + p)',lambda r,m,p:r+p)
    else:
        ex,f=pos_expr(e,cls,Bkey); b=('(%s - %d)'%(ex.replace('r + ','i.1 + '),MARG),lambda r,m,p,f=f:f(r,m,p)-MARG)
    return a,b

def refine_m3(e,cls,root,piece):
    """split a profile M3D piece into subpieces with a constant window pair; return list of (s,t,tagpair)"""
    ka=F(root+1,3); s,t=F(piece['left']),F(piece['right']); ln=Line(*map(F,piece['line']))
    # sample-based detection of the pair; split at pair changes via kinks of all cut/lo/hi lines
    L=[c[1] for c in cutlines(ka,s,t)]+[x[1] for x in LO+HI]
    K={s,t}
    for a_ in range(len(L)):
        for b_ in range(a_):
            f,g=L[a_],L[b_]
            if f.s!=g.s:
                x=(g.i-f.i)/(f.s-g.s)
                if s<x<t: K.add(x)
    K=sorted(K); subs=[]
    for u,v in zip(K,K[1:]):
        cs=[(l,A,B) for (l,A,B) in candidates(ka,u,v) if l.key()==ln.key()]
        assert cs,(piece,u,v)
        l,A,B=cs[0]
        tag=(A[0],A[1].key(),B[0],B[1].key())
        if subs and subs[-1][2]==tag and subs[-1][1]==u: subs[-1]=(subs[-1][0],v,tag)
        else: subs.append((u,v,tag))
    return subs

def primes_like(lo,hi,cls,cnt=7):
    out=[]
    for w in (F(1,1000),F(1,50),F(1,7),F(1,3),F(1,2),F(2,3),F(24,25),F(999,1000)):
        p=int(lo+(hi-lo)*w)
        while p%6!=cls: p+=1
        if lo<p<=hi: out.append(p)
    return out

def cutfree(a,b,r,p,e):
    # no t in (a,b) (exclusive both ends are covered by margins) with p|t, p|3t-e, p|t-r
    lo,hi=a+1,b-1   # t in [a+1,b-1]
    if lo>hi: return True
    if hi//p>(lo-1)//p: return False
    if (hi-r)//p>(lo-1-r)//p: return False
    # 3t-e = j p: t=(jp+e)/3 ; scan j in range
    j0=(3*lo-e)//p; j1=(3*hi-e)//p+1
    for j in range(j0,j1+1):
        if (j*p+e)%3==0 and lo<=(j*p+e)//3<=hi: return False
    return True

def brute_m3(e,cls,root,s,t,ln,tag,rs):
    Atag,Akey,Btag,Bkey=tag
    (ae,af),(be,bf)=m3_endpoints(e,cls,Atag,Akey,Btag,Bkey)
    usedm3=0; worst=None
    for r in rs:
        m=border(r)
        for p in primes_like(s*r,t*r,cls):
            if not (s*r<p<=t*r): continue
            a=max(r,af(r,m,p)); b=min(bf(r,m,p),r+2*m,r+p)
            ap=max(a,r+2*m-p)
            if ap+8<=b:
                usedm3+=1
                assert r<=a<=b<=r+2*m and b<=r+p
                assert cutfree(a,b,r,p,e),('cut',r,p,a,b,tag)
                price=2*r+(2*m-(b-ap))
            else:
                price=2*(r+m)
            val=ln.i*r+ln.s*p
            worst=max(worst,price-val) if worst is not None else price-val
    return usedm3,worst

mode=sys.argv[1] if len(sys.argv)>1 else ''
if __name__=='__main__' and mode=='check':
    rs=[10**6+2,3*10**6+4,10**8+6,7*10**9+8]
    for (a,cls),(e,root) in CASES.items():
        print('a',a,'cls',cls,'e',e,'root',root+1)
        for k,pc in enumerate(prof['classes'][root]['pieces']):
            if pc['layer']!='M3D': continue
            ln=Line(*map(F,pc['line']))
            subs=refine_m3(e,cls,root,pc)
            for (u,v,tag) in subs:
                n,w=brute_m3(e,cls,root,u,v,ln,tag,rs)
                print('  piece',k,u,v,tag[0],tag[2],'m3 used',n,'worst',float(w) if w is not None else None)

# ---------------------------------------------------------------- emission
sys.path.insert(0,HERE+'scripts/claude/bank/thirds/content')
import branches as BR
def lcm(a,b): return a*b//math.gcd(a,b)
def piece_args(s,t,ln):
    D=lcm(ln.i.denominator,ln.s.denominator)
    return (s.numerator,s.denominator,t.numerator,t.denominator,int(ln.i*D),int(ln.s*D),E0*D,D)
def par(x): return '(%d)'%x if x<0 else str(x)

def nvals(e,cls,root,s,t,tag,rs):
    Atag,Akey,Btag,Bkey=tag
    (ae,af),(be,bf)=m3_endpoints(e,cls,Atag,Akey,Btag,Bkey)
    n0s=set();n1s=[];n1e=[];n3s=set()
    for r in rs:
        m=border(r)
        for p in primes_like(s*r,t*r,cls):
            a=max(r,af(r,m,p)); b=min(bf(r,m,p),r+2*m,r+p)
            if max(a,r+2*m-p)+8>b: continue
            n0s.add(a//p); n3s.add((a-r)//p)
            n1s.append((3*a-e)//p); n1e.append(-((-(3*b-e))//p))
    assert len(n0s)==1 and len(n3s)==1,(tag,n0s,n3s)
    n1=min(n1s); K1=max(n1e)-n1-1
    assert 0<=K1<=4
    return n0s.pop(),n1,K1,n3s.pop()

def aexpr(e,cls,tag):
    Atag,Akey,Btag,Bkey=tag
    K='G310.borderSize RR'
    if Atag=='lo_r': lo='RR'
    elif Atag=='lo_p': lo='(RR + 2*%s - p)'%K
    else:
        ex,_=pos_expr(e,cls,Akey); lo='(%s + %d)'%(ex.replace('r + ','RR + '),MARG)
    if Btag=='hi_m': hi='(RR + 2*%s)'%K
    elif Btag=='hi_p': hi='(RR + p)'
    else:
        ex,_=pos_expr(e,cls,Bkey); hi='(%s - %d)'%(ex.replace('r + ','RR + '),MARG)
    return 'max RR %s'%lo, 'min %s (min (RR + 2*%s) (RR + p))'%(hi,K)

def header(name,Fr,cls,args):
    sn,sd,tn,td,A,B,E,D=args
    return (f"theorem {name} (depth : ℕ) (i : (FamE {Fr} depth).ι) (hi : (FamE {Fr} depth).Adm i) (p : ℕ)\n"
      f"    (hpc : (p : ZMod 6) = {cls}) [hp : Fact p.Prime] :\n"
      f"    {sn} * i.1 / {sd} < p → p ≤ {tn} * i.1 / {td} → PCov {Fr} depth i p {par(A)} {par(B)} {par(E)} {par(D)} := by\n"
      f"  intro hs ht\n"
      f"  have hp6 : p % 6 = {cls} := cls6 (r := {cls}) (by simpa using hpc) (by norm_num)\n"
      f"  have hp5 : 5 ≤ p := by have := hp.out.two_le; omega\n"
      f"  by_cases hr : i.1 < 10 ^ 6\n"
      f"  · exact pcov_small (by simp [cFr_{Fr}]) i hi hr p hp.out.two_le _ _ _ _ (by norm_num) (by omega)\n"
      f"  · push_neg at hr\n"
      f"    have hr2 : i.1 % 2 = 0 := hi.2\n"
      f"    obtain ⟨hk1, hk2⟩ := border_bounds hr2\n"
      f"    have hsq : 3 * (i.1 + 2 * G310.borderSize i.1) < p * p := hsq_of hr hk2 (by omega)\n"
      f"    have hG := thirds_T_gle {Fr}_data depth i hr2 (by omega) p hp5 hsq\n")

def emit_case(a,cls):
    e,root=CASES[(a,cls)]
    Fr='thirdsAc' if a==1 else 'thirdsBc'; data=Fr+'_data'
    out=[]
    rs=[10**6+2,3*10**6+4,10**8+6,7*10**9+8]
    for k,pc in enumerate(prof['classes'][root]['pieces']):
        s,t=F(pc['left']),F(pc['right']); ln=Line(*map(F,pc['line']))
        args=piece_args(s,t,ln)
        if pc['layer']=='T':
            name=f"tcov_{a}_{cls}_{k}"
            ok=BR.check(pc,e,cls,[10**7+2,3*10**8+4,7*10**9+6])
            br=[b for b in ('D1x','D45','D6','D2') if ok[b]][0]
            txt=header(name,Fr,cls,args)
            if br=='D1x':
                txt+=(f"    have hb := XGm_D1x (thirdsInst {data}) i.1 (G310.borderSize i.1) p hp.out (by omega)\n"
                      f"    have hmod : G310.borderSize i.1 % p = G310.borderSize i.1 := Nat.mod_eq_of_lt (by omega)\n"
                      f"    rw [hmod] at hb\n"
                      f"    exact ⟨_, hG, by omega⟩\n")
            elif br=='D45':
                txt+=(f"    have hb := XGm_D45 (thirds_levels {data}) i.1 (G310.borderSize i.1) p hp.out hp5 (by omega) (by omega)\n"
                      f"    have hq := thirds_kq_formula {data} hp5 (by omega)\n"
                      f"    exact ⟨_, hG, by omega⟩\n")
            elif br=='D6':
                txt+=(f"    have hq := thirds_kq_formula {data} hp5 (by omega)\n"
                      f"    have hb := XGm_D6 (thirds_levels {data}) i.1 (G310.borderSize i.1) p hp.out hp5 (by omega) (by omega)\n"
                      f"    exact ⟨_, hG, by omega⟩\n")
            else: raise Exception('no branch')
        elif pc['layer']=='M3D':
            name=f"mcov_{a}_{cls}_{k}"
            subs=refine_m3(e,cls,root,pc); assert len(subs)==1
            tag=subs[0][2]
            n0,n1,K1,n3=nvals(e,cls,root,s,t,tag,rs)
            ae,be=aexpr(e,cls,tag)
            A_=ae.replace('RR','i.1'); B_=be.replace('RR','i.1'); Af=ae.replace('RR','r'); Bf=be.replace('RR','r')
            K='G310.borderSize i.1'
            txt=header(name,Fr,cls,args)
            txt+=(f"    by_cases hlen : max ({A_}) (i.1 + 2 * {K} - p) + 8 ≤ {B_}\n"
                  f"    · have hv : m3dValid G310 {Fr} (fun r p => {Af}) (fun r p => {Bf}) i.1 p :=\n"
                  f"        m3dValid_thirds {data} _ _ i.1 p hr2 hp5 hsq (by omega) (by omega) (by omega) (by omega) (by omega)\n"
                  f"          (nocut_window3 p i.1 _ _ {e} hp.out.pos {n0} {n1} {K1} {n3}\n"
                  f"            ⟨by omega, by omega⟩ ⟨by omega, by omega⟩\n"
                  f"            (by intro j hj1 hj2; interval_cases j <;> omega) ⟨by omega, by omega⟩)\n"
                  f"      have hg := m3_gle (fun r p => {Af}) (fun r p => {Bf}) i hi p hv\n"
                  f"      beta_reduce at hg\n"
                  f"      exact ⟨_, hg, by omega⟩\n"
                  f"    · have hb := XGm_D1 (thirdsInst {data}) i.1 (G310.borderSize i.1) p\n"
                  f"      exact ⟨_, hG, by omega⟩\n")
        else: continue
        out.append((name,pc['layer'],k,args,txt))
    return Fr,out

PRE='''import CatalanCore.Uniform.Bank.ThirdsContent.Pre
import CatalanCore.Uniform.Bank.ThirdsContent.M3
import CatalanFrames.HybGen.TableSum
set_option Elab.async false
set_option maxHeartbeats 3200000
set_option maxRecDepth 4000

/-! Generated by `scripts/claude/bank/thirds/content/gen_cov.py`: tropical (table T) and M3D piece
covers of the thirds no-UF profile, case a = %d, class %d (mod 6).  Each lemma is affine arithmetic
for `omega` after the layer bridge (`thirds_T_gle`, `m3_gle`, `nocut_window3`). -/

namespace CatalanCore.Uniform.Bank.ThirdsContent
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Bank.Thirds CatalanCore.Uniform.Content.Shape
  CatalanCore.Uniform.Content.Wire CatalanCore.Arith.Hybrid CatalanFrames.HybGen CatalanFrames.Thirds

'''
if __name__=='__main__' and mode=='emit':
    which=[(int(x.split(',')[0]),int(x.split(',')[1])) for x in sys.argv[2:]] or list(CASES)
    for (a,cls) in which:
        Fr,out=emit_case(a,cls)
        txt=PRE%(a,cls)+'\n'.join(o[4] for o in out)+'\nend CatalanCore.Uniform.Bank.ThirdsContent\n'
        p=HERE+f'CatalanCore/Uniform/Bank/ThirdsContent/Cov/A{a}C{cls}.lean'
        import os; os.makedirs(os.path.dirname(p),exist_ok=True)
        open(p,'w',encoding='utf-8').write(txt)
        print('wrote',p,len(out),'lemmas')

# ---- sawtooth prefix pieces (generic in the frame)
NPRE=50
def prefix_pieces():
    pcs=[]
    for n in range(NPRE-1,0,-1):
        u=AL/(n+1); v=2*AL/(2*n+1); w=AL/n
        pcs.append((n,0,u,v,Line(2+3*AL,-(n+1))))
        pcs.append((n,1,v,w,Line(2+AL,n)))
    return pcs
def emit_prefix():
    out=[PRE_P]
    for (n,h,u,v,ln) in prefix_pieces():
        sn,sd,tn,td,A,B,E,D=piece_args(u,v,ln)
        name=f"pcov_{n}_{h}"
        out.append(
f"""theorem {name} {{Fr : Frame}} {{e : ℕ}} (T : ThirdsData Fr e) (depth : ℕ) (i : (FamE Fr depth).ι)
    (hi : (FamE Fr depth).Adm i) (hc : cFr Fr ≤ 25) (p : ℕ) [hp : Fact p.Prime] :
    {sn} * i.1 / {sd} < p → p ≤ {tn} * i.1 / {td} → PCov Fr depth i p {par(A)} {par(B)} {par(E)} {par(D)} := by
  intro hs ht
  by_cases hr : i.1 < 10 ^ 6
  · exact pcov_small hc i hi hr p hp.out.two_le _ _ _ _ (by norm_num) (by omega)
  · push_neg at hr
    have hp5 : 5 ≤ p := by omega
    have hr2 : i.1 % 2 = 0 := hi.2
    obtain ⟨hk1, hk2⟩ := border_bounds hr2
    have hsq : 3 * (i.1 + 2 * G310.borderSize i.1) < p * p := hsq_of hr hk2 (by omega)
    have hG := thirds_T_gle T depth i hr2 (by omega) p hp5 hsq
    have hb := XGm_D1x (thirdsInst T) i.1 (G310.borderSize i.1) p hp.out (by omega)
    have hd := dist_ge p (G310.borderSize i.1) {n} hp.out.pos (by omega)
    generalize G310.borderSize i.1 % p = s0 at hb hd
    exact ⟨_, hG, by omega⟩
""")
    out.append('end CatalanCore.Uniform.Bank.ThirdsContent\n')
    p=HERE+'CatalanCore/Uniform/Bank/ThirdsContent/Cov/Prefix.lean'
    open(p,'w',encoding='utf-8').write('\n'.join(out)); print('wrote',p,len(out)-2)
PRE_P='''import CatalanCore.Uniform.Bank.ThirdsContent.Pre
set_option Elab.async false
set_option maxHeartbeats 3200000

/-! Generated by `scripts/claude/bank/thirds/content/gen_cov.py`: the finite sawtooth prefix
(`delta = 3/1000`, `N = 50`) of the thirds no-UF profile, from `XGm_D1x` and `dist_ge`. -/

namespace CatalanCore.Uniform.Bank.ThirdsContent
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Bank.Thirds CatalanCore.Arith.Hybrid
  CatalanFrames.HybGen CatalanFrames.Thirds

'''
if __name__=='__main__' and mode=='prefix': emit_prefix()
if __name__=='__main__' and mode=='prefixcheck':
    for (n,h,u,v,ln) in prefix_pieces():
        for r in (10**6+2,10**9+4):
            m=border(r)
            for w in (F(1,100),F(1,2),F(99,100)):
                p=int((u+(v-u)*w)*r)|1
                if not (u*r<p<=v*r): continue
                assert n*p<=m,(n,h,r,p,m)
                dm=min(m-n*p,(n+1)*p-m)
                val=2*r+2*m-dm
                assert val<=ln.i*r+ln.s*p+8,(n,h,r,p,val,ln.i*r+ln.s*p)
    print('prefix ok')
