import sys, json, time; sys.set_int_max_str_digits(0)
from mirror3 import *
R='./CatalanLambda/Cert/'
BIAS=2**62
M=32
GMIN=F(-14645,10000)
r0=F(7,50)
def pack(slots):
    assert all(abs(v)<BIAS for v in slots)
    return sum((v+BIAS)<<(64*k) for k,v in enumerate(slots))
# ---- segment cells: uniform grid, NSEG cells
NSEG=2816
a0=math.floor(-r0*Z)
step=-(a0//NSEG)   # ceil(-a0/NSEG)
assert (NSEG-1)*step < -a0 <= NSEG*step
seg_cells=[(a0+i*step,min(a0+(i+1)*step,0)) for i in range(NSEG)]
# ---- line cells: adaptive bisection
def lb(c): return full_sig(*c)-ut(*c)
def adapt(lo_,hi_,thr,maxw=2**-8):
    out=[]; stack=[(lo_,hi_)]
    while stack:
        a,b=stack.pop()
        if (b-a)<=int(maxw*Z) and lb((a,b))>=thr: out.append((a,b))
        else:
            m=(a+b)//2; stack.append((m,b)); stack.append((a,m))
    return sorted(out)
line_cells=adapt(-(Z//64),0,GMIN)+adapt(0,Z,GMIN)
while len(line_cells)%(4*M)!=0:   # split widest cells until count multiple of 128
    k=max(range(len(line_cells)),key=lambda i:line_cells[i][1]-line_cells[i][0])
    a,b=line_cells.pop(k); m=(a+b)//2; line_cells[k:k]=[(a,m),(m,b)]
NLINE=len(line_cells)
def macro_slots(cells,mode):
    if mode=='seg':
        thr=lambda i,lb_,fl,u: lb_>=fl-F(2,10**5)
    else:
        thr=lambda i,lb_,fl,u: lb_-u>=GMIN if False else True
    # for line: need sigLB - ut >= GMIN ; macro_choose_real passes (lbs=sigLB), uts
    if mode=='line':
        thr=lambda i,lb_,fl,u: lb_-u>=GMIN
    c=macro_choose_real(cells,thr)
    cost,x0,y0,i0,i1,gs=c
    sl=[x0,y0,i0,i1]
    for (xl,xh),g in zip(cells,gs):
        gam=math.floor(g*2**32) if mode=='seg' else 0
        sl+=[xl,xh,gam]
    return sl,cost,gs
def write_module(name,cells,mode,G):
    nmac=len(cells)//M; slots=[]; cost=0; allg=[]
    for k in range(nmac):
        sl,c,gs=macro_slots(cells[k*M:(k+1)*M],mode); slots+=sl; cost+=c; allg+=gs
    P=pack(slots)
    txt=["import CatalanLambda.Cert.RealCells\n\n/-! Generated (gen_real.py): %s, %d cells in %d macros of %d. -/\nnamespace CatalanLambda.Cert\n\nset_option maxRecDepth 100000\n\ndef %sP : Nat := %d\n\n"%(name,len(cells),nmac,M,name,P)]
    modeS='true' if mode=='seg' else 'false'
    for k in range(nmac//4):
        txt.append("theorem %s_c%d : (List.range 4).all (fun j => realMacroOK %s %s %d %sP (%d + j)) = true := by decide +kernel\n"%(name,k,modeS,G,M,name,4*k))
    txt.append("\ntheorem %s_ok : ∀ j < %d, realMacroOK %s %s %d %sP j = true := by\n  have h := chunks_all (fun j => realMacroOK %s %s %d %sP j) %d (by\n    intro k hk\n    interval_cases k\n    exacts [%s])\n  exact h\n"%(name,nmac,modeS,G,M,name,modeS,G,M,name,nmac//4,", ".join("%s_c%d"%(name,k) for k in range(nmac//4))))
    txt.append("\nend CatalanLambda.Cert\n")
    open(R+name+'.lean','w',encoding='utf-8',newline='\n').write("".join(txt))
    return cost,allg
if __name__=="__main__":
    t=time.time()
    half=NSEG//2
    c1,g1=write_module('SegA',seg_cells[:half],'seg','0')
    c2,g2=write_module('SegB',seg_cells[half:],'seg','0')
    gs=g1+g2
    # S_cert integer form: N = sum (b-a)*min(gam*1e5 - 197179*2^32,0) ; here use gam from floor
    gam=[math.floor(g*2**32) for g in gs]
    S=F(0)
    for (a,b),g in zip(seg_cells,gam): S+=2*F(b-a,Z)*min(F(g,2**32)-F(197179,100000),0)
    c3,g3=write_module('LineM',line_cells,'line','(-14645 / 10000 : ℚ)')
    print("seg cells",NSEG,"S_cert",float(S),"cost/cell",(c1+c2)/NSEG,"| line cells",NLINE,"min lb",float(min(g3)),"cost/cell",c3/NLINE,"| t",time.time()-t)
    json.dump({'seg':[(a,b,g) for (a,b),g in zip(seg_cells,gam)],'line':line_cells},open('real_cells.json','w'))
