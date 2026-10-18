import sys, json, time; sys.set_int_max_str_digits(0)
from genraymac import *
M=32; PER=32
boxes=allboxes()
nmac=(len(boxes)+M-1)//M
nmod=(nmac+PER-1)//PER
t=time.time(); tot=0
for n in range(nmod):
    slots=[]
    for k in range(PER):
        mi=min(n*PER+k,nmac-1)   # pad with last macro
        sl,c=macro_slots(boxes[mi*M:mi*M+M],M); slots+=sl; tot+=c[0]
    P=pack(slots)
    name="RayM%d"%n
    txt=["import CatalanLambda.Cert.RayTaylor\n\n/-! Generated (gen_allray.py): ray macros %d..%d (M=%d, %d per module); Taylor far-field. -/\nnamespace CatalanLambda.Cert\n\nset_option maxRecDepth 100000\n\ndef %sP : Nat := %d\n\n"%(n*PER,n*PER+PER-1,M,PER,name,P)]
    for k in range(PER//4):
        txt.append("theorem %s_c%d : (List.range 4).all (fun j => rayMacroOK MPRAY %d %sP (%d + j)) = true := by decide +kernel\n"%(name,k,M,name,4*k))
    txt.append("\ntheorem %s_ok : ∀ j < %d, rayMacroOK MPRAY %d %sP j = true := by\n  have h := chunks_all (fun j => rayMacroOK MPRAY %d %sP j) %d (by\n    intro k hk\n    interval_cases k\n    exacts [%s])\n  exact h\n"%(name,PER,M,name,M,name,PER//4,", ".join("%s_c%d"%(name,k) for k in range(PER//4))))
    txt.append("\nend CatalanLambda.Cert\n")
    open(R+name+'.lean','w',encoding='utf-8',newline='\n').write("".join(txt))
print("modules",nmod,"macros",nmac,"cost units/cell",tot/(nmod*PER*M),"time",time.time()-t)
