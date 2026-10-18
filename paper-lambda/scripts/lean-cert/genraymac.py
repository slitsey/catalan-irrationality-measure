import sys, json; sys.set_int_max_str_digits(0)
from mirror2 import *
R='./CatalanLambda/Cert/'
BIAS=2**62
mp=F(197179,100000)
_boxes=None
def allboxes():
    global _boxes
    if _boxes is None: _boxes=[mkbox(F(*a),F(*b)) for a,b in data['ray_cells']]
    return _boxes
def macro_slots(bs,M):
    bs=bs+[bs[-1]]*(M-len(bs))
    c=macro_choose(bs,ray_rest,mp)
    _,x0,y0,i0,i1=c
    sl=[x0,y0,i0,i1]
    for b in bs: sl+=list(b)
    return sl,c
def pack(slots):
    assert all(abs(v)<BIAS for v in slots)
    return sum((v+BIAS)<<(64*k) for k,v in enumerate(slots))
def write(name,macros_idx,M,comment):
    boxes=allboxes(); allsl=[]; cost=0
    for mi in macros_idx:
        sl,c=macro_slots(boxes[mi*M:mi*M+M],M); allsl+=sl; cost+=c[0]
    P=pack(allsl)
    with open(R+name+'.lean','w',encoding='utf-8',newline='\n') as f:
        f.write("/-! Generated (genraymac.py): %s; M=%d, %d macros. -/\nnamespace CatalanLambda.Cert\n\ndef %sPacked : Nat := %d\n\nend CatalanLambda.Cert\n"%(comment,M,len(macros_idx),name,P))
    return cost
if __name__=="__main__":
    M=int(sys.argv[1]); nm=int(sys.argv[2]); name=sys.argv[3]
    nmac=(len(allboxes())+M-1)//M
    idx=[ (k*nmac)//nm for k in range(nm)]
    cost=write(name,idx,M,"timing test")
    print("macros",idx,"cost units/cell",cost/(nm*M))
