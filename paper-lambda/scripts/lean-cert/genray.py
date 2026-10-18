import sys; sys.set_int_max_str_digits(0)
from mirror import *
R='./CatalanLambda/Cert/'
N=int(sys.argv[1]); name=sys.argv[2]
off=int(sys.argv[3]) if len(sys.argv)>3 else 0
cells=data['ray_cells']; st=len(cells)//N
sel=list(range(0,len(cells),st))[:N]
mp=F(197179,100000)
boxes=[mkbox(F(*cells[i][0]),F(*cells[i][1])) for i in sel]
assert all(box_lb(b,mp)>=mp for b in boxes)
def z(v): return "(%d : ℤ)"%v if v<0 else str(v)
def w(path, text):
    with open(path,'w',encoding='utf-8',newline=chr(10)) as f: f.write(text)
w(R+'SigmaData.lean',
  "import CatalanLambda.Cert.RayBox\n\n/-! Generated: sigma300 (X,Y scaled 2^40, masses n/2^32). -/\nnamespace CatalanLambda.Cert\n\ndef sigmaPts : List Pt := [\n"
  + ",\n".join("  (%s, %s, %d)"%(z(X),z(Y),n) for X,Y,n in pts) + "]\n\nend CatalanLambda.Cert\n")
flat=[v for b in boxes for v in b]
assert all(abs(v)<2**62 for v in flat)
P=sum((v+2**62)<<(64*k) for k,v in enumerate(flat))
w(R+name+'.lean',
  "/-! Generated: %d ray boxes (stride %d of the 26977 cells of cert_K300_data.json), 4 signed ints per box biased by 2^62 in 64-bit slots. -/\nnamespace CatalanLambda.Cert\n\ndef %sPacked : Nat := %d\n\nend CatalanLambda.Cert\n"%(len(boxes),st,name,P))
print(len(boxes))
