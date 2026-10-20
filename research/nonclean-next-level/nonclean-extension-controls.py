from pathlib import Path
import importlib.util,json,time
spec=importlib.util.spec_from_file_location('pilot',str(Path(__file__).with_name('research-pilots.py')));P=importlib.util.module_from_spec(spec);spec.loader.exec_module(P)
mat=P.matrix

def run(r,m,p,o,u,v):
 q=p**3;R=P.rational_frame(r,m,str(o));F=R.prefix
 d=next(d for d in range(2,p) if pow(d,(p-1)//2,p)==p-1)
 def red(a,mod):return int(a.p)%mod*pow(int(a.q)%mod,-1,mod)%mod
 def ent(i,j):return red(p*p*R(i,j),q)
 C=list(range(r));X=list(range(r,r+2*m,2));Y=[x+1 for x in X]
 A=mat(C,C,lambda i,j:ent(i,j)+(u if i==j else 0),q)
 I=mat(C,C,lambda i,j:int(i==j),q)
 B=A*A-(v*v*d)*I
 Bp=mat(C,C,lambda i,j:int(B[i,j]),p)
 try:Bi0=Bp.inv()
 except ZeroDivisionError:return dict(exceptional=True,r=r,m=m,p=p,o=o,u=u,v=v)
 Bi=mat(C,C,lambda i,j:int(Bi0[i,j]),q)
 for _ in range(2):Bi=Bi*(2*I-B*Bi)
 assert B*Bi==I
 Ar=A*Bi;Ai=-v*Bi
 assert A*Ar+(d*v)*Ai==I and A*Ai+v*Ar==0*I
 Cx=mat(X,C,ent,q);By=mat(C,Y,ent,q)
 Dr=mat(X,Y,ent,q)-Cx*Ar*By;Di=-Cx*Ai*By
 h=o*pow(4,-1,p)%p;short=set(range(h)) if h<p/2 else set(range(h,p));sgn=1 if h<p/2 else -1
 cuts=[r]+[z for z in range(r+1,r+2*m) if z*(4*z-o)%p==0]+[r+2*m]
 aa,bb=max(zip(cuts,cuts[1:]),key=lambda t:t[1]-t[0])
 if bb-aa<=m or ((aa+bb-1)/2)%p in short:return dict(outside=True,r=r,m=m,p=p,o=o,u=u,v=v)
 ix=[i for i,x in enumerate(X) if aa<=x<bb];iy=[j for j,y in enumerate(Y) if aa<=y<bb];z=X[ix[0]]
 add=lambda a,b:((a[0]+b[0])%p,(a[1]+b[1])%p)
 sub=lambda a,b:((a[0]-b[0])%p,(a[1]-b[1])%p)
 mul=lambda a,b:((a[0]*b[0]+d*a[1]*b[1])%p,(a[0]*b[1]+a[1]*b[0])%p)
 scale=lambda a,k:(a[0]*k%p,a[1]*k%p)
 def inv_chain(c):
  ids=[i for i in C if i%p==c]
  a=mat(ids,ids,lambda i,j:ent(i,j)+(u if i==j else 0),p)
  e=mat(ids,ids,lambda i,j:int(i==j),p)
  bi=(a*a-(v*v*d)*e).inv()
  return ids,a*bi,-v*bi
 ids,qr,qi=inv_chain(z%p)
 b=mat([z],ids,lambda z,i:red(p*p*R(z,i),p),p)
 gr=b*qr;gi=b*qi
 g=[(int(gr[0,j]),int(gi[0,j])) for j in range(len(ids))]
 B0=(1,0);A0=(red(p*F[z],p),0)
 for c,gc in zip(ids,g):
  B0=sub(B0,gc);A0=sub(A0,scale(gc,red(p*F[c],p)))
 def response(c):
  ids,qr,qi=inv_chain(c)
  vec=[sub(A0,scale(B0,red(p*F[i],p))) for i in ids]
  out=(0,0)
  for i in range(len(ids)):
   for j in range(len(ids)):
    out=add(out,mul(mul(vec[i],(int(qr[i,j]),int(qi[i,j]))),vec[j]))
  return out
 cc=response(z%p)
 w={c:scale(add(sub(cc,response(c)),scale(mul(B0,B0),sgn if c in short else 0)),pow(16,-1,p)) for c in range(p)}
 occupied={t%p for t in X+Y};free=[c for c in range(p) if c not in occupied]
 assert all(w[c]==(0,0) for c in free if c not in short)
 assert len({w[c] for c in free if c in short})<=1
 for i in ix:
  for j in iy:
   dr,di=int(Dr[i,j]),int(Di[i,j]);assert dr%(p*p)==di%(p*p)==0
   observed=(dr//(p*p)%p,di//(p*p)%p);pred=(0,0)
   for c in range(p):
    if c in {X[i]%p,Y[j]%p}:continue
    pred=add(pred,scale(w[c],pow((c-X[i])*(c-Y[j])%p,-1,p)))
   assert observed==pred,(r,m,p,o,u,v,X[i],Y[j],observed,pred)
 return dict(r=r,m=m,p=p,o=o,u=u,v=v,nonsquare=d,entries=len(ix)*len(iy),weighted_identity=True,free_geometry=True)

if __name__=='__main__':
 cases=[(64,8,29,1),(128,16,43,1),(128,16,59,1),(128,16,53,1),(128,16,41,1),(64,8,23,1),(64,8,19,3),(128,16,47,3),(128,16,61,3)]
 records=[]
 for args in cases:
  for u,v in [(0,1),(1,1),(2,3)]:
   start=time.time();out=run(*args,u,v);out['seconds']=round(time.time()-start,3);records.append(out);print(json.dumps(out),flush=True)
 Path(__file__).with_name('nonclean-extension-controls.json').open('w').write(json.dumps(records,indent=2))
 print('ALL QUADRATIC EXTENSION CONTROLS PASSED',sum(x.get('weighted_identity',False) for x in records),flush=True)
