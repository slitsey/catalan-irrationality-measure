from pathlib import Path
import sys,json,time
from flint import fmpq,nmod_mat

def matrix(rs,cs,f,q):return nmod_mat(len(rs),len(cs),[f(i,j)%q for i in rs for j in cs],q)
def rational_frame(r,m,kind):
 N=r+2*m;F=[fmpq(0)];P=[fmpq(0)]
 for k in range(1,N):
  if kind=='p6':
   d=fmpq(1,k)+fmpq(6,3*k-2)-fmpq(6,2*k-1)
   e=fmpq(1,k*k)+fmpq(18,(3*k-2)**2)-fmpq(12,(2*k-1)**2);norm=36
  else:
   o=int(kind);d=(fmpq(1,k)-fmpq(4,4*k-o))/4
   e=(fmpq(1,k*k)-fmpq(16,(4*k-o)**2))/4;norm=4
  F.append(F[-1]+d);P.append(P[-1]+e)
 def R(a,b):return P[a]/norm if a==b else (F[a]-F[b])/(norm*(b-a))
 R.prefix=F
 return R
def run(r,m,p,kind,u,detail=False):
 R=rational_frame(r,m,kind);q=p**3
 def red(a):return int(a.p)%q*pow(int(a.q)%q,-1,q)%q
 def b(i,j):return red(p*p*R(i,j))
 C=range(r);X=list(range(r,r+2*m,2));Y=[x+1 for x in X]
 A=matrix(C,C,lambda i,j:b(i,j)+(u if i==j else 0),q)
 A0=matrix(C,C,lambda i,j:int(A[i,j]),p)
 try:B=A0.inv()
 except ZeroDivisionError:return dict(r=r,m=m,p=p,kind=kind,u=u,exceptional=True)
 Ai=matrix(C,C,lambda i,j:int(B[i,j]),q)
 I=matrix(C,C,lambda i,j:int(i==j),q)
 for _ in range(2):Ai=Ai*(2*I-A*Ai)
 assert A*Ai==I
 D=matrix(X,Y,b,q)-matrix(X,C,b,q)*Ai*matrix(C,Y,b,q)
 assert all(int(D[i,j])%p==0 for i in range(m) for j in range(m))
 M=matrix(range(m),range(m),lambda i,j:int(D[i,j])//p,p*p)
 M0=matrix(range(m),range(m),lambda i,j:int(M[i,j]),p)
 RB,n=M0.nullspace();LB,n2=M0.transpose().nullspace();assert n==n2
 L=matrix(range(n),range(m),lambda i,j:int(LB[j,i]),p*p)
 RR=matrix(range(m),range(n),lambda i,j:int(RB[i,j]),p*p)
 E=L*M*RR
 assert all(int(E[i,j])%p==0 for i in range(n) for j in range(n))
 N=matrix(range(n),range(n),lambda i,j:int(E[i,j])//p,p)
 out=dict(r=r,m=m,p=p,kind=kind,u=u,leading_corank=n,next_rank=N.rank(),extra=n-N.rank())
 if kind!='p6':
  o=int(kind);h=(o*pow(4,-1,p))%p
  short=list(range(h)) if h<p/2 else list(range(h,p))
  free=[c for c in short if c not in {z%p for z in X+Y}]
  W=matrix(X,free,lambda x,c:pow((c-x)%p,-1,p),p)
  V=matrix(Y,free,lambda y,c:pow((c-y)%p,-1,p),p)
  L0=matrix(range(n),range(m),lambda i,j:int(LB[j,i]),p)
  R0=matrix(range(m),range(n),lambda i,j:int(RB[i,j]),p)
  PW=L0*W;QV=V.transpose()*R0;G=PW*QV
  piv=next(((i,j) for i in range(n) for j in range(n) if int(G[i,j])),None)
  k=int(N[piv[0],piv[1]])*pow(int(G[piv[0],piv[1]]),-1,p)%p if piv else 0
  fit=N==k*G
  colcat=matrix(range(n),range(len(free)+n),lambda i,j:int(PW[i,j]) if j<len(free) else int(N[i,j-len(free)]),p)
  rowcat=matrix(range(len(free)+n),range(n),lambda i,j:int(QV[i,j]) if i<len(free) else int(N[i-len(free),j]),p)
  out.update(b=len(free),predicted_extra=max(0,n-len(free)),scalar_fit=fit,kappa=k,column_inclusion=colcat.rank()==PW.rank(),row_inclusion=rowcat.rank()==QV.rank())
  cuts=[r]+[z for z in range(r+1,r+2*m) if z*(4*z-o)%p==0]+[r+2*m]
  aa,bb=max(zip(cuts,cuts[1:]),key=lambda t:t[1]-t[0])
  islong=((aa+bb-1)/2)%p>=h if h<p/2 else ((aa+bb-1)/2)%p<h
  ix=[i for i,x in enumerate(X) if aa<=x<bb];iy=[j for j,y in enumerate(Y) if aa<=y<bb]
  if bb-aa>m and islong:
   assert all(int(M[i,j])%p==0 for i in ix for j in iy)
   raw=matrix(ix,iy,lambda i,j:int(M[i,j])//p,p)
   gram=matrix(ix,iy,lambda i,j:sum(pow((c-X[i])*(c-Y[j])%p,-1,p) for c in short),p)
   piv=next(((i,j) for i in range(len(ix)) for j in range(len(iy)) if int(gram[i,j])),None)
   kk=int(raw[piv[0],piv[1]])*pow(int(gram[piv[0],piv[1]]),-1,p)%p if piv else 0
   out['raw_sameclass_scalar_fit']=raw==kk*gram
   out['raw_sameclass_kappa']=kk
   if raw!=kk*gram:
    i,j=next((i,j) for i in range(len(ix)) for j in range(len(iy)) if int(raw[i,j])!=kk*int(gram[i,j])%p)
    out['raw_counterexample']=dict(pivot=[X[ix[piv[0]]],Y[iy[piv[1]]],int(raw[piv[0],piv[1]]),int(gram[piv[0],piv[1]])],mismatch=[X[ix[i]],Y[iy[j]],int(raw[i,j]),int(gram[i,j])])
 if detail:return out,dict(R=R,M=M,M0=M0,A0=A0,X=X,Y=Y,LB=LB,RB=RB)
 return out
if __name__=='__main__':
 cases=[(64,8,29,'1'),(128,16,43,'1'),(128,16,59,'1'),(128,16,53,'1'),(128,16,41,'1'),(64,8,23,'1'),(64,8,19,'3'),(128,16,47,'3'),(128,16,61,'3')]
 cases += [(64,8,p,'p6') for p in [19,23,29,31,37,41,43,47,53]]
 for r,m,p,k in cases:
  for u in [1,2,3]:
   t=time.time();o=run(r,m,p,k,u);o['seconds']=round(time.time()-t,3);print(json.dumps(o),flush=True)
