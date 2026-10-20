from pathlib import Path
import importlib.util,json
spec=importlib.util.spec_from_file_location('pilot',str(Path(__file__).with_name('research-pilots.py')));P=importlib.util.module_from_spec(spec);spec.loader.exec_module(P)
mat=P.matrix
def solve(cols,y,p):
 if not cols:return [] if not any(y) else None
 A=[[int(c[i])%p for c in cols]+[int(y[i])%p] for i in range(len(y))];n=len(cols);row=0;pivs=[]
 for j in range(n):
  k=next((i for i in range(row,len(A)) if A[i][j]),None)
  if k is None:continue
  A[row],A[k]=A[k],A[row];a=pow(A[row][j],-1,p);A[row]=[a*x%p for x in A[row]]
  for i in range(len(A)):
   if i!=row:
    a=A[i][j];A[i]=[(x-a*y)%p for x,y in zip(A[i],A[row])]
  pivs.append(j);row+=1
 if any(not any(a[:n]) and a[n] for a in A):return None
 ans=[0]*n
 for i,j in enumerate(pivs):ans[j]=A[i][n]
 return ans
def run(r,m,p,o,u):
 out,D=P.run(r,m,p,str(o),u,True)
 if out.get('exceptional'):return out
 X,Y,R,M=D['X'],D['Y'],D['R'],D['M'];F=R.prefix
 red=lambda a:int(a.p)%p*pow(int(a.q)%p,-1,p)%p
 h=o*pow(4,-1,p)%p
 cuts=[r]+[z for z in range(r+1,r+2*m) if z*(4*z-o)%p==0]+[r+2*m]
 aa,bb=max(zip(cuts,cuts[1:]),key=lambda t:t[1]-t[0]);ix=[i for i,x in enumerate(X) if aa<=x<bb];iy=[j for j,y in enumerate(Y) if aa<=y<bb]
 if bb-aa<=m:return out
 islong=((aa+bb-1)/2)%p>=h if h<p/2 else ((aa+bb-1)/2)%p<h
 if not islong:return out
 regions=list(zip(sorted(set([0,h,r%p,p])),sorted(set([0,h,r%p,p]))[1:]))
 z=X[ix[0]];C=[i for i in range(r) if i%p==z%p]
 Q=D['A0'];Qc=mat(C,C,lambda i,j:int(Q[i,j]),p)
 b=mat([z],C,lambda a,b:red(p*p*R(a,b)),p);g=b*Qc.inv()
 A=(red(p*F[z])-sum(int(g[0,j])*red(p*F[c]) for j,c in enumerate(C)))%p
 B=(1-sum(int(g[0,j]) for j in range(len(C))))%p
 def response(c):
  I=[i for i in range(r) if i%p==c]
  if not I:return 0
  Qc=mat(I,I,lambda i,j:int(Q[i,j]),p);v=mat([0],I,lambda _,i:A-B*red(p*F[i]),p)
  return int((v*Qc.inv()*v.transpose())[0,0])
 cC=response(z%p);columns=[];pred=[];labels=[]
 for lo,hi in regions:
  if lo<=z%p<hi:continue
  S=range(lo,hi)
  G=mat(ix,iy,lambda i,j:sum(pow((c-X[i])*(c-Y[j])%p,-1,p) for c in S),p)
  columns.append([int(G[i,j]) for i in range(len(ix)) for j in range(len(iy))]);labels.append((lo,hi))
  c=response(lo);short=(lo<h) if h<p/2 else (lo>=h);sgn=1 if h<p/2 else -1
  pred.append(((cC-c)+(sgn*B*B if short else 0))*pow(16,-1,p)%p)
 raw=[int(M[i,j])//p for i in ix for j in iy]
 coeff=solve(columns,raw,p)
 free=[c for c in range(p) if c not in {x%p for x in X+Y}]
 short=lambda c:(c<h) if h<p/2 else (c>=h)
 weight=lambda c:((cC-response(c))+((1 if h<p/2 else -1)*B*B if short(c) else 0))*pow(16,-1,p)%p
 free_short_weights={weight(c) for c in free if short(c)}
 out.update(weighted_regions=labels,weighted_coefficients=coeff,predicted_coefficients=pred,weighted_fit=coeff is not None,
   predicted_fit=all(sum(col[i]*v for col,v in zip(columns,pred))%p==raw[i] for i in range(len(raw))),A=A,B=B,cC=cC,
   free_long_zero=all(weight(c)==0 for c in free if not short(c)),free_short_constant=len(free_short_weights)<=1,
   pole_jumps_nonzero=all(red(p*F[x])!=red(p*F[z]) for x in X+Y if not aa<=x<bb))
 return out
if __name__=='__main__':
 for r,m,p,o in [(64,8,29,1),(128,16,43,1),(128,16,59,1),(128,16,53,1),(128,16,41,1),(128,16,47,3),(192,24,83,1),(192,24,97,1),(192,24,101,1)]:
  for u in [2,3,5]:print(json.dumps(run(r,m,p,o,u)),flush=True)
