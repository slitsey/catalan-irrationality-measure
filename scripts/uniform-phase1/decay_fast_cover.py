"""Directed-Arb assembly of the exact-moment compressed cover, avoiding giant common denominators."""
from decay_common import *
from decay_far import Cluster,ORDER,L
import decay_cover as cover
import copy

def chooseFast(tree,z,blockR,tolerance,totalTV):
    D=S.sub(z,tree.c);dist=A(max(map(abs,D))-blockR)
    if dist>A(tree.R):
        r=A(tree.R)/dist;error=A(tree.TV)*r**(L+1)/((L+1)*(1-r))
        if r<A(Q(1,3))and error<=A(tolerance*tree.TV/totalTV):return[tree],[],error
    if not tree.children:return[],list(tree.ids),arb(0)
    far=[];near=[];error=arb(0)
    for child in tree.children:
        f,n,e=chooseFast(child,z,blockR,tolerance,totalTV);far+=f;near+=n;error+=e
    return far,near,error

def fastCoefficients(cluster,z,direction,h):
    if not hasattr(cluster,'arbMom'):cluster.arbMom=[C(m)for m in cluster.moments()]
    D=C(S.sub(z,cluster.c));q=C(direction)/D;mass=cluster.arbMom[0].real
    co=[acb(0)for _ in range(ORDER)];co[0]=-mass*abs(D).log()
    terms=[cluster.arbMom[k]/(k*D**k)for k in range(1,L+1)]
    co[0]+=sum(terms,acb(0))
    for j in range(1,ORDER):
        qj=q**j;co[j]+=-mass*((-1)**(j+1))*qj/j
        for k,ak in enumerate(terms,1):co[j]+=ak*qj*((-1)**j)*comb(k+j-1,j)
    rho=abs(q)*A(h)
    if not rho<1:return None
    error=abs(mass)*rho**ORDER/(ORDER*(1-rho))
    for k,ak in enumerate(terms,1):error+=abs(ak)*comb(k+ORDER-1,ORDER)*rho**ORDER/(1-rho)**(k+ORDER)
    return[x.real*A(h**j)for j,x in enumerate(co)],error

class FastField(Field):
    def __init__(self,row,variant='baseline'):
        super().__init__(row,variant);self.tree=Cluster(self.pieces,list(range(len(self.pieces))));self.stats=[]
    def bound(self,kind,lo,hi,n=8):
        c=(lo+hi)/2;h=(hi-lo)/2;self.active=c;z=self.point(kind,c);direction=self.direction(kind)
        far,near,mpError=chooseFast(self.tree,z,h*sum(map(abs,direction)),Q(1,10**10),self.tree.TV)
        nf=copy.copy(self);nf.pieces=[self.pieces[i]for i in near]
        farco=[arb(0)for _ in range(ORDER)];tail=A(self.b)*mpError
        for cluster in far:
            value=fastCoefficients(cluster,z,direction,h)
            if value is None:return None
            cs,error=value;farco=[a+A(self.b)*b for a,b in zip(farco,cs)];tail+=A(self.b)*error
        data=jets(nf,kind,c,h,ORDER);self.stats.append((len(near),len(far)))
        if data is None:
            nb=Field.bound(nf,kind,lo,hi,n)
            if nb is None:return None
            fr=bernstein_range(farco,Q(1));return nb[0]+fr-tail,nb[1]+fr+tail,'endpoint-multipole',float(tail)+nb[3]
        co,nearError=data;total=[co[j]*A(h**j)+farco[j]for j in range(ORDER)]
        br=bernstein_range(total,Q(1));error=nearError+tail
        return br-error,br+error,'multipole-logjet8',float(error)

def main(frame,variant):
    destination=EVID/'fast-covers';destination.mkdir(exist_ok=True)
    cover.Field=FastField;cover.EVID=destination;cover.run(frame,variant)
    path=destination/f'cover-{frame}-{variant}.json';record=json.loads(path.read_text())
    record['policy']='DirectedArb assembly from exact signed source moments; order12multipoles/order8queryjets; endpoint-near-only modulus; fresh unions up to8'
    record['kernel_model']={'status':'C pending measured per-frame full compressed arithmetic closure'}
    path.write_text(json.dumps(record,indent=2)+'\n')
if __name__=='__main__':main(*sys.argv[1:3])
