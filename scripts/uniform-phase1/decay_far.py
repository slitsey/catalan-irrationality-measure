"""Exact rational source-cluster multipoles and larger-cell validation."""
from decay_common import *
from decay_emit import emit
import time,copy
ctx.prec=384
ORDER=8;L=12
class Cluster:
    def __init__(self,pieces,indices):
        self.ps=pieces;self.ids=indices
        xs=[p[k][0]for p in pieces for k in(0,1)];ys=[p[k][1]for p in pieces for k in(0,1)]
        self.c=((min(xs)+max(xs))/2,(min(ys)+max(ys))/2)
        self.R=max(abs(p[k][0]-self.c[0])+abs(p[k][1]-self.c[1])for p in pieces for k in(0,1))
        self.TV=Q(0)
        for a,b,cs in pieces:
            n=len(cs)-1;bs=[sum((cs[k]*Q(comb(j,k),comb(n,k))for k in range(j+1)),Q(0))for j in range(n+1)]
            self.TV+=sum(map(abs,bs),Q(0))/len(bs)
        self.children=[];self._mom=None
        if len(pieces)>1:
            axis=0 if max(xs)-min(xs)>=max(ys)-min(ys)else 1
            order=sorted(range(len(pieces)),key=lambda i:pieces[i][0][axis]+pieces[i][1][axis]);mid=len(order)//2
            self.children=[Cluster([pieces[i]for i in part],[indices[i]for i in part])for part in(order[:mid],order[mid:])]
    def moments(self):
        if self._mom is None:
            ms=[(Q(0),Q(0))for _ in range(L+1)]
            for a,b,cs in self.ps:
                d=S.sub(a,self.c);v=S.sub(b,a)
                for k in range(L+1):
                    for j in range(k+1):
                        integral=sum((cv/Q(j+l+1)for l,cv in enumerate(cs)),Q(0))
                        ms[k]=S.za(ms[k],S.zc(S.zm(S.zp(d,k-j),S.zp(v,j)),comb(k,j)*integral))
            self._mom=ms
        return self._mom

def choose(tree,z,blockR,tolerance,totalTV):
    D=S.sub(z,tree.c);dist=max(map(abs,D))-blockR
    if dist>tree.R:
        r=tree.R/dist;error=tree.TV*r**(L+1)/((L+1)*(1-r))
        if r<Q(1,3)and error<=tolerance*tree.TV/totalTV:return[tree],[],error
    if not tree.children:return[],list(tree.ids),Q(0)
    far=[];near=[];err=Q(0)
    for child in tree.children:
        f,n,e=choose(child,z,blockR,tolerance,totalTV);far+=f;near+=n;err+=e
    return far,near,err

def coefficients(cluster,z,direction,h):
    D=S.sub(z,cluster.c);q=S.zd(direction,D);mom=cluster.moments();mass=mom[0][0];assert mom[0][1]==0
    co=[S.Expr()for _ in range(ORDER)];co[0]+=S.Expr(terms={('log',S.norm2(D)):-mass/2})
    terms=[S.zc(S.zd(mom[k],S.zp(D,k)),Q(1,k))for k in range(1,L+1)]
    co[0]+=sum(v[0]for v in terms)
    for j in range(1,ORDER):
        qj=S.zp(q,j);co[j]+=-mass*Q((-1)**(j+1),j)*qj[0]
        for k,A0 in enumerate(terms,1):co[j]+=S.zm(A0,qj)[0]*((-1)**j)*comb(k+j-1,j)
    rho=(abs(q[0])+abs(q[1]))*h;assert rho<1
    error=abs(mass)*rho**ORDER/(ORDER*(1-rho))
    for k,A0 in enumerate(terms,1):error+=(abs(A0[0])+abs(A0[1]))*comb(k+ORDER-1,ORDER)*rho**ORDER/(1-rho)**(k+ORDER)
    return[x*h**j for j,x in enumerate(co)],error

def bernstein(co):
    powers=[sum((co[k]*Q(comb(k,j)*2**j*(-1)**(k-j))for k in range(j,ORDER)),S.Expr())for j in range(ORDER)]
    return[sum((powers[k]*Q(comb(j,k),comb(ORDER-1,k))for k in range(j+1)),S.Expr())for j in range(ORDER)]
def main():
    started=time.monotonic();row=getrow('chi3');f=Field(row);c=(f.ys[1]+f.ys[2])/2;h=Q(1,1000);f.active=c;z=f.point('ray',c);direction=f.direction('ray')
    tree=Cluster(f.pieces,list(range(len(f.pieces))))
    far,near,error=choose(tree,z,h*sum(map(abs,direction)),Q(1,10**10),tree.TV)
    nearfield=copy.copy(f);nearfield.pieces=[f.pieces[i]for i in near]
    co=S.point_jets(nearfield,'ray',c,h,ORDER);tayerror=Q(0)
    for cluster in far:
        cs,err=coefficients(cluster,z,direction,h);co=[a+f.b*b for a,b in zip(co,cs)];tayerror+=f.b*err
    data=jets(nearfield,'ray',c,h,ORDER);assert data is not None
    nearerror=upper_q(data[1]);wholeerror=f.b*error+tayerror+nearerror
    bs=bernstein(co)
    # Independent Arb direct potential controls for real full signed114piece field.
    for offset in(Q(-1),Q(0),Q(1)):
        t=c+offset*h;zz=f.point('ray',t);approx=sum((ex.value()*A(offset**j)for j,ex in enumerate(co)),arb(0));direct=f.evaluate('ray',t)
        assert abs(approx-direct)<=A(wholeerror),(offset,approx,direct,wholeerror)
    bound=f.bound('ray',c-h,c+h)
    assert bound is not None
    compressed_lower=min(-upper_q(-ex.value())for ex in bs)-wholeerror
    report=dict(compressed_cell_lower=str(compressed_lower),compressed_cell_accepted=bool(compressed_lower>f.targets['ray']),error_magnitudes_F=dict(multipole=float(f.b*error),Taylor=float(tayerror),near=float(nearerror),total=float(wholeerror)),source_sha256=hashlib.sha256(SOURCE.read_bytes()).hexdigest(),full_pieces=len(f.pieces),near_pieces=len(near),near_indices=near,far_clusters=len(far),cluster_sizes=[len(t.ids)for t in far],multipole_order=L,logjet_order=ORDER,cell_center=str(c),cell_half_width=str(h),original_pilot_half_width='1/10000000',nearest_endpoint_distance_lower_F=min(float(abs(C(S.sub(z,e))))for p in f.pieces for e in p[:2]),uniform_multipole_error_upper=str(f.b*error),rational_Taylor_error_upper=str(tayerror),near_jet_error_upper=str(nearerror),total_error_upper=str(wholeerror),larger_cell_lower=str(-upper_q(-bound[0])),target=str(f.targets['ray']),larger_cell_accepted=bool(bound[0]>A(f.targets['ray'])),seconds=time.monotonic()-started,scope='Exact arithmetic and independent direct Arb controls. Generic multipole analytic soundness remains a Phase2 obligation; no HasDecay asserted.')
    emit('Far',bs,report)
    compact=Field(row,'12');compact.active=c;compactco=S.point_jets(compact,'ray',c,h,ORDER)
    emit('Compact',bernstein(compactco),dict(source_sha256=report['source_sha256'],pieces=len(compact.pieces),cell_half_width=str(h),order=ORDER,variant='chi3 compact12',scope='Real compact trial potential arithmetic, analytic transfer pending'))
    (EVID/'far-field-validation.json').write_text(json.dumps(report,indent=2)+'\n');print('FAR_VALIDATED '+json.dumps({k:v for k,v in report.items()if k not in ('uniform_multipole_error_upper','rational_Taylor_error_upper','near_jet_error_upper','total_error_upper','compressed_cell_lower')}),flush=True)
if __name__=='__main__':main()

