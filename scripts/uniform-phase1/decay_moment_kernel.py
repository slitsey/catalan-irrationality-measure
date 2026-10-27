"""Cold integer-cleared source-moment certificate preparation, with structural normalization."""
from decay_common import *
from decay_far import Cluster,L as ORDER
import math,functools,time
sys.set_int_max_str_digits(0)
def gcdall(xs):return functools.reduce(math.gcd,map(abs,xs),0)or 1
def zadd(a,b):return(a[0]+b[0],a[1]+b[1])
def zmul(a,b):return(a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def zscale(a,z):return(a*z[0],a*z[1])
def zpow(z,n):
    p=(1,0)
    for _ in range(n):p=zmul(p,z)
    return p

def main(frame,variant,label):
    started=time.monotonic();f=Field(getrow(frame),variant);P=f.pieces;root=Cluster(P,list(range(len(P))))
    nodes=[]
    def collect(node):nodes.append(node);[collect(c)for c in node.children]
    collect(root)
    Qscale=2*math.lcm(*(c.denominator for a,b,cs in P for c in a+b));Dscale=math.lcm(*(c.denominator for a,b,cs in P for c in cs));Lscale=math.lcm(*range(1,18))
    pieces=[];normalized_zeros=0;original_zeros=0
    for a,b,cs in P:
        ai=tuple(int(x*Qscale)for x in a);vi=tuple(int(x*Qscale)for x in S.sub(b,a));geo=gcdall(ai+vi);an=tuple(x//geo for x in ai);vn=tuple(x//geo for x in vi)
        ci=[int(c*Dscale)for c in cs];dens=gcdall(ci);cn=[x//dens for x in ci]
        iw=[sum(cn[ell]*(Lscale//(j+ell+1))for ell in range(len(cn)))for j in range(ORDER+1)]
        assert all(Lscale%(j+ell+1)==0 for j in range(ORDER+1)for ell in range(len(cn)))
        moments=[]
        for k in range(ORDER+1):
            m=(0,0)
            for j in range(k+1):m=zadd(m,zscale(math.comb(k,j)*iw[j],zmul(zpow(an,k-j),zpow(vn,j))))
            moments.append(m)
            original_zeros+=sum(int(x*dens*geo**k)%2**64==0 and x!=0 for x in m);normalized_zeros+=sum(x%2**64==0 and x!=0 for x in m)
        pieces.append(dict(a=an,v=vn,geo=geo,dens=dens,cs=cn,iw=iw,moments=moments))
    node_data=[]
    for node in nodes:
        centre=tuple(int(v*Qscale)for v in node.c);geo=gcdall([pieces[i]['geo']for i in node.ids]+list(centre));dens=gcdall(pieces[i]['dens']for i in node.ids);cn=tuple(x//geo for x in centre)
        raw=[];centered=[]
        for k in range(ORDER+1):
            s=(0,0)
            for i in node.ids:s=zadd(s,zscale((pieces[i]['dens']//dens)*(pieces[i]['geo']//geo)**k,pieces[i]['moments'][k]))
            raw.append(s)
            m=(0,0)
            for j in range(k+1):m=zadd(m,zscale(math.comb(k,j),zmul(zpow((-cn[0],-cn[1]),k-j),raw[j])))
            centered.append(m)
        # Independent existing rational polynomial moment implementation.
        actual=node.moments()
        for k,(m,qm)in enumerate(zip(centered,actual)):
            scale=Q(Dscale*Lscale*Qscale**k,dens*geo**k)
            assert tuple(Q(x)*scale for x in qm)==m
        node_data.append(dict(ids=node.ids,geo=geo,dens=dens,centre=cn,raw=raw,centered=centered))
    out=WORK/'CatalanCore/Uniform/Decay/Optimization'
    arithmetic='''import CatalanCore.Uniform.Decay.PilotArithmetic
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1
namespace CatalanCore.Uniform.Decay.Optimization.Moments
abbrev Z := Int × Int
def za (a b : Z) : Z := (a.1+b.1,a.2+b.2)
def zm (a b : Z) : Z := (a.1*b.1-a.2*b.2,a.1*b.2+a.2*b.1)
def zsc (a : Int) (z : Z) : Z := (a*z.1,a*z.2)
def zp (a : Z) : Nat → Z
  | 0 => (1,0)
  | n+1 => zm a (zp a n)
def zTape : List Int → List Z
  | a::b::xs => (a,b)::zTape xs
  | _ => []
def linearAux (a v previous : Z) : List Z → List Z
  | [] => [zm v previous]
  | x::xs => za (zm a x) (zm v previous)::linearAux a v x xs
def linearPower (a v : Z) : Nat → List Z
  | 0 => [(1,0)]
  | n+1 => linearAux a v (0,0) (linearPower a v n)
def dotWeights (p : List Z) (ws : List Int) : Z :=
  match p,ws with
  | [],_ => (0,0)
  | _,[] => (0,0)
  | x::xs,w::ws => za (zsc w x) (dotWeights xs ws)
termination_by structural p
def integralWeights (L : Nat) (cs : List Int) : List Int :=
  (List.range 13).map (fun j => cs.zipIdx.foldl (fun acc x => acc+x.1*(L/(j+x.2+1) : Nat)) 0)
def rawMoment (a v : Z) (ws : List Int) (k : Nat) : Z := dotWeights (linearPower a v k) ws
def adjacent : List Nat → List Nat
  | a::b::xs => (a+b)::adjacent (b::xs)
  | _ => []
def chooseRow : Nat → List Nat
  | 0 => [1]
  | n+1 => 1::(adjacent (chooseRow n) ++ [1])
def centeredMoment (c : Z) (k : Nat) (raw : List Z) : Z :=
  (raw.take (k+1)).zipIdx.foldl (fun acc x =>
    za acc (zsc ((chooseRow k).getD x.2 0 : Int) (zm (zp (-c.1,-c.2) (k-x.2)) x.1))) (0,0)
end CatalanCore.Uniform.Decay.Optimization.Moments
'''
    arith=out/'MomentArithmetic.lean'
    if not arith.exists():arith.write_text(arithmetic,encoding='utf8')
    from decay_emit import raw
    lines=['import CatalanCore.Uniform.Decay.Optimization.MomentArithmetic','set_option Elab.async false','set_option profiler true','set_option profiler.threshold 1','set_option maxRecDepth 100000','set_option maxHeartbeats 0',f'namespace CatalanCore.Uniform.Decay.Optimization.{label}','open CatalanCore.Uniform.Decay.Optimization.Moments']
    for i,p in enumerate(pieces):
        lines +=[raw(f'a{i}Tape',p['a']),raw(f'v{i}Tape',p['v']),f'def a{i} : Z := ((a{i}Tape.getD 0 0),(a{i}Tape.getD 1 0))',f'def v{i} : Z := ((v{i}Tape.getD 0 0),(v{i}Tape.getD 1 0))',raw(f'coeff{i}',p['cs']),raw(f'iw{i}',p['iw']),f'theorem iw{i}_check : integralWeights {Lscale} coeff{i} = iw{i} := by decide +kernel',raw(f'moment{i}Tape',[x for m in p['moments']for x in m]),f'def moments{i} : List Z := zTape moment{i}Tape']
        for k in range(ORDER+1):lines +=[f'theorem p{i}m{k} : rawMoment a{i} v{i} iw{i} {k} = moments{i}.getD {k} (0,0) := by decide +kernel']
    # A node's member weights restore exactly the factored coordinate/density scales.
    for node_id,node in enumerate(node_data):
        for k in range(ORDER+1):
            terms=[f'zsc (({pieces[i]["dens"]//node["dens"]} : Int) * ({pieces[i]["geo"]//node["geo"]} : Int)^{k}) (moments{i}.getD {k} (0,0))'for i in node['ids']]
            expr='(0,0)'
            for term in reversed(terms):expr=f'za ({term}) ({expr})'
            lines +=[f'def node{node_id}Raw{k} : Z := {expr}']
        lines +=[raw(f'node{node_id}RawTape',[x for m in node['raw']for x in m]),f'def node{node_id}Raw : List Z := zTape node{node_id}RawTape',raw(f'node{node_id}CentreTape',node['centre']),f'def node{node_id}Centre : Z := (node{node_id}CentreTape.getD 0 0,node{node_id}CentreTape.getD 1 0)',raw(f'node{node_id}MomentTape',[x for m in node['centered']for x in m]),f'def node{node_id}Moments : List Z := zTape node{node_id}MomentTape']
        for k in range(ORDER+1):
            lines +=[f'theorem n{node_id}raw{k} : node{node_id}Raw{k} = node{node_id}Raw.getD {k} (0,0) := by decide +kernel',f'theorem n{node_id}center{k} : centeredMoment node{node_id}Centre {k} node{node_id}Raw = node{node_id}Moments.getD {k} (0,0) := by decide +kernel']
    lines +=[f'#print axioms p0m12',f'#print axioms n0center12',f'end CatalanCore.Uniform.Decay.Optimization.{label}']
    (out/(label+'.lean')).write_text('\n'.join(lines)+'\n',encoding='utf8')
    record=dict(status='EXACT_INTEGER_MOMENT_WORKLOAD_GENERATED',frame=frame,variant=variant,physical_pieces=len(P),tree_nodes=len(nodes),order=ORDER,global_coordinate_denominator=str(Qscale),global_density_denominator=str(Dscale),integration_lcm=Lscale,normalization='Perpiece and pernode divide coordinate and densitygcds; restore scales by powers in arithmetic, never emit structured rawstates.',nonzero_low64zero_literals_before=original_zeros,nonzero_low64zero_literals_after=normalized_zeros,independent_exact_centered_moment_equalities=len(nodes)*(ORDER+1),source_sha256=hashlib.sha256(SOURCE.read_bytes()).hexdigest(),seconds=time.monotonic()-started,scope='Cold source-bound integer integration/translation certificate arithmetic for fullcompacttree; generic polynomial integration/geometry interpretation remainsPhase2.')
    (EVID/(label+'-model.json')).write_text(json.dumps(record,indent=2)+'\n');print('MOMENT_KERNEL_WORKLOAD',label,len(P),len(nodes),'low64',original_zeros,'to',normalized_zeros,'seconds',record['seconds'],flush=True)
if __name__=='__main__':main(*sys.argv[1:4])
