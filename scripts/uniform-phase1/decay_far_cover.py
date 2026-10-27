"""Directed adaptive covers with signed source-cluster compression."""
from decay_common import *
from decay_far import Cluster,choose,coefficients,ORDER
import decay_cover as cover
import copy,statistics
class CompressedField(Field):
    def __init__(self,row,variant='baseline'):
        super().__init__(row,variant);self.tree=Cluster(self.pieces,list(range(len(self.pieces))));self.stats=[]
    def bound(self,kind,lo,hi,n=8):
        c=(lo+hi)/2;h=(hi-lo)/2;self.active=c;z=self.point(kind,c);direction=self.direction(kind)
        far,near,mpError=choose(self.tree,z,h*sum(map(abs,direction)),Q(1,10**10),self.tree.TV)
        nf=copy.copy(self);nf.pieces=[self.pieces[i]for i in near]
        farco=[S.Expr()for _ in range(ORDER)];tail=self.b*mpError
        for cluster in far:
            cs,error=coefficients(cluster,z,direction,h);farco=[a+self.b*b for a,b in zip(farco,cs)];tail+=self.b*error
        data=jets(nf,kind,c,h,ORDER)
        self.stats.append((len(near),len(far)))
        if data is None:
            nb=Field.bound(nf,kind,lo,hi,n)
            if nb is None:return None
            fr=bernstein_range([ex.value()for ex in farco],Q(1))
            return nb[0]+fr-A(tail),nb[1]+fr+A(tail),'endpoint-multipole',float(tail)+nb[3]
        co,nearError=data
        total=[co[j]*A(h**j)+farco[j].value()for j in range(ORDER)]
        br=bernstein_range(total,Q(1));error=nearError+A(tail)
        return br-error,br+error,'multipole-logjet8',float(error)

def main(frame,variant):
    destination=EVID/'far-covers';destination.mkdir(exist_ok=True)
    cover.Field=CompressedField;cover.EVID=destination
    cover.run(frame,variant)
    path=destination/f'cover-{frame}-{variant}.json';record=json.loads(path.read_text())
    record['policy']='Signed absolute-TV order12 source-cluster multipoles; order8 query jets; endpoint modulus for nearby pieces only; rechecked unions up to8'
    record['kernel_model']={'status':'C pending measured compressed-cell closure; original indexed cost formula intentionally removed'}
    path.write_text(json.dumps(record,indent=2)+'\n')
if __name__=='__main__':main(*sys.argv[1:3])
