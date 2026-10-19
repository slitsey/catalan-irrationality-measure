from hybmirror import *
from multiprocessing import Pool
LAMLST=Lst(LAM); sc=legacy_seg(); MT=F(22147,10000)
def job(a):
    GRP,j=a
    b=(sc[GRP*j][0], sc[GRP*j+GRP-1][1],0,0)
    return hLB(sig_flat(LAMLST,b),b)
if __name__=='__main__':
    with Pool(6) as pool:
        for GRP in (22,11,4,2):
            n=len(sc)//GRP
            ls=pool.map(job,[(GRP,j) for j in range(n)],chunksize=16)
            S=F(0)
            for i,(a,b,g) in enumerate(sc):
                S+=F(b-a,Z)*min(F(g,2**32)+ls[i//GRP]-MT,0)
            print(GRP, n, float(2*S), flush=True)
