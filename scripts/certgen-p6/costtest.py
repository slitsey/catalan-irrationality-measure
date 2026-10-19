import sys; sys.path.insert(0,'.')
import genreal as g
from p6mirror import *
import math
for tol in (2e-5, 1e-4, 3e-4, 1e-3):
    tot=0; n=0; S=0
    for k in range(0, g.NSEG//32, 4):
        cells=g.seg_cells[k*32:(k+1)*32]
        c=g.macro_choose_real(cells, lambda i,lb_,fl,u: lb_>=fl-F(tol))
        tot+=c[0]; n+=32
    print(tol, tot/n, flush=True)
