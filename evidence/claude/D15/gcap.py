import sys; sys.path.insert(0,'.')
from gdec import *
import pickle
mp=mprime
xs=[Fr(-95100+i*10,10**6) if False else Fr(-951000+ i*100, 10**7) for i in range(0,81)]   # -0.0951 .. -0.0943 step 1e-5
out=[]
for x in xs:
    v=g(C(DF(x),D(0)))-DF(mp)
    out.append((float(x),float(v)))
pickle.dump(out,open('C:/Users/seanl/Documents/Codex/2026-10-11/plea/work/catalan-uniform/evidence/claude/D15/gcap_window.pkl','wb'))
for x,v in out[::4]: print('%.6f %.3e'%(x,v))
