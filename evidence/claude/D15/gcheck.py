import sys; sys.path.insert(0,'.')
from gdec import *
mp=float(mprime)
import json
for u in ['0','0.01','0.03','0.0625','0.0626','0.1','0.2','0.5','0.8','1']:
    gv=float(gedge(7,u))
    print(u,'g-m\'=%.6f'%(gv-mp))
