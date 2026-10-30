import sys,time; sys.path.insert(0,'evidence/claude/D15')
exec(open('evidence/claude/D15/e7.py').read().split("for (ua,ub) in []")[0])
for (ua,ub) in [(Fr(0),Fr(1,16)),(Fr(1,16),Fr(1,4)),(Fr(1,4),Fr(1)),(Fr(1,16),Fr(1,2)),(Fr(1,2),Fr(1)),(Fr(1,16),Fr(1)),(Fr(0),Fr(1,12))]:
    for J_ in (6,8):
        r=evalcell(ua,ub,J=J_)
        print(ua,ub,J_,float(r[0]) if r else None)
