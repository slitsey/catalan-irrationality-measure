"""Closed form of selfEnergy [(1,0,1),(1/2,1,13/10)] = rat + a13*log(13/10) + a3*log(3/10) (thirds node measure)."""
from fractions import Fraction as F
import math
pieces=[(F(1),F(0),F(1)),(F(1,2),F(1),F(13,10))]
def H(s):
    # returns (rat, coeff of log13, coeff of log3) of s^2 log|s|/2 - 3/4 s^2
    r=-F(3,4)*s*s; l13=F(0); l3=F(0)
    a=abs(s)
    if a==0: return (F(0),F(0),F(0))
    c=s*s/2
    if a==1: pass
    elif a==F(13,10): l13+=c
    elif a==F(3,10): l3+=c
    else: raise ValueError(a)
    return (r,l13,l3)
def add(x,y,k=1): return tuple(a+k*b for a,b in zip(x,y))
tot=(F(0),F(0),F(0))
for (w,a,b) in pieces:
    for (v,c,d) in pieces:
        pe=(F(0),F(0),F(0))
        pe=add(pe,H(b-d)); pe=add(pe,H(a-c)); pe=add(pe,H(b-c),-1); pe=add(pe,H(a-d),-1)
        tot=add(tot,pe,w*v)
print(tot)
val=float(tot[0])+float(tot[1])*math.log(1.3)+float(tot[2])*math.log(0.3)
print(val, 867481404213/500000000000)
