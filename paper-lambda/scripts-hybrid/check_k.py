from fractions import Fraction as Fr
import sys
sys.setrecursionlimit(10000)
def inv(M):
    n=len(M); A=[row[:]+[Fr(int(i==j)) for j in range(n)] for i,row in enumerate(M)]
    for i in range(n):
        p=next(r for r in range(i,n) if A[r][i]!=0); A[i],A[p]=A[p],A[i]
        d=A[i][i]; A[i]=[x/d for x in A[i]]
        for r in range(n):
            if r!=i and A[r][i]!=0:
                f=A[r][i]; A[r]=[x-f*y for x,y in zip(A[r],A[i])]
    return [row[n:] for row in A]
def det(M):
    n=len(M); A=[r[:] for r in M]; d=Fr(1)
    for i in range(n):
        p=next((r for r in range(i,n) if A[r][i]!=0),None)
        if p is None: return Fr(0)
        if p!=i: A[i],A[p]=A[p],A[i]; d=-d
        d*=A[i][i]
        for r in range(i+1,n):
            f=A[r][i]/A[i][i]; A[r]=[x-f*y for x,y in zip(A[r],A[i])]
    return d
def mul(A,B): return [[sum(A[i][k]*B[k][j] for k in range(len(B))) for j in range(len(B[0]))] for i in range(len(A))]
def kRL(K,m,th):
    s=K-m; G=list(range(1,s+1)); Y=[s+1+2*i for i in range(m)]; X=[s+2+2*i for i in range(m)]
    C=lambda J:[[Fr(1)/(a+th+j) for j in J] for a in range(K)]
    CX=C(G+X); CY=C(G+Y)
    Gam=mul([list(r) for r in zip(*CX)],CY)
    Gi=inv(Gam); T=[[Gi[i][j] for j in range(s)] for i in range(s)]
    g=s-1
    rows=[]; v=[Fr(int(i==g)) for i in range(s)]
    for k in range(s):
        rows.append(v[:])
        v=[sum(v[i]*T[i][j] for i in range(s)) for j in range(s)]  # row vector * T
    kR=det(rows)
    cols=[]; v=[Fr(int(i==g)) for i in range(s)]
    for k in range(s):
        cols.append(v[:]); v=[sum(T[i][j]*v[j] for j in range(s)) for i in range(s)]
    kL=det([list(r) for r in zip(*cols)])
    return kR,kL
def T2(n): return n*(n-1) if n>=1 else 0
def e(K,m,c):
    s=K-m
    if c<=K: return (c if c<s else 0)+T2(min(c,s))+T2(c-m)
    d=c-K; F=max(0,d-m); n=s-F; o=max(0,s-d)
    return T2(n)+T2(o)+(d if d<s else 0)
for (K,m) in [(3,0),(3,1),(4,1),(4,2),(5,0),(5,2),(6,3)]:
    ratios=set(); ratL=set()
    for th in [Fr(1),Fr(2),Fr(1,3),Fr(5,7),Fr(11)]:
        kR,kL=kRL(K,m,th)
        P=Fr(1)
        for c in range(1,2*K): P*=(th+c)**e(K,m,c)
        ratios.add(kR/P); ratL.add(kL/P)
    print(K,m,'const R:',ratios if len(ratios)==1 else 'NOT CONSTANT', ' L:',ratL if len(ratL)==1 else 'NOT CONSTANT')
