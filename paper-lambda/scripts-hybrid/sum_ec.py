def T2(n): return n*(n-1) if n>=1 else 0
def e(K,m,c):
    s=K-m
    if c<=K: return (c if c<s else 0)+T2(min(c,s))+T2(c-m)
    d=c-K; F=max(0,d-m); n=s-F; o=max(0,s-d)
    return T2(n)+T2(o)+(d if d<s else 0)
bad=0
for K in range(2,201):
    for m in range(0,K-1):
        s=K-m; D=s*(s-1)*(4*s+6*m+1)//3
        assert s*(s-1)*(4*s+6*m+1)%3==0
        if sum(e(K,m,c) for c in range(1,2*K))!=D: bad+=1; print('bad',K,m)
print('checked K<=200, bad =',bad)
# compare with DP's min-formula
def eDP(K,m,c):
    s=K-m
    T=lambda n: n*(n+1) if n>0 else 0
    if c<=K:
        d=K-c
        return min(c*c+T(c-m-1), s*(s-1)+T(s-1-d))
    dp=c-K; t=2*K-c; u=s-1-dp
    A=s*s-1+u*u if u>=0 else s*(s-1)
    B=t*(t-1) if t<=m else K+2*t*t-(2*m+3)*t+m*m+m
    return min(A,B)
mis=0
for K in range(2,80):
    for m in range(0,K-1):
        for c in range(1,2*K):
            if e(K,m,c)!=eDP(K,m,c): mis+=1
print('mismatches with DP min-formula (K<80):',mis)
