import sys;sys.path.insert(0,r'scripts\claude\bank\screen')
from bp import *
P=r'C:\Users\seanl\Documents\Codex\2026-10-11\plea\outputs\Compatibility programme\hybrid-exact-receipts-2026-10-27'
ex=json.loads(open(P+r'\exact-FIFTH.json').read());f=RField(ex)
def test(kind,p,sigma,S):
    pt=f.point(kind,p) if kind=='ray' else (p,Q(0))
    if kind=='ray':
        j=f.edge(p) if sigma>0 else sum(y<p for y in f.ys);dvec=(sigma*f.leans[j],Q(sigma))
    else:dvec=(Q(sigma),Q(0))
    d=complex(float(dvec[0]),float(dvec[1]))
    inc=[];far_s=[];far_n=[]
    for fac,ps,tg in ((f.b,f.pieces,'s'),(Q(-1),f.nu,'n')):
        for Pc in ps:
            if same(Pc[0],pt):inc.append((fac,Pc))
            elif same(Pc[1],pt):inc.append((fac,reverse_piece(Pc)))
            else:(far_s if tg=='s' else far_n).append(Pc)
    pa,pl,rem=inc_model(inc,d,None);sub=SubField(f,far_s,far_n,dvec);sub.active=p
    Sq=Q(S).limit_denominator(10**12);co,rad=jets(sub,kind,p,Sq,8);co=[float(x.mid()) for x in co];rad=float(rad.upper())
    print(kind,float(p),sigma,'ninc',len(inc),'rad',rad,'rem',rem(S))
    for s in (S*0.1,S*0.5,S):
        tt=p+sigma*Q(s).limit_denominator(10**12)
        # for ray: parameter t = y: point = p + s*d => y = p + sigma*s
        gv=float(f.evaluate(kind,tt).mid())
        far=sum(co[i]*s**i for i in range(len(co)))
        if kind=='ray' and sigma<0:far-=2*float(1-f.eps)*math.pi*s
        incv=sum(pa[i]*s**i for i in range(len(pa)))+math.log(s)*sum(pl[i]*s**i for i in range(len(pl)))
        print('  s',s,'g',gv,'model',far+incv,'diff',gv-far-incv)
test('line',Q(7,10),1,0.02);test('line',Q(7,10),-1,0.02);test('line',Q(0),1,0.02);test('seg',-f.r0,1,0.0001)
test('ray',Q(22,100),1,0.01);test('ray',Q(22,100),-1,0.01)
