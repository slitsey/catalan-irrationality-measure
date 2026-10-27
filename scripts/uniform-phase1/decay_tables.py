"""Shared log/atan node tables plus checked short residual series on actual inputs."""
from decay_common import *
sys.set_int_max_str_digits(0)
def short(a,b,alt=False):
    p,q=a,b;v=0
    for j in range(10):
        t=S.S*p//(q*(2*j+1));v+=(-t if alt and j%2 else t);p*=a*a;q*=b*b
    return v
LOG=[(S.evaluate_term(('log',Q(64+j,64)))[0],130)for j in range(65)]
ATAN=[S.evaluate_term(('atan',Q(j,128)))for j in range(129)]
def fastTerm(key):
    kind,x=key
    if kind=='pi':return S.PI,2000
    if kind=='log':
        m=x.numerator.bit_length()-x.denominator.bit_length();y=x/Q(2)**m
        if y<1:m-=1;y*=2
        a,b=y.numerator,y.denominator;j=64*(a-b)//b;ta=64*a-(64+j)*b;tb=64*a+(64+j)*b
        assert 0<=j<65 and 128*ta<=tb
        v,e=LOG[j];return v+2*short(ta,tb)+m*S.L2,e+22+130*abs(m)
    neg=x<0;x=abs(x);inv=x>1
    if inv:x=1/x
    a,b=x.numerator,x.denominator;j=128*a//b;ta=128*a-j*b;tb=128*b+j*a
    assert 0<=j<129 and 128*ta<=tb
    v,e=ATAN[j];v+=short(ta,tb,True);e+=12
    if inv:v=S.PI//2-v;e+=1100
    return(-v if neg else v),e

def main():
    from decay_emit import raw,emit
    out=WORK/'CatalanCore/Uniform/Decay/Optimization'
    lines=['import CatalanCore.Uniform.Decay.Optimization.Arithmetic','set_option Elab.async false','set_option profiler true','set_option profiler.threshold 1','set_option maxRecDepth 100000','namespace CatalanCore.Uniform.Decay.Optimization','open CatalanCore.Uniform.Decay.SignedPilot']
    for kind,values,code,den in [('log',LOG,1,64),('atan',ATAN,2,128)]:
        for j,(v,e)in enumerate(values):
            num=64+j if code==1 else j
            lines+=[f'theorem {kind}Node{j} : evalInput ({code},{num},{den},0) = some ({S.lean_int(v)},{e}) := by decide +kernel']
        lines += [raw(kind+'NodesTape',[n for v,e in values for n in(v,e)]),f'def {kind}Nodes : List (Int × Nat) := valueTape {kind}NodesTape']
    lines+=['''def shortSeries (alt : Bool) (a b : Nat) : Int := seriesLoop alt (a*a) (b*b) 10 a b 0 0

def evalFastInput (input : Input) : Option (Int × Nat) :=
  let (kind,n,d,m) := input
  if d == 0 then none else
  if kind == 0 then some (piLiteral,2000) else
  if kind == 1 then
    let (a,b) := if 0 ≤ m then (n.natAbs,d*2^m.toNat) else (n.natAbs*2^(-m).toNat,d)
    if 0 < n && b ≤ a && a ≤ 2*b then
      let j := 64*(a-b)/b
      let ta := 64*a-(64+j)*b
      let tb := 64*a+(64+j)*b
      if j < 65 && (64+j)*b ≤ 64*a && 128*ta ≤ tb then
        let (v,e) := logNodes.getD j (0,0)
        some (v + 2*shortSeries false ta tb + m*log2Literal,e+22+130*m.natAbs)
      else none
    else none
  else if kind == 2 then
    let neg := n < 0
    let inv := d < n.natAbs
    let (a,b) := if inv then (d,n.natAbs) else (n.natAbs,d)
    let j := 128*a/b
    let ta := 128*a-j*b
    let tb := 128*b+j*a
    if j < 129 && j*b ≤ 128*a && 128*ta ≤ tb then
      let (v,e) := atanNodes.getD j (0,0)
      let (v,e) := (v+shortSeries true ta tb,e+12)
      let (v,e) := if inv then (piLiteral/2-v,e+1100) else (v,e)
      some ((if neg then -v else v),e)
    else none
  else none

def evalFastInputs : List Input → Option (List (Int × Nat))
  | [] => some []
  | x::xs => do
    let v ← evalFastInput x
    let vs ← evalFastInputs xs
    some (v::vs)

theorem evalFastInputs_cons {x xs v vs} (h : evalFastInput x = some v)
    (hs : evalFastInputs xs = some vs) : evalFastInputs (x::xs) = some (v::vs) := by
  simp only [evalFastInputs,h,hs]
  rfl

end CatalanCore.Uniform.Decay.Optimization
''']
    (out/'Tables.lean').write_text('\n'.join(lines)+'\n',encoding='utf8')
    import decay_far as far
    captured={}
    far.emit=lambda label,exprs,metadata:captured.setdefault(label,(exprs,metadata))
    far.main()
    emit('TableFar',*captured['Far'],fast=True)
    (EVID/'shared-table-model.json').write_text(json.dumps(dict(log_nodes=65,atan_nodes=129,residual_terms=10,original_terms=64,max_residual='1/128',scope='Each node kernel-checks the old64term evaluator once; every new residual verifies its1/128guard. Arb independently validates every actual new interval. Generic log/atan addition and remainder analytic proofs remainPhase2. No exact finite-series equality to old input values claimed.'),indent=2)+'\n')
    print('SHARED_TABLE_WORKLOAD_VALIDATED',flush=True)
if __name__=='__main__':main()

