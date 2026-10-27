"""Generate an arithmetic workload from the saved signed chi3 spline.
No analytic soundness, remainder theorem or new bound is asserted.
"""
import sys,json,hashlib
sys.set_int_max_str_digits(0)
from pathlib import Path
from fractions import Fraction as Q
from math import comb
BASE=Path(r'C:\Users\seanl\Documents\Codex\2026-10-11\plea')
WORK=BASE/'work/catalan-uniform'
SRC=BASE/'outputs/Compatibility programme'
LEG=SRC/'analytic-decay-2026-10-25'
sys.path[:0]=[str(BASE/'work/pylibs'),str(LEG/'cell-reduction-v1'),str(LEG/'endpoints-v1')]
from flint import ctx
ctx.prec=256
import symbolic_bench as S
from hybrid_cover import potential as direct_potential
from spline_energy import mutual as direct_mutual

source=SRC/'scope-screen-2026-10-27/selected-candidates.json'
row=json.loads(source.read_text())['hybrid'][0]; num=row['numerical']; degree=num['deg']
pieces=[]
for i,p in enumerate(num['pieces']):
    weights=[Q(v) for v in num['w'][i*(degree+1):(i+1)*(degree+1)]]
    cs=[sum((weights[j]*(-1)**(j+k)*comb(j,k)*comb(j+k,k)
        for j in range(k,degree+1)),Q(0)) for k in range(degree+1)]
    a=tuple(Q(str(v)) for v in p['A']); b=tuple(Q(str(v)) for v in p['B'])
    if p['kind']=='ray':
        cs=[v/2 for v in cs]; pieces.append((a,b,cs))
        pieces.append(((a[0],-a[1]),(b[0],-b[1]),cs.copy()))
    else: pieces.append((a,b,cs))
mass=sum((v/Q(k+1) for _,_,cs in pieces for k,v in enumerate(cs)),Q(0))
correction=6*(1-mass); pieces[-1][2][1]+=correction; pieces[-1][2][2]-=correction
assert sum((v/Q(k+1) for _,_,cs in pieces for k,v in enumerate(cs)),Q(0))==1
negative=[i for i,(_,_,cs) in enumerate(pieces)
    if any(sum((c*t**k for k,c in enumerate(cs)),Q(0))<0 for t in (Q(0),Q(1,2),Q(1)))]
assert negative, 'This workload must contain an actually negative density value'
ys=list(map(Q,row['spec']['parameters']['contour']['heights']))
leans=list(map(Q,row['spec']['parameters']['contour']['leans']))
vertices=[(-Q(row['spec']['parameters']['r0']),Q(0))]
for y,l in zip(ys,leans):
    x0,y0=vertices[-1]; vertices.append((x0+l*(y-y0),y))
c=(ys[1]+ys[2])/2; h=Q(1,10**7)
cell_lo,cell_hi=c-h,c+h
class Field:
    b=1+Q(row['alpha']); eps=Q(1,1000)
    nu=[((Q(0),Q(0)),(Q(1),Q(0)),[Q(1)]),
        ((Q(1),Q(0)),(1+2*Q(row['alpha']),Q(0)),[Q(row['alpha'])])]
    def point(self,kind,t):
        x,y=vertices[2]; return (x+leans[2]*(t-y),t)
    def direction(self,kind): return (leans[2],Q(1))
field=Field(); field.pieces=pieces
co=S.point_jets(field,'ray',c,h,8)
numeric,remainder_direct=S.jets(field,'ray',c,h,8)
for j,ex in enumerate(co):
    assert (ex.value()-numeric[j]*S.A(h**j)).contains(0)
z=field.point('ray',c)
control=S.A(field.b)*sum((direct_potential(p,z) for p in pieces),S.A(0))
control-=sum((direct_potential(p,z) for p in field.nu),S.A(0))
control+=S.A(1-field.eps)*S.arb.pi()*S.A(c)
assert (co[0].value()-control).contains(0)
power=[sum((co[k]*Q(comb(k,j)*2**j*(-1)**(k-j)) for k in range(j,8)),S.Expr()) for j in range(8)]
bern=[sum((power[k]*Q(comb(j,k),comb(7,k)) for k in range(j+1)),S.Expr()) for j in range(8)]
idx=negative[0]
energy=S.mutual(pieces[idx],pieces[idx])
assert (energy.value()-direct_mutual(pieces[idx],pieces[idx])).contains(0)
positive_idx=next(i for i,(_,_,cs) in enumerate(pieces)
    if all(sum((v*t**k for k,v in enumerate(cs)),Q(0))>0 for t in (Q(0),Q(1,2),Q(1))))
cross_energy=S.mutual(pieces[idx],pieces[positive_idx])
assert (cross_energy.value()-direct_mutual(pieces[idx],pieces[positive_idx])).contains(0)
keys=sorted(set(k for ex in bern+[energy,cross_energy] for k,v in ex.terms.items() if v))
values=[S.evaluate_term(k) for k in keys]
for key,(v,e) in zip(keys,values):
    exact=S.Expr(terms={key:Q(1)}).value()
    assert S.A(Q(v-e,S.S))<=exact and exact<=S.A(Q(v+e,S.S))

out=WORK/'CatalanCore/Uniform/Decay'; out.mkdir(parents=True,exist_ok=True)
template=(LEG/'cell-reduction-v1/Arithmetic.template.lean').read_text(encoding='utf-8-sig')
template=template.replace('import Lean','import Lean\nimport CatalanMeasure.CellCert.RawInts')
template=template.replace('namespace DecayCellBenchmark','namespace CatalanCore.Uniform.Decay.SignedPilot')
template=template.replace('SCALE_VALUE',str(S.S)).replace('LOG2_VALUE',str(S.L2)).replace('PI_VALUE',str(S.PI))
template+='''
def inputTape : List Int → List Input
  | k::n::d::m::xs => (k.toNat,n,d.toNat,m)::inputTape xs
  | _ => []
def termTape : List Int → List (Nat × Int × Nat)
  | i::n::d::xs => (i.toNat,n,d.toNat)::termTape xs
  | _ => []
def valueTape : List Int → List (Int × Nat)
  | v::e::xs => (v,e.toNat)::valueTape xs
  | _ => []
theorem evalInputs_cons {x xs v vs} (h : evalInput x = some v)
    (hs : evalInputs xs = some vs) : evalInputs (x::xs) = some (v::vs) := by
  simp only [evalInputs, h, hs]
  rfl
'''
template+='\nend CatalanCore.Uniform.Decay.SignedPilot\n'
(out/'PilotArithmetic.lean').write_text(template,encoding='utf-8')
def raw(name,ns): return 'def '+name+' : List Int := raw_ints% ['+', '.join(map(str,ns))+']\n'
def emit(label,exprs):
    used=sorted(set(k for ex in exprs for k,v in ex.terms.items() if v)); vals=[S.evaluate_term(k) for k in used]
    tape=[]; inputs=[]
    for kind,x in used:
        m=0
        if kind=='log':
            m=x.numerator.bit_length()-x.denominator.bit_length()
            if x/Q(2)**m<1:m-=1
        inp=[{'pi':0,'log':1,'atan':2}[kind],x.numerator,x.denominator,m]
        tape.extend(inp); inputs.append(inp)
    lines=['import CatalanCore.Uniform.Decay.PilotArithmetic',
        'set_option Elab.async false','set_option profiler true','set_option profiler.threshold 1',
        'set_option maxRecDepth 100000','set_option maxHeartbeats 0',
        'namespace CatalanCore.Uniform.Decay.SignedPilot']
    for i,(inp,(v,e)) in enumerate(zip(inputs,vals)):
        name=f'{label}Input{i}'
        lines += [raw(name+'Tape',inp),f'def {name} : Input := (inputTape {name}Tape).head!',
            f'theorem {name}_check : evalInput {name} = some ({S.lean_int(v)}, {e}) := by decide +kernel']
    lines += ['def '+label+'Inputs : List Input := ['+', '.join(f'{label}Input{i}' for i in range(len(inputs)))+']',
        raw(label+'ValuesTape',[n for v,e in vals for n in (v,e)]),
        f'def {label}Values : List (Int × Nat) := valueTape {label}ValuesTape',
        f'theorem {label}Values_check : evalInputs {label}Inputs = some {label}Values :=\n  '+
        ''.join(f'evalInputs_cons {label}Input{i}_check (' for i in range(len(inputs)))+
        '(by rfl)'+')'*len(inputs)]
    reports=[]
    for i,ex in enumerate(exprs):
        terms=[]; value=ex.c.numerator*S.S//ex.c.denominator; err=1
        for key,w in sorted(ex.terms.items()):
            if not w: continue
            v,e=vals[used.index(key)]
            # Lean Int division is Euclidean division for positive denominators.
            value+=w.numerator*v//w.denominator
            err+=(abs(w.numerator)*e+w.denominator-1)//w.denominator+1
            terms.extend([used.index(key),w.numerator,w.denominator])
        lo,hi=value-err,value+err
        name=label+str(i)
        lines += [raw(name+'TermsTape',terms),
            raw(name+'Constant',[ex.c.numerator,ex.c.denominator]),
            'def '+name+'Terms : List (Nat × Int × Nat) := termTape '+name+'TermsTape',
            f'def {name}Expression : Expression := ({name}Constant.getD 0 0, ({name}Constant.getD 1 0).toNat, {name}Terms)',
            f'theorem {name}_rows : checkRows {label}Values [{name}Expression] [({S.lean_int(lo)}, {S.lean_int(hi)})] = true := by decide +kernel',
            f'theorem {name}_check : check {label}Inputs [{name}Expression] [({S.lean_int(lo)}, {S.lean_int(hi)})] = true := by\n'+
            f'  unfold check\n  rw [{label}Values_check]\n  exact {name}_rows']
        reports.append(dict(term_count=len(terms)//3,lower=str(lo),upper=str(hi),scaled_width=str(hi-lo)))
    lines+=['end CatalanCore.Uniform.Decay.SignedPilot']
    path=out/('Pilot'+label+'.lean'); path.write_text('\n'.join(lines)+'\n',encoding='utf-8')
    return dict(module='CatalanCore.Uniform.Decay.Pilot'+label,transcendentals=len(used),rows=reports,bytes=path.stat().st_size)
results=[emit('Potential',bern),emit('Energy',[energy,cross_energy])]
# Rational L1 majorants for every grouped endpoint jet-tail contribution.
endpoints={}; direction=field.direction('ray')
for factor,ps in ((field.b,pieces),(Q(-1),field.nu)):
    for a,b,cs in ps:
        v=S.sub(b,a); w=S.zd(S.sub(z,a),v); d=S.zd(direction,v)
        mass=sum((x/Q(k+1) for k,x in enumerate(cs)),Q(0)); degree=len(cs)
        H=[(Q(0),Q(0)) for _ in range(degree+1)]
        for k,x in enumerate(cs):
            for j in range(k+2):
                H[j]=S.za(H[j],S.zc(S.zm(S.zp(w,k+1-j),S.zp(d,j)),x/Q(k+1)*comb(k+1,j)))
        for endpoint,pol in ((a,[S.zc(x,-1) for x in H]),
            (b,[S.zs(x,(mass if j==0 else Q(0),Q(0))) for j,x in enumerate(H)])):
            if endpoint not in endpoints: endpoints[endpoint]=[(Q(0),Q(0)) for _ in pol]
            for j,x in enumerate(pol): endpoints[endpoint][j]=S.za(endpoints[endpoint][j],S.zc(x,factor))
tails=[]
for endpoint,pol in endpoints.items():
    q=S.zd(direction,S.sub(z,endpoint)); r=(abs(q[0])+abs(q[1]))*h
    assert r<1
    for j,pj in enumerate(pol):
        k=8-j; tails.append((abs(pj[0])+abs(pj[1]))*h**j*r**k/(k*(1-r)))
assert remainder_direct <= sum((S.A(t) for t in tails),S.A(0))
tail_upper=sum((S.S*t.numerator+t.denominator-1)//t.denominator for t in tails)
tail_text='''import CatalanCore.Uniform.Decay.PilotArithmetic
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace CatalanCore.Uniform.Decay.SignedPilot
def tailSum : List Int → Nat
  | n::d::xs => (scale*n.toNat+d.toNat-1)/d.toNat + tailSum xs
  | _ => 0
'''+raw('remainderTape',[n for t in tails for n in (t.numerator,t.denominator)])+f'''
theorem remainder_arithmetic : tailSum remainderTape = {tail_upper} := by decide +kernel
end CatalanCore.Uniform.Decay.SignedPilot
'''
(out/'PilotRemainder.lean').write_text(tail_text,encoding='utf-8')
results.append(dict(module='CatalanCore.Uniform.Decay.PilotRemainder',terms=len(tails),upper_scaled=str(tail_upper)))
receipt=dict(source=str(source),sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
    frame=row['frame'],pieces=len(pieces),negative_sample_pieces=negative,energy_self_piece=idx,
    opposite_sign_cross_piece=positive_idx,
    mass_correction=str(correction),cell=[str(cell_lo),str(cell_hi)],scale=str(S.S),
    results=results,
    low64=dict(reduced_rational_pairs=sum(len(ex.terms)+1 for ex in bern+[energy,cross_energy]),
        both_numerator_denominator_zero=sum(int(q.numerator%2**64==0 and q.denominator%2**64==0)
        for ex in bern+[energy,cross_energy] for q in [ex.c]+list(ex.terms.values()))),
    scope='Full signed chi3 potential arithmetic, 8 Bernstein values and grouped order8 rational L1 tail sum; negative-piece self-energy and positive/negative cross-energy. Analytic formula/remainder/enclosure soundness remains unproved; no HasDecay or new bank.')
(WORK/'scripts/uniform-phase0/signed-mirror.json').write_text(json.dumps(receipt,indent=2)+'\n')
print('SIGNED_MIRROR_COMPLETED '+json.dumps(receipt),flush=True)
