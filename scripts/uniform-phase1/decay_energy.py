"""Weight-aware precision repair of the actual ill-conditioned signed energy block."""
from decay_common import *
sys.set_int_max_str_digits(0)
import math
ctx.prec=512
P=50;SCALE=10**P+39;N=96

def series(a,b,alt=False):
    p,q=a,b;acc=0
    for j in range(N):
        term=SCALE*p//(q*(2*j+1));acc+=(-term if alt and j%2 else term);p*=a*a;q*=b*b
    return acc
L2=2*series(1,3);PI=16*series(1,5,True)-4*series(1,239,True)
def evaluate(key):
    kind,x=key
    if kind=='pi':return PI,3000
    if kind=='log':
        m=x.numerator.bit_length()-x.denominator.bit_length();y=x/Q(2)**m
        if y<1:m-=1;y*=2
        t=(y-1)/(y+1);return2=2*series(t.numerator,t.denominator)+m*L2
        return return2,200*(1+abs(m))
    neg=x<0;x=abs(x);inv=x>1
    if inv:x=1/x
    if x>Q(1,2):t=(1-x)/(1+x);v=PI//4-series(t.numerator,t.denominator,True);e=900
    else:v=series(x.numerator,x.denominator,True);e=100
    if inv:v=PI//2-v;e+=1700
    return(-v if neg else v),e

def main():
    from decay_emit import raw
    f=Field(getrow('chi3'));idx=86;pos=0
    expressions=[S.mutual(f.pieces[idx],f.pieces[idx]),S.mutual(f.pieces[idx],f.pieces[pos])]
    from spline_energy import mutual as independent
    for ex,p,q in zip(expressions,[idx,idx],[idx,pos]):assert(ex.value()-independent(f.pieces[p],f.pieces[q])).contains(0)
    keys=sorted({k for ex in expressions for k,v in ex.terms.items()if v});vals=[evaluate(k)for k in keys]
    for key,(v,e)in zip(keys,vals):
        exact=S.Expr(terms={key:Q(1)}).value();assert A(Q(v-e,SCALE))<=exact and exact<=A(Q(v+e,SCALE))
    out=WORK/'CatalanCore/Uniform/Decay/Optimization'
    arithmetic=(WORK/'CatalanCore/Uniform/Decay/PilotArithmetic.lean').read_text(encoding='utf-8-sig')
    arithmetic=arithmetic.replace('namespace CatalanCore.Uniform.Decay.SignedPilot','namespace CatalanCore.Uniform.Decay.Optimization.EnergyPrecision').replace('end CatalanCore.Uniform.Decay.SignedPilot','end CatalanCore.Uniform.Decay.Optimization.EnergyPrecision')
    arithmetic=arithmetic.replace(str(S.S),str(SCALE)).replace(str(S.L2),str(L2)).replace(str(S.PI),str(PI)).replace(' 64 a b 0 0',' 96 a b 0 0').replace('(piLiteral, 2000)','(piLiteral, 3000)').replace('130*(1+m.natAbs)','200*(1+m.natAbs)').replace('), 600)', '), 900)').replace('else (series true a b, 70)','else (series true a b, 100)').replace('e+1100','e+1700')
    (out/'EnergyArithmetic.lean').write_text(arithmetic,encoding='utf8')
    lines=['import CatalanCore.Uniform.Decay.Optimization.EnergyArithmetic','set_option Elab.async false','set_option profiler true','set_option profiler.threshold 1','set_option maxRecDepth 100000','set_option maxHeartbeats 0','namespace CatalanCore.Uniform.Decay.Optimization.EnergyPrecision']
    for i,((kind,x),(v,e))in enumerate(zip(keys,vals)):
        m=0
        if kind=='log':
            m=x.numerator.bit_length()-x.denominator.bit_length()
            if x/Q(2)**m<1:m-=1
        lines +=[raw(f'input{i}Tape',[{'pi':0,'log':1,'atan':2}[kind],x.numerator,x.denominator,m]),f'def input{i} : Input := (inputTape input{i}Tape).head!',f'theorem input{i}_check : evalInput input{i} = some ({S.lean_int(v)},{e}) := by decide +kernel']
    lines +=['def inputs : List Input := ['+', '.join(f'input{i}'for i in range(len(keys)))+']',raw('valuesTape',[n for v,e in vals for n in(v,e)]),'def values : List (Int × Nat) := valueTape valuesTape','theorem values_check : evalInputs inputs = some values :=\n  '+''.join(f'evalInputs_cons input{i}_check ('for i in range(len(keys)))+'(by rfl)'+')'*len(keys)]
    widths=[];reports=[]
    for j,ex in enumerate(expressions):
        value=ex.c.numerator*SCALE//ex.c.denominator;error=1;terms=[]
        for key,w in sorted(ex.terms.items()):
            if not w:continue
            i=keys.index(key);v,e=vals[i];value+=w.numerator*v//w.denominator;error+=(abs(w.numerator)*e+w.denominator-1)//w.denominator+1;terms.extend([i,w.numerator,w.denominator])
        lo,hi=value-error,value+error; width=Q(hi-lo,SCALE);widths.append(width)
        lines +=[raw(f'constant{j}',[ex.c.numerator,ex.c.denominator]),raw(f'terms{j}',terms),f'def expression{j} : Expression := (constant{j}.getD 0 0,(constant{j}.getD 1 0).toNat,termTape terms{j})',f'theorem row{j} : checkRows values [expression{j}] [({S.lean_int(lo)},{S.lean_int(hi)})] = true := by decide +kernel']
        exact=ex.value();assert A(Q(lo,SCALE))<=exact and exact<=A(Q(hi,SCALE))
        reports.append(dict(lower=str(Q(lo,SCALE)),upper=str(Q(hi,SCALE)),width=str(width),width_F=float(width)))
    lines +=['#print axioms row1','end CatalanCore.Uniform.Decay.Optimization.EnergyPrecision'];(out/'EnergyHigh.lean').write_text('\n'.join(lines)+'\n',encoding='utf8')
    old=json.loads((SRC/'lean-plan-2026-10-27/evidence/phase0/signed-mirror.json').read_text())['results'][1]['rows'][1]
    oldwidth=Q(int(old['scaled_width']),S.S)
    # Choose precision from the actual amplification, not a universal giant grid.
    target=Q(1,10**18);required=math.ceil(math.log10(float(oldwidth*S.S/target)))+1
    assert P>=required and widths[1]<target
    record=dict(status='DIRECTED_WEIGHT_AWARE_ENERGY_REPAIR',source_sha256=hashlib.sha256(SOURCE.read_bytes()).hexdigest(),negative_piece=idx,positive_piece=pos,inputs=len(keys),old_width=str(oldwidth),old_width_F=float(oldwidth),selected_decimal_precision=P,required_digits_from_old_weight_amplification=required,series_terms=N,rows=reports,scope='Same actual negative self/positive-negative cross source blocks; independent exact symbolic and Arb controls. Generic scalar enclosure/source transfer remainsPhase2.')
    (EVID/'energy-precision.json').write_text(json.dumps(record,indent=2)+'\n');print('ENERGY_FIXED',float(oldwidth),'to',float(widths[1]),'digits',P,'required',required,flush=True)
if __name__=='__main__':main()
