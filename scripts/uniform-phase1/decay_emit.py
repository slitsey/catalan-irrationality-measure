"""Emit literal arithmetic cell data and matched indexed/streamed checks."""
from decay_common import *
sys.set_int_max_str_digits(0)
def raw(name,ns):return f'def {name} : List Int := raw_ints% ['+', '.join(map(str,ns))+']\n'
def emit(label,exprs,metadata,fast=False):
    out=WORK/'CatalanCore/Uniform/Decay/Optimization';out.mkdir(exist_ok=True)
    keys=sorted({k for ex in exprs for k,w in ex.terms.items()if w})
    if fast:
        from decay_tables import fastTerm
    evaluator=fastTerm if fast else S.evaluate_term
    values=[evaluator(k)for k in keys]
    arithmetic='Tables' if fast else 'Arithmetic';checkInput='evalFastInput' if fast else 'evalInput';evalList='evalFastInputs' if fast else 'evalInputs';cons='evalFastInputs_cons' if fast else 'evalInputs_cons'
    lines=[f'import CatalanCore.Uniform.Decay.Optimization.{arithmetic}','set_option Elab.async false','set_option profiler true','set_option profiler.threshold 1','set_option maxRecDepth 100000','set_option maxHeartbeats 0',f'namespace CatalanCore.Uniform.Decay.Optimization.{label}','open CatalanCore.Uniform.Decay.SignedPilot']
    for i,((kind,x),(v,e))in enumerate(zip(keys,values)):
        m=0
        if kind=='log':
            m=x.numerator.bit_length()-x.denominator.bit_length()
            if x/Q(2)**m<1:m-=1
        inp=[{'pi':0,'log':1,'atan':2}[kind],x.numerator,x.denominator,m]
        exact=S.Expr(terms={(kind,x):Q(1)}).value();assert A(Q(v-e,S.S))<=exact and exact<=A(Q(v+e,S.S))
        lines += [raw(f'input{i}Tape',inp),f'def input{i} : Input := (inputTape input{i}Tape).head!',f'theorem input{i}_check : {checkInput} input{i} = some ({S.lean_int(v)},{e}) := by decide +kernel']
    lines += ['def inputs : List Input := ['+', '.join(f'input{i}'for i in range(len(keys)))+']',raw('valuesTape',[n for v,e in values for n in(v,e)]),'def values : List (Int × Nat) := valueTape valuesTape',f'theorem values_check : {evalList} inputs = some values :=\n  '+''.join(f'{cons} input{i}_check ('for i in range(len(keys)))+'(by rfl)'+')'*len(keys)]
    bounds=[]
    for j,ex in enumerate(exprs):
        ws=[ex.terms.get(k,Q(0))for k in keys];value=ex.c.numerator*S.S//ex.c.denominator;error=1
        for w,(v,e)in zip(ws,values):value+=w.numerator*v//w.denominator;error+=(abs(w.numerator)*e+w.denominator-1)//w.denominator+1
        lo,hi=value-error,value+error;bounds.append((lo,hi))
        lines += [raw(f'weight{j}Tape',[n for w in ws for n in(w.numerator,w.denominator)]),f'def weights{j} : List (Int × Nat) := valueTape weight{j}Tape',raw(f'constant{j}Tape',[ex.c.numerator,ex.c.denominator]),f'def expression{j} : Expression := (constant{j}Tape.getD 0 0,(constant{j}Tape.getD 1 0).toNat,indexedTerms values weights{j})']
    lines += [f'end CatalanCore.Uniform.Decay.Optimization.{label}']
    (out/(label+'Data.lean')).write_text('\n'.join(lines)+'\n',encoding='utf-8')
    header=[f'import CatalanCore.Uniform.Decay.Optimization.{label}Data','set_option Elab.async false','set_option profiler true','set_option profiler.threshold 1','set_option maxRecDepth 100000','set_option maxHeartbeats 0',f'namespace CatalanCore.Uniform.Decay.Optimization.{label}','open CatalanCore.Uniform.Decay.SignedPilot']
    indexed=header.copy();stream=header.copy()
    for j,((lo,hi),ex)in enumerate(zip(bounds,exprs)):
        indexed += [f'theorem indexed{j} : checkRows values [expression{j}] [({S.lean_int(lo)},{S.lean_int(hi)})] = true := by decide +kernel']
        stream += [f'theorem streamed{j} : streamCheck values (constant{j}Tape.getD 0 0) (constant{j}Tape.getD 1 0).toNat weights{j} ({S.lean_int(lo)}) ({S.lean_int(hi)}) = true := by decide +kernel',f'theorem transferred{j} : checkRows values [expression{j}] [({S.lean_int(lo)},{S.lean_int(hi)})] = true := by\n  unfold expression{j}\n  rw [checkRows_stream]\n  exact streamed{j}']
    indexed += [f'end CatalanCore.Uniform.Decay.Optimization.{label}'];stream += [f'end CatalanCore.Uniform.Decay.Optimization.{label}']
    (out/(label+'Indexed.lean')).write_text('\n'.join(indexed)+'\n',encoding='utf-8');(out/(label+'Stream.lean')).write_text('\n'.join(stream)+'\n',encoding='utf-8')
    rec=dict(label=label,inputs=len(keys),rows=len(exprs),bounds=[[str(a),str(b)]for a,b in bounds],max_width=max((b-a)/S.S for a,b in bounds),**metadata)
    (EVID/(label+'-arithmetic.json')).write_text(json.dumps(rec,indent=2)+'\n');print('EMITTED',label,'inputs',len(keys),'width',rec['max_width'],flush=True);return rec


