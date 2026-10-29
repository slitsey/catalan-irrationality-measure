"""G8f: emit all instance files Bank532/Host_<NM>.lean and the final module Hosts532Inst.lean.
usage: gen_all.py [--emit KEY...]   (default: all keys)
       gen_all.py --final           (write Hosts532Inst.lean from the existing Host_* files)"""
import os, sys, re, json
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gencheck2 import *
from gencheck4 import *
from gencheck5 import *

B532 = os.path.join(ROOT, 'CatalanMeasure', 'GenD', 'Uniform', 'Bank532')

def host_path(key): return os.path.join(B532, 'Host_%s.lean' % modname(key))

if __name__ == '__main__':
    if len(sys.argv) > 1 and sys.argv[1] == '--final':
        keys = [k for k in all_keys()]
        fields = []
        mods = []
        for k in keys:
            nm = modname(k)
            if 'L0146' in k:
                fields.append('  h_%s := CatalanMeasure.GenD.Uniform.W.Charts5.physHost_pilot' % nm)
            else:
                assert os.path.exists(host_path(k)), k
                mods.append('public import CatalanMeasure.GenD.Uniform.Bank532.Host_%s' % nm)
                fields.append('  h_%s := CatalanMeasure.GenD.Uniform.Bank532.Pk.%s.phys' % (nm, nm))
        L = ['module', 'public import CatalanMeasure.GenD.Uniform.Bank532.Final532',
             'public import CatalanMeasure.GenD.Uniform.W.Charts5.Phys'] + mods + [
             '@[expose] public section', 'set_option Elab.async false', '',
             '/-! The 34 packet hosts, from the verified checker `checkHost` (33 packets) and the pilot host (L0146):',
             '    `Hosts532` and the unconditional `μ(G) ≤ 532`. -/', '',
             'namespace CatalanMeasure.GenD.Uniform.Bank532', 'noncomputable section', '',
             'theorem hosts532 : Hosts532 where'] + fields + [
             '', '/-- **`μ(G) ≤ 532`.** -/',
             'theorem catalan_irrationalityMeasure_532 :',
             '    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,',
             '      (b : ℝ) ^ (-(532 : ℝ)) <',
             '        |(∑\' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| :=',
             '  catalan_irrationalityMeasure_532_of_hosts hosts532', '',
             'end', 'end CatalanMeasure.GenD.Uniform.Bank532', '',
             '#print axioms CatalanMeasure.GenD.Uniform.Bank532.catalan_irrationalityMeasure_532']
        out = os.path.join(B532, 'Hosts532Inst.lean')
        open(out, 'w', encoding='utf-8').write('\n'.join(L) + '\n')
        print('wrote', out)
        sys.exit(0)
    keys = sys.argv[2:] if len(sys.argv) > 2 and sys.argv[1] == '--emit' else [k for k in all_keys() if 'L0146' not in k]
    for k in keys:
        try:
            g, res = emit(k, host_path(k))
            print('OK ', k, res.get('regions'), res.get('cover'), flush=True)
        except Exception as e:
            print('FAIL', k, repr(e)[:300], flush=True)
