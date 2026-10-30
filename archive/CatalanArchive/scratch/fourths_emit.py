import sys
sys.path.insert(0, 'scripts/claude/bank/check')
import emit_bank_uf as U
from fractions import Fraction as F
U.BANKS['lambda'].update(lp2w=True, pre_nmax=8, target=F(314411, 10000))
sys.argv = ['emit_bank_uf.py', 'lambda']
src = open('scripts/claude/bank/check/emit_bank_uf.py', encoding='utf-8').read()
main = src[src.index("if __name__ == '__main__':"):]
body = main.split('\n', 1)[1]
import textwrap
exec(textwrap.dedent(body), U.__dict__)
