"""Prepare q7-specific local rank certificates and matched assembly contract."""
from pathlib import Path
import re
import sys

ROOT = Path(r'C:/Users/seanl/Documents/Codex/2026-10-11/plea/work/catalan-uniform')
OUT = Path(sys.argv[1]) if len(sys.argv) > 1 else ROOT/'CatalanCore/Uniform/Bank/Sevenths'
OUT.mkdir(exist_ok=True)
from pathlib import Path
p=Path(__file__).with_name('prepare_rank.py')
exec(compile(p.read_text(encoding='utf-8'),str(p),'exec'),{'__file__':str(p)})

s = (ROOT/'CatalanCore/Uniform/Bank/Lambda/PolePalette.lean').read_text(encoding='utf-8')
s = s.replace('Bank.Lambda', 'Bank.Sevenths').replace('q4', 'q7').replace('D4', 'D7Frame').replace('hp4', 'hp7')
s = re.sub(r'\b16\b', '49', s)
s = re.sub(r'\b4\b', '7', s)
(OUT/'PolePalette.lean').write_text(s, encoding='utf-8')

s = (ROOT/'CatalanCore/Uniform/Bank/Lambda/Content.lean').read_text(encoding='utf-8')
s = s.replace('Bank.Lambda', 'Bank.Sevenths').replace('lambda', 'sevenths').replace('FL', 'F7').replace('LamL', 'Lam7')
(OUT/'Content.lean').write_text(s, encoding='utf-8')
print('Prepared q7 pole palette, content assembly, and 240 local rank certificate modules')
