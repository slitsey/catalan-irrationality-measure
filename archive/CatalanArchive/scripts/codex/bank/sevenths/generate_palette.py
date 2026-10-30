from pathlib import Path
p=Path(__file__).with_name('prepare_rank.py')
exec(compile(p.read_text(encoding='utf-8'),str(p),'exec'),{'__file__':str(p)})
