import subprocess,sys
F=r'C:\Users\seanl\Documents\Codex\2026-10-11\plea\outputs\Compatibility programme\decay-cell-reduction-2026-10-28\d16\fewer'
for spec in sys.argv[1:]:
    t,lay=spec.split('-')
    subprocess.run([sys.executable,'-I','-X','utf8',r'scripts\claude\bank\screen\pipe.py',F+rf'\exact-{t}-{lay}.json',f'{t}-{lay}'])
