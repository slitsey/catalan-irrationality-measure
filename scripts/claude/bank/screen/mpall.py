import subprocess,sys,os
P=r'C:\Users\seanl\Documents\Codex\2026-10-11\plea\outputs\Compatibility programme'
R=P+r'\hybrid-exact-receipts-2026-10-27';S7=P+r'\sevenths-decay-2026-10-27\exact-check';OUT=P+r'\decay-cell-reduction-2026-10-28\d16'
for t,d in (('THIRD',R),('LAMB',R),('CHI3',R),('A',S7)):
    with open(OUT+rf'\mp-{t}.log','w') as lg:
        subprocess.run([sys.executable,'-I','-X','utf8',r'scripts\claude\bank\screen\mp.py',d+rf'\exact-{t}.json',OUT+rf'\mp-{t}.json'],stdout=lg,stderr=subprocess.STDOUT)
