import subprocess,sys,os,time
P=r'C:\Users\seanl\Documents\Codex\2026-10-11\plea\outputs\Compatibility programme'
R=P+r'\hybrid-exact-receipts-2026-10-27';S7=P+r'\sevenths-decay-2026-10-27\exact-check';O=P+r'\decay-cell-reduction-2026-10-28\d16'
for t,d in (('THIRD',R),('LAMB',R),('CHI3',R),('A',S7)):
    while not os.path.exists(O+rf'\asm-{t}.json'):time.sleep(10)
    time.sleep(3)
    subprocess.run([sys.executable,'-I','-X','utf8',r'scripts\claude\bank\screen\summary.py',d+rf'\exact-{t}.json',O+rf'\rec-{t}.json',O+rf'\bp-{t}.json',O+rf'\asm-{t}.json',O+rf'\mp-{t}.json',O+rf'\sum-{t}.json'],stdout=open(O+rf'\sum-{t}.log','w'),stderr=subprocess.STDOUT)
