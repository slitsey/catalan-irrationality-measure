"""Assemble coherent node-table lookup certificates from the individual checked nodes."""
from decay_tables import *
from decay_emit import raw
out=WORK/'CatalanCore/Uniform/Decay/Optimization'
lines=['import CatalanCore.Uniform.Decay.Optimization.Tables','set_option Elab.async false','set_option profiler true','set_option profiler.threshold 1','set_option maxRecDepth 100000','namespace CatalanCore.Uniform.Decay.Optimization','open CatalanCore.Uniform.Decay.SignedPilot']
for kind,number,code,den in [('log',65,1,64),('atan',129,2,128)]:
    inputs=[f'({code},{64+j if code==1 else j},{den},0)'for j in range(number)]
    lines +=[f'def {kind}NodeInputs : List Input := ['+', '.join(inputs)+']',f'theorem {kind}Nodes_check : evalInputs {kind}NodeInputs = some {kind}Nodes :=\n  '+''.join(f'evalInputs_cons {kind}Node{j} ('for j in range(number))+'(by rfl)'+')'*number]
lines +=['#print axioms logNodes_check','#print axioms atanNodes_check','end CatalanCore.Uniform.Decay.Optimization']
(out/'TablesSound.lean').write_text('\n'.join(lines)+'\n',encoding='utf8')
print('SHARED_NODE_TABLE_ASSEMBLY_GENERATED',flush=True)
