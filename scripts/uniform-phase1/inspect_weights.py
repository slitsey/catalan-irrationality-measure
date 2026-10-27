from rank_integer import *
for leaf,side in [('D58-L0108','right'),('D58-L0002','left'),('D58-L0203','right')]:
 s=json.loads((BASE/f'complete29/production/{leaf}/{side}.json').read_text());w=lower(BASE/f'complete30/production/{leaf}/{side}.json')
 print(leaf,side,'central',s['leading_central'],'knot',s['knot'],'scale',s['integer_weight_scale'],'a',s['integer_objective']['a'],'lowerkeys',list(w))
 print('LOWER_SCALARS',{k:v for k,v in w.items() if not isinstance(v,(list,dict))})
 cert={int(z['map']):z for z in s['leading_weight_certificates']}
 print('WEIGHTS',[(mp['compressed_map_index'],mp['members'],mp['weight'],cert.get(int(mp['compressed_map_index']),{}).get('at_knot')) for mp in s['active_maps']+s['dropped_zero_weight_maps']])
