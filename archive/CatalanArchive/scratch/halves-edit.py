p='CatalanCore/Uniform/Bank/HalvesContent/Auto.lean'
s=open(p,encoding='utf-8',newline='').read()
print(repr(s[s.find('bankData.cat')-5:s.find('bankData.cat')+60]))
a="bankData.cat :=\n  catValid_bankUF (twoTermInst"
assert a in s
s=s.replace(a,"bankData.cat := by\n  rw [bankData_cat]\n  exact catValid_bankUFwP (twoTermInst",1)
w="    [(3, 4), (4, 4), (4, 5), (5, 5), (5, 6), (6, 6), (6, 7), (7, 7), (7, 8)]"
assert w in s
s=s.replace(w,"    bankWins bankPres",1)
open(p,'w',encoding='utf-8',newline='').write(s)
for f in ('AutoMeasure','Bound'):
    p=f'CatalanCore/Uniform/Bank/HalvesContent/{f}.lean'
    s=open(p,encoding='utf-8',newline='').read().replace('327 / 50','3263 / 500').replace('327/50','3263/500')
    open(p,'w',encoding='utf-8',newline='').write(s)
