from pathlib import Path
R=Path(r'C:/Users/seanl/Documents/Codex/2026-10-11/plea/work/catalan-uniform')
B=R/'CatalanCore/Uniform/Bank/Sevenths'
s=(R/'CatalanCore/Uniform/Bank/Thirds/Energy.lean').read_text(encoding='utf-8-sig')
s=s.replace('Bank.Thirds.Geom','Bank.Sevenths.Geom\nimport CatalanLambda.Cert.LogBounds')
s=s.replace('Bank.Thirds','Bank.Sevenths').replace('G310','F7').replace('RP310','RP7')
s=s.replace('1587 / 800','169 / 96').replace('169 / 200','49 / 72').replace('9 / 400','1 / 144')
s=s.replace('13 / 10','7 / 6').replace('3 / 10','1 / 6').replace('-13 / 10','-7 / 6').replace('-3 / 10','-1 / 6')
s=s.replace('log1310_le','log76_le').replace('log310_ge','log16_ge')
s=s.replace('3 / 23','1 / 13').replace('7 / 13','5 / 7').replace('10 / 3','6')
s=s.replace('30','60')
s=s.replace('867481404213 / 500000000000','102691611939 / 62500000000')
s=s.replace('((3 : ℝ) / 23)','((1 : ℝ) / 13)').replace('((7 : ℝ) / 13)','((5 : ℝ) / 7)')
s += '\n#print axioms CatalanCore.Uniform.Bank.Sevenths.Inu_le_nodeEnergy\n'
(B/'Energy.lean').write_text(s,encoding='utf-8')
