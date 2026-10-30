def assignment(case, cell, name, tnames):
 names=sorted({tnames[v['type_id']] for v in cell['runs']})
 u,v=Q(cell['left']),Q(cell['right']);j=case['root_index']
 ps='''(a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : 1 ≤ a ∧ a ≤ 6) (hp64 : 64 ≤ p) (hp7 : ¬ p ∣ 7)
    (hrp : r ≤ 6 * p) (hm1 : 12 * m ≤ r + 6)'''
 txt='\n'
 for ri,run in enumerate(cell['runs']):
  A,B,D=line(run['lower']);AA,BB,DD=line(run['upper']);res=run['residue']
  txt+=f'''noncomputable def {name}_test{ri} (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p) : Prop :=
  x.val % 2 = {res} ∧ 4 ≤ x.val ∧
    ({A} : ℤ) * r + ({B} : ℤ) * p + {4*D} ≤ ({D} : ℤ) * x.val ∧
    ({DD} : ℤ) * x.val ≤ ({AA} : ℤ) * r + ({BB} : ℤ) * p - {4*DD} ∧
    x.val ∉ deletedResidues r p s
'''
 txt+=f'\nnoncomputable def {name}_assignment '+ps+''' : ZMod p → FibreCert := fun x =>
'''
 for ri,run in enumerate(cell['runs']):
  tn=tnames[run['type_id']]
  txt+=f'  if {name}_test{ri} r p s x then {tn} else\n'
 txt+='  trivCert (seventhsPoleSplit a p r m ha hp64 hp7 hrp hm1) (rowsOf r m s) (colsOf r m s) x\n'
 dens=', '.join(n+'_den' for n in names)
 txt+=f'\ntheorem {name}_assignment_valid '+ps+f'''
    (hr : r % 2 = 0) (hp : p % 2 = 1) (hm2 : r ≤ 12 * m + 6)
    (hleft : {u.numerator} * r ≤ {u.denominator} * p)
    (hright : {v.denominator} * p ≤ {v.numerator} * r)
    (k : ℕ) (hk : k < p) (hroot : 7 * k + a = {j} * p)
    (hden : ∀ N ∈ ([{dens}] : List ℕ), ¬ p ∣ N) (x : ZMod p) :
    ({name}_assignment a p r m s ha hp64 hp7 hrp hm1 x).Ok ∧
    ({name}_assignment a p r m s ha hp64 hp7 hrp hm1 x).Integral p ∧
    Realizes (seventhsPoleSplit a p r m ha hp64 hp7 hrp hm1)
      (rowsOf r m s) (colsOf r m s) x
      ({name}_assignment a p r m s ha hp64 hp7 hrp hm1 x) := by
  have hxp : x.val < p := ZMod.val_lt x
  unfold {name}_assignment
  split_ifs with '''+' '.join(f'h{i}' for i in range(len(cell['runs'])))+'\n'
 for ri,run in enumerate(cell['runs']):
  tn=tnames[run['type_id']]
  txt+=f'''  · obtain ⟨hpar, hx, hlo, hhi, hgood⟩ := h{ri}
    have h := {name}_run{ri} a p (r + 2 * m) hp7 (D7Frame_coeff_mem a p)
      (D7Frame_den_units a p hp7) (by omega) (D7Frame_band a r m p ha hp64 hrp hm1)
      r m x.val s hr hp hpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
      k ha hk hroot hgood (hden {tn}_den (by simp))
    simpa only [seventhsPoleSplit, ZMod.natCast_zmod_val] using h
'''
 txt+='''  · exact ⟨FibreCert.triv_ok _ _ _ _, FibreCert.triv_integral _ _ _ _,
      trivCert_realizes _ _ _ _⟩
'''
 for i,ri in enumerate(cell['runs']):
  for jj in range(i+1,len(cell['runs'])):
   rj=cell['runs'][jj]
   if ri['residue']!=rj['residue']:continue
   txt+=f"""
private theorem {name}_disjoint{i}_{jj} (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p)
    (hleft : {u.numerator} * r ≤ {u.denominator} * p)
    (hright : {v.denominator} * p ≤ {v.numerator} * r) :
    ¬ ({name}_test{i} r p s x ∧ {name}_test{jj} r p s x) := by
  rintro ⟨⟨hpar0, hx0, hlo0, hhi0, hgood0⟩, ⟨hpar1, hx1, hlo1, hhi1, hgood1⟩⟩
  omega
"""
 for i,run in enumerate(cell['runs']):
  tn=tnames[run['type_id']]
  txt+=f'\ntheorem {name}_assignment_on_run{i} '+ps+f"""
    (hleft : {u.numerator} * r ≤ {u.denominator} * p)
    (hright : {v.denominator} * p ≤ {v.numerator} * r) (x : ZMod p)
    (hi : {name}_test{i} r p s x) :
    {name}_assignment a p r m s ha hp64 hp7 hrp hm1 x = {tn} := by
"""
  for jj in range(i):
   if cell['runs'][jj]['residue']==run['residue']:
    txt+=f'  have hn{jj} : ¬ {name}_test{jj} r p s x := fun hj => {name}_disjoint{jj}_{i} r p s x hleft hright ⟨hj, hi⟩\n'
   else:
    txt+=f"""  have hn{jj} : ¬ {name}_test{jj} r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
"""
  simps=', '.join([name+'_assignment']+[f'if_neg hn{jj}' for jj in range(i)]+['if_pos hi'])
  txt+=f'  simp only [{simps}]\n'
 txt+=f'\n#print axioms {name}_assignment_valid\n#print axioms {name}_assignment_on_run0\n'
 return txt
