module
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialInfJets
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialEndpointSources
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset
open scoped BigOperators
namespace CatalanCore.Li2.NVMod.DataSupport
noncomputable section

def earlierCoefficients (kind : Kind) : List ℕ→List ℤ
  | []=>if kind=.U then [0,1] else [1]
  | t::ts=>coefficientsMul (powerCoefficients 3 [(t:ℤ),1]) (earlierCoefficients kind ts)

theorem earlierCoefficients_spec (A : TypeKey) (ts : List ℕ) :
    (coefficientsPoly (earlierCoefficients A.kind ts)).map (Int.castRingHom ℚ)=earlierPoly A ts := by
  induction ts with
  | nil=>cases hk : A.kind <;> simp [earlierCoefficients,earlierPoly,coefficientsPoly,hk]
  | cons t ts ih=>
    rw [earlierCoefficients,coefficientsPoly_mul,powerCoefficients_spec,
      Polynomial.map_mul,Polynomial.map_pow,ih]
    have hc : (coefficientsPoly ([(t:ℤ),1]:List ℤ)).map (Int.castRingHom ℚ)=X+C (t:ℚ) := by
      simp [coefficientsPoly]
      ring
    rw [hc]
    cases hk : A.kind <;> simp [earlierPoly,hk] <;> ring

def restDenCoefficients (ms : List ℕ) (t : ℕ) : List ℤ :=
  linearProductCoefficients ((ms.filter (fun (m : ℕ)=>m≠t)).map (fun (m : ℕ)=>(m:ℤ)))

theorem restDenCoefficients_spec (A : TypeKey) (ms : List ℕ) (t : ℕ)
    (hn : ms.Nodup) (hs : ms.toFinset=poleSet A) :
    (coefficientsPoly (restDenCoefficients ms t)).map (Int.castRingHom ℚ)=
      poleProd ((poleSet A).erase t) := by
  let ls:=ms.filter (fun (m : ℕ)=>m≠t)
  have hl : ls.toFinset=(poleSet A).erase t := by
    ext m
    have hm : m∈ms ↔ m∈poleSet A := by rw [←hs,List.mem_toFinset]
    simp only [ls,List.mem_toFinset,List.mem_filter,Finset.mem_erase,decide_eq_true_eq]
    simpa only [hm,and_comm]
  have hp:=list_product_polynomial ls (hn.filter _)
  change (coefficientsPoly (linearProductCoefficients (ls.map (fun (m : ℕ)=>(m:ℤ))))).map
    (Int.castRingHom ℚ)=_
  rw [hp,Polynomial.map_prod]
  simp only [Polynomial.map_add,Polynomial.map_X,Polynomial.map_C,Int.coe_castRingHom,Int.cast_natCast]
  rw [hl]
  rfl

def polePhiCoefficients (kind : Kind) (num : List ℤ) (ts : List ℕ) : List ℤ :=
  let e:=earlierCoefficients kind ts
  coefficientsMul (coefficientsMul e e) num

theorem polePhi_from_tables (A : TypeKey) (num : List ℤ) (ms ts : List ℕ) (t : ℕ)
    (hnum : coefficientsPoly num=numeratorZ A) (hn : ms.Nodup)
    (hs : ms.toFinset=poleSet A) (ht : t∈poleSet A) :
    (rfX+rfPoly (C (t:ℚ)))*(rfPoly (earlierPoly A ts))^2*weight A=
      rfPoly ((coefficientsPoly (polePhiCoefficients A.kind num ts)).map (Int.castRingHom ℚ))/
        rfPoly ((coefficientsPoly (restDenCoefficients ms t)).map (Int.castRingHom ℚ)) := by
  have hp : (coefficientsPoly (polePhiCoefficients A.kind num ts)).map (Int.castRingHom ℚ)=
      (earlierPoly A ts)^2*weightNum A := by
    simp only [polePhiCoefficients,coefficientsPoly_mul,Polynomial.map_mul,
      earlierCoefficients_spec,hnum,numeratorZ_map,numeratorK_Q,pow_two]
  rw [hp,restDenCoefficients_spec A ms t hn hs]
  calc
    _=rfPoly ((earlierPoly A ts)^2)*((rfX+rfPoly (C (t:ℚ)))*weight A) := by
      simp only [rfPoly,map_pow]
      ring
    _=rfPoly ((earlierPoly A ts)^2)*(rfPoly (weightNum A)/rfPoly (poleProd ((poleSet A).erase t))) := by
      rw [weight_removed A t ht]
    _=_ := by simp only [rfPoly,map_mul];ring

def partialFromJets (p q : ℤ×ℤ×ℤ) (take : ℕ) : ℚ :=
  let v : ℚ:=(p.1:ℚ)/(q.1:ℚ)
  let sig : ℚ:=(p.2.1:ℚ)/(p.1:ℚ)-(q.2.1:ℚ)/(q.1:ℚ)
  let dsig : ℚ:=(p.2.2:ℚ)/(p.1:ℚ)-((p.2.1:ℚ)/(p.1:ℚ))^2-
    (q.2.2:ℚ)/(q.1:ℚ)+((q.2.1:ℚ)/(q.1:ℚ))^2
  if take=1 then -v*(sig^2+dsig)/2 else v^2*(dsig-sig^2)/2

def partialInfWith (A : TypeKey) (num : List ℤ) (ms ts : List ℕ) (t take : ℕ) : ℚ :=
  if t∈ms then
    let p:=evalJet2 (-(t:ℤ)) (polePhiCoefficients A.kind num ts)
    let q:=evalJet2 (-(t:ℤ)) (restDenCoefficients ms t)
    if p.1=0 ∨ q.1=0 then partialInf A ts t take else partialFromJets p q take
  else partialInf A ts t take

theorem partialInfWith_spec (A : TypeKey) (num : List ℤ) (ms ts : List ℕ) (t take : ℕ)
    (hnum : coefficientsPoly num=numeratorZ A) (hn : ms.Nodup) (hs : ms.toFinset=poleSet A) :
    partialInf A ts t take=partialInfWith A num ms ts t take := by
  unfold partialInfWith
  dsimp only
  split_ifs with ht hz
  · rfl
  · let pc:=polePhiCoefficients A.kind num ts
    let qc:=restDenCoefficients ms t
    let P:=(coefficientsPoly pc).map (Int.castRingHom ℚ)
    let Q:=(coefficientsPoly qc).map (Int.castRingHom ℚ)
    let Φ:=(rfX+rfPoly (C (t:ℚ)))*(rfPoly (earlierPoly A ts))^2*weight A
    have hp:=intJet2_spec pc (-(t:ℤ))
    have hq:=intJet2_spec qc (-(t:ℤ))
    simp only [Int.cast_neg,Int.cast_natCast] at hp hq
    have hp0 : P.eval (-(t:ℚ))≠0 := by
      rw [hp.1]
      exact_mod_cast (not_or.mp hz).1
    have hq0 : Q.eval (-(t:ℚ))≠0 := by
      rw [hq.1]
      exact_mod_cast (not_or.mp hz).2
    have hF : Φ=rfPoly P/rfPoly Q:=polePhi_from_tables A num ms ts t hnum hn hs
      (hs ▸ List.mem_toFinset.mpr ht)
    have hj:=fraction_log_jet Φ P Q (-(t:ℚ)) hp0 hq0 hF
    rw [hp.1,hp.2.1,hp.2.2,hq.1,hq.2.1,hq.2.2] at hj
    unfold partialInf
    change (if take=1 then -rfEval Φ (-(t:ℚ))*((rfEval (rfDeriv Φ/Φ) (-(t:ℚ)))^2+
      rfEval (rfDeriv (rfDeriv Φ/Φ)) (-(t:ℚ)))/2 else
      (rfEval Φ (-(t:ℚ)))^2*(rfEval (rfDeriv (rfDeriv Φ/Φ)) (-(t:ℚ))-
        (rfEval (rfDeriv Φ/Φ) (-(t:ℚ)))^2)/2)=_
    rw [hj.1,hj.2.1,hj.2.2]
    rfl
  · rfl
def weightDerivativeWith (A : TypeKey) (num den : List ℤ) : ℚ :=
  let p:=evalJet2 (0:ℤ) num
  let q:=evalJet2 (0:ℤ) den
  if q.1=0 then rfEval (rfDeriv (weight A)) 0
  else ((p.2.1:ℚ)*(q.1:ℚ)-(p.1:ℚ)*(q.2.1:ℚ))/(q.1:ℚ)^2

theorem weightDerivativeWith_spec (A : TypeKey) (num den : List ℤ)
    (hn : coefficientsPoly num=numeratorZ A) (hd : coefficientsPoly den=denominatorZ A) :
    rfEval (rfDeriv (weight A)) 0=weightDerivativeWith A num den := by
  unfold weightDerivativeWith
  dsimp only
  split_ifs with hz
  · rfl
  · let P:=(coefficientsPoly num).map (Int.castRingHom ℚ)
    let Q:=(coefficientsPoly den).map (Int.castRingHom ℚ)
    have hp:=intJet2_spec num 0
    have hq:=intJet2_spec den 0
    simp only [Int.cast_zero] at hp hq
    have hq0 : Q.eval 0≠0:=by rw [hq.1];exact_mod_cast hz
    have hf : weight A=rfPoly P/rfPoly Q := by
      simp only [P,Q,hn,hd,numeratorZ_map,denominatorZ_map,numeratorK_Q,denominatorK_Q]
      rfl
    rw [eval_derivative_fraction (weight A) P Q 0 hq0 hf,hp.1,hp.2.1,hq.1,hq.2.1]

def infFoldNative (A : TypeKey) (num : List ℤ) (ms : List ℕ) (rho : ℕ→ℚ) :
    List ℕ→ℕ→List ℕ→ℚ
  | [],_,_=>1
  | t::ts,left,earlier=>
    if left=0 then 1 else if 3≤left then
      (rho t)^3*(earlierValue A.kind earlier t)^6*infFoldNative A num ms rho ts (left-3) (earlier++[t])
    else partialInfWith A num ms earlier t left

theorem infFoldNative_spec (A : TypeKey) (num : List ℤ) (ms : List ℕ) (rho : ℕ→ℚ)
    (ts : List ℕ) (left : ℕ) (earlier : List ℕ)
    (hnum : coefficientsPoly num=numeratorZ A) (hn : ms.Nodup) (hs : ms.toFinset=poleSet A)
    (hr : ∀ t∈ts,rho t=residue A t) :
    infFold A ts left earlier=infFoldNative A num ms rho ts left earlier := by
  induction ts generalizing left earlier with
  | nil=>rfl
  | cons t ts ih=>
    simp only [infFold,infFoldNative]
    split_ifs
    · rfl
    · rw [←hr t (by simp),earlierValue_spec,ih (left-3) (earlier++[t]) (fun u hu=>hr u (by simp [hu]))]
    · exact partialInfWith_spec A num ms earlier t left hnum hn hs

def infLeadNative (A : TypeKey) (num den : List ℤ) (ms : List ℕ) (rho : ℕ→ℚ) : ℚ :=
  if A.size=0 then 1 else
  if A.kind=.U then -weightDerivativeWith A num den*infFoldNative A num ms rho (poleList A) (A.size-1) []
  else infFoldNative A num ms rho (poleList A) A.size []

theorem infLeadNative_spec (A : TypeKey) (num den : List ℤ) (ms : List ℕ) (rho : ℕ→ℚ)
    (hnum : coefficientsPoly num=numeratorZ A) (hden : coefficientsPoly den=denominatorZ A)
    (hn : ms.Nodup) (hs : ms.toFinset=poleSet A) (hr : ∀ t∈poleSet A,rho t=residue A t) :
    infLead A=infLeadNative A num den ms rho := by
  have hh:=infFoldNative_spec A num ms rho (poleList A)
    (hnum:=hnum) (hn:=hn) (hs:=hs) (hr:=fun t ht=>hr t ((mem_poleList A t).mp ht))
  unfold infLead infLeadNative
  split_ifs <;> simp only [hh,weightDerivativeWith_spec A num den hnum hden]
#print axioms infLeadNative_spec
#print axioms partialInfWith_spec
end
end CatalanCore.Li2.NVMod.DataSupport
