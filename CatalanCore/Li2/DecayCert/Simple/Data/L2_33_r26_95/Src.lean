module
public import CatalanCore.Li2.DecayCert.Simple.Data.L2_33_r26_95.Logs0
public import CatalanCore.Li2.DecayCert.Simple.Data.L2_33_r26_95.Logs1
public import CatalanCore.Li2.DecayCert.Simple.Data.L2_33_r26_95.Logs2
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open MeasureTheory Set
namespace CatalanCore.Li2.DecayCert.Simple.Data.L2_33_r26_95
open CatalanCore.Li2.DecayCert CatalanCore.Li2.DecayCert.Simple CatalanCore.Li2.DecayCert.LatticeSimple CatalanCore.Li2.DecayCert.LatticeGate
theorem logs_ok : logs.all logEntryOK=true := by simp only [logs,List.all_append,logC00_ok,logC01_ok,logC02_ok,logC03_ok,logC04_ok,logC05_ok,logC06_ok,logC07_ok,logC08_ok,logC09_ok,logC10_ok,logC11_ok,logC12_ok,logC13_ok,Bool.and_self]
theorem s01 : decide (source.z=z ∧ source.Y=input.Y ∧ 1 < source.phi ∧ source.y0=input.first.mid.1-input.first.half.1*((source.phi+source.phi⁻¹)/2) ∧
    source.y0 < 0 ∧ 0 ≤ aux.H ∧ aux.H < -source.y0 ∧ |(-4:ℚ)-source.y0| ≤ aux.H ∧ |(-1:ℚ)-source.y0| ≤ aux.H ∧ 0 < source.MU.length ∧
    input.second.mid=(-5/2,0) ∧ input.second.half=(3/2,0) ∧ 0 < input.first.half.1 ∧
    aux.sm.length=aux.KA+1 ∧ 4+source.y0 < -source.y0)=true := by decide +kernel
theorem s03 : logEntryOK ⟨|z|,source.L⟩=true := by decide +kernel
theorem s04 : logEntryOK ⟨4/input.Y,aux.lU1c⟩=true := by decide +kernel
theorem s05 : boxIn (boxMulF (boxOfQ (input.first.c 0)) aux.lU1c) source.U1c=true := by decide +kernel
theorem s06 : logEntryOK ⟨4/3,aux.lU2c⟩=true := by decide +kernel
theorem s07 : boxIn (boxMulF (boxOfQ (input.second.c 0)) aux.lU2c) source.U2c=true := by decide +kernel
theorem s08 : qIn source.m1 (input.first.c 0)=true := by decide +kernel
theorem s09 : qIn source.m2 (input.second.c 0)=true := by decide +kernel
theorem s10 : scalarLowerCheck ((source.U1y0.1:ℚ)/(S:ℚ)) (u1y0Expr aux input source.phi)=true := by decide +kernel
theorem s11 : scalarUpperCheck (u1y0Expr aux input source.phi) ((source.U1y0.2:ℚ)/(S:ℚ))=true := by decide +kernel
theorem s12 : widthIn source.P1mid source.P1width (q1Q input).reverse=true := by decide +kernel
theorem s13 : widthIn source.PAmid source.PAwidth (atomXList input source.y0 aux.sm aux.KA).reverse=true := by decide +kernel
theorem s14 : listIn source.MU ((List.range source.MU.length).map (wQ input source.y0))=true := by decide +kernel
theorem s15 : (List.range source.MU.length).all (fun k => decide (|wQ input source.y0 k| ≤
    |input.second.c 0| * (max |source.y0+4| |-1-source.y0|)^(k+1)/((k:ℚ)+1)))=true := by decide +kernel
theorem s16 : listIn source.firstOverK (fkQ input)=true := by decide +kernel
theorem s17 : stieltjesMomentFast input.first source.phi aux.KA aux.sm=true := by decide +kernel
theorem s18 : decide (2*mpErrQ (input.second.c 0) (aux.H/(-source.y0)) source.MU.length ≤ (source.globalW:ℚ)/(S:ℚ))=true := by decide +kernel
theorem s19 : decide (2*mpErrQ (input.first.c 0) ((max (-1-source.y0) (4+source.y0))/(-source.y0)) aux.KA ≤ (source.globalA:ℚ)/(S:ℚ))=true := by decide +kernel
theorem s20 : decide (aux.qI=((qListIntegral (ownXList input)).reverse.map boxOfQ))=true := decide_eq_true rfl
theorem s21 : decide (aux.qAI=((qListIntegral (atomXList input source.y0 aux.sm aux.KA)).reverse.map boxOfQ))=true := decide_eq_true rfl
theorem source_ok : simpleSourceCheck z input source logs aux=true := by
  simp only [simpleSourceCheck,Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨s01,logs_ok⟩,s03⟩,s04⟩,s05⟩,s06⟩,s07⟩,s08⟩,s09⟩,s10⟩,s11⟩,s12⟩,s13⟩,s14⟩,s15⟩,s16⟩,s17⟩,s18⟩,s19⟩,s20⟩,s21⟩
end CatalanCore.Li2.DecayCert.Simple.Data.L2_33_r26_95
