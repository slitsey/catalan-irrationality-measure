module

public import CatalanMeasure.GenD.Signed.RouteI.RowCert.RadOKP
public import CatalanMeasure.GenD.Signed.RouteI.RowCert.CovP0
public import CatalanMeasure.GenD.Signed.RouteI.RowCert.CovP1
public import CatalanMeasure.GenD.Signed.RouteI.RowCert.CovP2

@[expose] public section

set_option Elab.async false
set_option maxRecDepth 100000
set_option autoImplicit false

/-!
# The radial field of sign P through the cover

kcost: the small end, one evaluation; the pieces are checked in their modules.
-/

namespace CatalanMeasure.GenD.Signed.RouteI.RowCert

open CatalanMeasure.GenD.Signed.RouteI.FreeRowCap0
open CatalanMeasure.GenD.Signed.RouteI.MarkedPilot
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceTail
open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.CapFields.CapSource
open CatalanMeasure.GenD.Signed.RouteI.CapSourceData
open CatalanMeasure.Signed.ChebSquare
open CatalanMeasure.GenD.Signed.Davis.CircleCheb
open Set
open CatalanMeasure.GenD.Signed.RouteI.OrdHf

theorem csP : 0 ≤ CP.s := by decide +kernel -- kcost: one rational
theorem caP : 0 ≤ CP.α := by decide +kernel -- kcost: one rational
theorem ckP : 2 * CP.s + mc4 CP.Cl 0 * CP.α ^ 2 ≤ (20903017 / 524288) := by
  decide +kernel -- kcost: 19 rational terms
theorem cxP : (CP.Bs.all fun B => decide ((1 / 1000) ≤ B.rho)) = true := by
  decide +kernel -- kcost: 17 comparisons at most
theorem cmP : smallY CP.W (1 / 1000) CP.Bs + max (-CP.evC 0) (-CP.evC (1 / 1000)) +
    mc4 CP.Cl 0 * CP.α ^ 2 * (1 / 1000) ^ 2 / 8 ≤ 0 := by
  decide +kernel -- kcost: 17 sums of 224 terms, two Chebyshev evaluations
theorem cbP : ∀ B ∈ CP.Bs, 0 < B.rho ∧ 0 ≤ B.M ∧ Real.log B.rho ≤ B.sg := blks_ok RP2 bP hq0P allP
theorem smallP : ∀ t ∈ Ioc (0 : ℝ) (((1 / 1000) : ℚ) : ℝ), CP.Phi t ≤ ((0 : ℚ) : ℝ) :=
  small_cover CP csP rfl rfl (by norm_num) (by norm_num) cbP
    (fun B hB => by simpa using List.all_eq_true.1 cxP B hB) cmP
theorem cvP : ∀ t ∈ Icc (((1 / 1000) : ℚ) : ℝ) (((1 / 1) : ℚ) : ℝ), CP.Phi t ≤ ((0 : ℚ) : ℝ) := by
  have p0 := piece_range CP csP caP cbP ckP pcP0
  have p1 := piece_range CP csP caP cbP ckP pcP1
  have p2 := piece_range CP csP caP cbP ckP pcP2
  have p3 := piece_range CP csP caP cbP ckP pcP3
  have p4 := piece_range CP csP caP cbP ckP pcP4
  have p5 := piece_range CP csP caP cbP ckP pcP5
  have p6 := piece_range CP csP caP cbP ckP pcP6
  have p7 := piece_range CP csP caP cbP ckP pcP7
  have p8 := piece_range CP csP caP cbP ckP pcP8
  have p9 := piece_range CP csP caP cbP ckP pcP9
  have p10 := piece_range CP csP caP cbP ckP pcP10
  have p11 := piece_range CP csP caP cbP ckP pcP11
  have p12 := piece_range CP csP caP cbP ckP pcP12
  have p13 := piece_range CP csP caP cbP ckP pcP13
  have p14 := piece_range CP csP caP cbP ckP pcP14
  have p15 := piece_range CP csP caP cbP ckP pcP15
  have p16 := piece_range CP csP caP cbP ckP pcP16
  have p17 := piece_range CP csP caP cbP ckP pcP17
  have p18 := piece_range CP csP caP cbP ckP pcP18
  have p19 := piece_range CP csP caP cbP ckP pcP19
  have p20 := piece_range CP csP caP cbP ckP pcP20
  have p21 := piece_range CP csP caP cbP ckP pcP21
  have p22 := piece_range CP csP caP cbP ckP pcP22
  have p23 := piece_range CP csP caP cbP ckP pcP23
  have p24 := piece_range CP csP caP cbP ckP pcP24
  have p25 := piece_range CP csP caP cbP ckP pcP25
  have p26 := piece_range CP csP caP cbP ckP pcP26
  have p27 := piece_range CP csP caP cbP ckP pcP27
  have p28 := piece_range CP csP caP cbP ckP pcP28
  have p29 := piece_range CP csP caP cbP ckP pcP29
  have p30 := piece_range CP csP caP cbP ckP pcP30
  have p31 := piece_range CP csP caP cbP ckP pcP31
  have p32 := piece_range CP csP caP cbP ckP pcP32
  have p33 := piece_range CP csP caP cbP ckP pcP33
  have p34 := piece_range CP csP caP cbP ckP pcP34
  have p35 := piece_range CP csP caP cbP ckP pcP35
  have p36 := piece_range CP csP caP cbP ckP pcP36
  have p37 := piece_range CP csP caP cbP ckP pcP37
  have p38 := piece_range CP csP caP cbP ckP pcP38
  have p39 := piece_range CP csP caP cbP ckP pcP39
  have p40 := piece_range CP csP caP cbP ckP pcP40
  have p41 := piece_range CP csP caP cbP ckP pcP41
  have p42 := piece_range CP csP caP cbP ckP pcP42
  have p43 := piece_range CP csP caP cbP ckP pcP43
  have p44 := piece_range CP csP caP cbP ckP pcP44
  have p45 := piece_range CP csP caP cbP ckP pcP45
  have p46 := piece_range CP csP caP cbP ckP pcP46
  have p47 := piece_range CP csP caP cbP ckP pcP47
  have p48 := piece_range CP csP caP cbP ckP pcP48
  have p49 := piece_range CP csP caP cbP ckP pcP49
  have p50 := piece_range CP csP caP cbP ckP pcP50
  have p51 := piece_range CP csP caP cbP ckP pcP51
  have p52 := piece_range CP csP caP cbP ckP pcP52
  have p53 := piece_range CP csP caP cbP ckP pcP53
  have p54 := piece_range CP csP caP cbP ckP pcP54
  have p55 := piece_range CP csP caP cbP ckP pcP55
  have p56 := piece_range CP csP caP cbP ckP pcP56
  have p57 := piece_range CP csP caP cbP ckP pcP57
  have p58 := piece_range CP csP caP cbP ckP pcP58
  have p59 := piece_range CP csP caP cbP ckP pcP59
  have p60 := piece_range CP csP caP cbP ckP pcP60
  have p61 := piece_range CP csP caP cbP ckP pcP61
  have p62 := piece_range CP csP caP cbP ckP pcP62
  have p63 := piece_range CP csP caP cbP ckP pcP63
  have p64 := piece_range CP csP caP cbP ckP pcP64
  have p65 := piece_range CP csP caP cbP ckP pcP65
  have p66 := piece_range CP csP caP cbP ckP pcP66
  have p67 := piece_range CP csP caP cbP ckP pcP67
  have p68 := piece_range CP csP caP cbP ckP pcP68
  have p69 := piece_range CP csP caP cbP ckP pcP69
  have p70 := piece_range CP csP caP cbP ckP pcP70
  have p71 := piece_range CP csP caP cbP ckP pcP71
  have p72 := piece_range CP csP caP cbP ckP pcP72
  have p73 := piece_range CP csP caP cbP ckP pcP73
  have p74 := piece_range CP csP caP cbP ckP pcP74
  have p75 := piece_range CP csP caP cbP ckP pcP75
  have p76 := piece_range CP csP caP cbP ckP pcP76
  have p77 := piece_range CP csP caP cbP ckP pcP77
  have p78 := piece_range CP csP caP cbP ckP pcP78
  have p79 := piece_range CP csP caP cbP ckP pcP79
  have q0 := p0
  have q1 := glue p1 q0
  have q2 := glue p2 q1
  have q3 := glue p3 q2
  have q4 := glue p4 q3
  have q5 := glue p5 q4
  have q6 := glue p6 q5
  have q7 := glue p7 q6
  have q8 := glue p8 q7
  have q9 := glue p9 q8
  have q10 := glue p10 q9
  have q11 := glue p11 q10
  have q12 := glue p12 q11
  have q13 := glue p13 q12
  have q14 := glue p14 q13
  have q15 := glue p15 q14
  have q16 := glue p16 q15
  have q17 := glue p17 q16
  have q18 := glue p18 q17
  have q19 := glue p19 q18
  have q20 := glue p20 q19
  have q21 := glue p21 q20
  have q22 := glue p22 q21
  have q23 := glue p23 q22
  have q24 := glue p24 q23
  have q25 := glue p25 q24
  have q26 := glue p26 q25
  have q27 := glue p27 q26
  have q28 := glue p28 q27
  have q29 := glue p29 q28
  have q30 := glue p30 q29
  have q31 := glue p31 q30
  have q32 := glue p32 q31
  have q33 := glue p33 q32
  have q34 := glue p34 q33
  have q35 := glue p35 q34
  have q36 := glue p36 q35
  have q37 := glue p37 q36
  have q38 := glue p38 q37
  have q39 := glue p39 q38
  have q40 := glue p40 q39
  have q41 := glue p41 q40
  have q42 := glue p42 q41
  have q43 := glue p43 q42
  have q44 := glue p44 q43
  have q45 := glue p45 q44
  have q46 := glue p46 q45
  have q47 := glue p47 q46
  have q48 := glue p48 q47
  have q49 := glue p49 q48
  have q50 := glue p50 q49
  have q51 := glue p51 q50
  have q52 := glue p52 q51
  have q53 := glue p53 q52
  have q54 := glue p54 q53
  have q55 := glue p55 q54
  have q56 := glue p56 q55
  have q57 := glue p57 q56
  have q58 := glue p58 q57
  have q59 := glue p59 q58
  have q60 := glue p60 q59
  have q61 := glue p61 q60
  have q62 := glue p62 q61
  have q63 := glue p63 q62
  have q64 := glue p64 q63
  have q65 := glue p65 q64
  have q66 := glue p66 q65
  have q67 := glue p67 q66
  have q68 := glue p68 q67
  have q69 := glue p69 q68
  have q70 := glue p70 q69
  have q71 := glue p71 q70
  have q72 := glue p72 q71
  have q73 := glue p73 q72
  have q74 := glue p74 q73
  have q75 := glue p75 q74
  have q76 := glue p76 q75
  have q77 := glue p77 q76
  have q78 := glue p78 q77
  have q79 := glue p79 q78
  exact q79
theorem hRadP : ∀ t ∈ Ioo (0 : ℝ) 1, capSource.radialA (Trunc.finite 384) Sign.pos (sgOf Sign.pos * t) -
    39 / 29 * Real.log (1 + t ^ 2) + (((0 : ℚ)) : ℝ) * Real.log t ≤
    rawSum clP 0 (2 * t - 1) / ((dPc : ℕ) : ℝ) + (((0 : ℚ) : ℝ) + ((errS RP2 16 : ℚ) : ℝ)) :=
  hRad2_pos radP rfl CP (dP := dPc) (by norm_num [dPc]) (cl := clP) (x0 := (1 / 1000)) (Bud := 0) rfl rfl rfl rfl rfl rfl
    smallP (fun t ht => cvP t (by simpa using ht)) (fun t ht => ⟨ht.1, ht.2.le⟩)

end CatalanMeasure.GenD.Signed.RouteI.RowCert
