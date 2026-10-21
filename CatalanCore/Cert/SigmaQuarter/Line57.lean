module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line57m0 : Macro := { x0 := (976735961088), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8981392668518159529992619811),(4676417126450865839373221888),(4903905780403743948800),(0),(886973340089086509056),(4211126582777902)), boxes := [
    (((976702406656),(976769515520),(0),(0)),((651134937770),(651179677014),(-7296844398),(0)))
] }
theorem Line57m0_far : farOK pts Line57m0 := by decide +kernel
theorem Line57m0_ok : axisOK pts Line57m0 = true := by decide +kernel
def Line57m1 : Macro := { x0 := (976803069952), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8990534847006334571859744710),(4676146695360948255030181888),(4904194010779895660544),(0),(886973340089086509056),(4210625117088125)), boxes := [
    (((976769515520),(976836624384),(0),(0)),((651179677013),(651224416256),(-7296832816),(0)))
] }
theorem Line57m1_far : farOK pts Line57m1 := by decide +kernel
theorem Line57m1_ok : axisOK pts Line57m1 = true := by decide +kernel
def Line57m2 : Macro := { x0 := (976870178816), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8999660665080275388825291486),(4675876119672568289579040768),(4904482241156047372288),(0),(886973340089086509056),(4210123596993679)), boxes := [
    (((976836624384),(976903733248),(0),(0)),((651224416256),(651269155499),(-7296820888),(0)))
] }
theorem Line57m2_far : farOK pts Line57m2 := by decide +kernel
theorem Line57m2_ok : axisOK pts Line57m2 = true := by decide +kernel
def Line57m3 : Macro := { x0 := (976937287680), y0 := (0), i0 := 1200, i1 := 1200, fd := ((9008793408520932075910668850),(4675606006644845286049972224),(4904770471532199084032),(0),(886973340089086509056),(4209622527000432)), boxes := [
    (((976903733248),(976970842112),(0),(0)),((651269155498),(651313894742),(-7296809297),(0)))
] }
theorem Line57m3_far : farOK pts Line57m3 := by decide +kernel
theorem Line57m3_ok : axisOK pts Line57m3 = true := by decide +kernel
def Line57m4 : Macro := { x0 := (977004396544), y0 := (0), i0 := 1200, i1 := 1200, fd := ((9017914311455717502513012097),(4675335532351684832608387072),(4905058701908350795776),(0),(886973340089086509056),(4209121201148395)), boxes := [
    (((976970842112),(977037950976),(0),(0)),((651313894741),(651358633984),(-7296796737),(0)))
] }
theorem Line57m4_far : farOK pts Line57m4 := by decide +kernel
theorem Line57m4_ok : axisOK pts Line57m4 = true := by decide +kernel
def Line57m5 : Macro := { x0 := (977071505408), y0 := (0), i0 := 1200, i1 := 1200, fd := ((9027038916760545995023966935),(4675065421625031350735077376),(4905346932284502507520),(0),(886973340089086509056),(4208620257566476)), boxes := [
    (((977037950976),(977105059840),(0),(0)),((651358633984),(651403373227),(-7296784755),(0)))
] }
theorem Line57m5_far : farOK pts Line57m5 := by decide +kernel
theorem Line57m5_ok : axisOK pts Line57m5 = true := by decide +kernel
def Line57m6 : Macro := { x0 := (977138614272), y0 := (0), i0 := 1200, i1 := 1200, fd := ((9036172034906019956389102347),(4674795293111560909699678208),(4905635162660654219264),(0),(886973340089086509056),(4208119365484309)), boxes := [
    (((977105059840),(977172168704),(0),(0)),((651403373226),(651448112470),(-7296772570),(0)))
] }
theorem Line57m6_far : farOK pts Line57m6 := by decide +kernel
theorem Line57m6_ok : axisOK pts Line57m6 = true := by decide +kernel
def Line57m7 : Macro := { x0 := (977205723136), y0 := (0), i0 := 1200, i1 := 1200, fd := ((9045295653490826166897175289),(4674524864210017254462062592),(4905923393036805931008),(0),(886973340089086509056),(4207618273150606)), boxes := [
    (((977172168704),(977239277568),(0),(0)),((651448112469),(651492851712),(-7296760438),(0)))
] }
theorem Line57m7_far : farOK pts Line57m7 := by decide +kernel
theorem Line57m7_ok : axisOK pts Line57m7 = true := by decide +kernel
def Line57Data : List Macro := [Line57m0,Line57m1,Line57m2,Line57m3,Line57m4,Line57m5,Line57m6,Line57m7]
theorem Line57_farAll : ∀ m ∈ Line57Data, farOK pts m := by
  intro m hm
  simp only [Line57Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line57m0_far,Line57m1_far,Line57m2_far,Line57m3_far,Line57m4_far,Line57m5_far,Line57m6_far,Line57m7_far]
theorem Line57_okAll : ∀ m ∈ Line57Data, axisOK pts m = true := by
  intro m hm
  simp only [Line57Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line57m0_ok,Line57m1_ok,Line57m2_ok,Line57m3_ok,Line57m4_ok,Line57m5_ok,Line57m6_ok,Line57m7_ok]
end CatalanCore.Cert.SigmaQuarter
