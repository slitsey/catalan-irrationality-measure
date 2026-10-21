module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line71m0 : Macro := { x0 := (1010391056384), y0 := (0), i0 := 1200, i1 := 1200, fd := ((13496768386430939440074040865),(4544642668760630218442539008),(5048453314043827388416),(0),(886973340089086509056),(3970514298156524)), boxes := [
    (((1009317314560),(1011464798208),(0),(0)),((672878209706),(674309865472),(-7296153116),(0)))
] }
theorem Line71m0_far : farOK pts Line71m0 := by decide +kernel
theorem Line71m0_ok : axisOK pts Line71m0 = true := by decide +kernel
def Line71m1 : Macro := { x0 := (1012538540032), y0 := (0), i0 := 1200, i1 := 1200, fd := ((13780543386204702627290916835),(4536486425058965050035666944),(5057676686080682164224),(0),(886973340089086509056),(3955868979842758)), boxes := [
    (((1011464798208),(1013612281856),(0),(0)),((674309865472),(675741521238),(-7293638326),(0)))
] }
theorem Line71m1_far : farOK pts Line71m1 := by decide +kernel
theorem Line71m1_ok : axisOK pts Line71m1 = true := by decide +kernel
def Line71m2 : Macro := { x0 := (1014686023680), y0 := (0), i0 := 1200, i1 := 1200, fd := ((14063824843361417100512659130),(4528359025345648057755435008),(5066900058117536940032),(0),(886973340089086509056),(3941304500453889)), boxes := [
    (((1013612281856),(1015759765504),(0),(0)),((675741521237),(677173177003),(-7290968631),(0)))
] }
theorem Line71m2_far : farOK pts Line71m2 := by decide +kernel
theorem Line71m2_ok : axisOK pts Line71m2 = true := by decide +kernel
def Line71m3 : Macro := { x0 := (1016833507328), y0 := (0), i0 := 1200, i1 := 1200, fd := ((14346590267844553247124563080),(4520261135893194541307330560),(5076123430154391715840),(0),(886973340089086509056),(3926820956857970)), boxes := [
    (((1015759765504),(1017907249152),(0),(0)),((677173177002),(678604832768),(-7288145614),(0)))
] }
theorem Line71m3_far : farOK pts Line71m3 := by decide +kernel
theorem Line71m3_ok : axisOK pts Line71m3 = true := by decide +kernel
def Line71m4 : Macro := { x0 := (1018980990976), y0 := (0), i0 := 1200, i1 := 1200, fd := ((14628839741233819616136198562),(4512192119807201689800343552),(5085346802191246491648),(0),(886973340089086509056),(3912417339941794)), boxes := [
    (((1017907249152),(1020054732800),(0),(0)),((678604832768),(680036488534),(-7285168343),(0)))
] }
theorem Line71m4_far : farOK pts Line71m4 := by decide +kernel
theorem Line71m4_ok : axisOK pts Line71m4 = true := by decide +kernel
def Line71m5 : Macro := { x0 := (1021128474624), y0 := (0), i0 := 1200, i1 := 1200, fd := ((14910609507131411513564639950),(4504151436639796337490591744),(5094570174228101267456),(0),(886973340089086509056),(3898092744353084)), boxes := [
    (((1020054732800),(1022202216448),(0),(0)),((680036488533),(681468144299),(-7282028633),(0)))
] }
theorem Line71m5_far : farOK pts Line71m5 := by decide +kernel
theorem Line71m5_ok : axisOK pts Line71m5 = true := by decide +kernel
def Line71m6 : Macro := { x0 := (1023275958272), y0 := (0), i0 := 1200, i1 := 1200, fd := ((15191865718171148787854562617),(4496139843735076059244199936),(5103793546264956043264),(0),(886973340089086509056),(3883847336163010)), boxes := [
    (((1022202216448),(1024349700096),(0),(0)),((681468144298),(682899800064),(-7278729715),(0)))
] }
theorem Line71m6_far : farOK pts Line71m6 := by decide +kernel
theorem Line71m6_ok : axisOK pts Line71m6 = true := by decide +kernel
def Line71m7 : Macro := { x0 := (1025423441920), y0 := (0), i0 := 1200, i1 := 1200, fd := ((15472630311029247469561919262),(4488156646385026785955938304),(5113016918301810819072),(0),(886973340089086509056),(3869680098785659)), boxes := [
    (((1024349700096),(1026497183744),(0),(0)),((682899800064),(684331455830),(-7275266939),(0)))
] }
theorem Line71m7_far : farOK pts Line71m7 := by decide +kernel
theorem Line71m7_ok : axisOK pts Line71m7 = true := by decide +kernel
def Line71Data : List Macro := [Line71m0,Line71m1,Line71m2,Line71m3,Line71m4,Line71m5,Line71m6,Line71m7]
theorem Line71_farAll : ∀ m ∈ Line71Data, farOK pts m := by
  intro m hm
  simp only [Line71Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line71m0_far,Line71m1_far,Line71m2_far,Line71m3_far,Line71m4_far,Line71m5_far,Line71m6_far,Line71m7_far]
theorem Line71_okAll : ∀ m ∈ Line71Data, axisOK pts m = true := by
  intro m hm
  simp only [Line71Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line71m0_ok,Line71m1_ok,Line71m2_ok,Line71m3_ok,Line71m4_ok,Line71m5_ok,Line71m6_ok,Line71m7_ok]
end CatalanCore.Cert.SigmaQuarter
