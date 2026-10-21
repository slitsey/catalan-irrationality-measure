module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line12m0 : Macro := { x0 := (959455428608), y0 := (0), i0 := 1200, i1 := 1200, fd := ((6611783266618839416116583042),(4747095303517262919167180800),(4829686458544678174720),(0),(886973340089086509056),(4343297435112263)), boxes := [
    (((959388319744),(959522537472),(0),(0)),((639592213162),(639681691648),(-7296493611),(0)))
] }
theorem Line12m0_far : farOK pts Line12m0 := by decide +kernel
theorem Line12m0_ok : axisOK pts Line12m0 = true := by decide +kernel
def Line12m1 : Macro := { x0 := (959589646336), y0 := (0), i0 := 1200, i1 := 1200, fd := ((6630340978552818853190693024),(4746538120512801509128732672),(4830262919296981598208),(0),(886973340089086509056),(4342246930745307)), boxes := [
    (((959522537472),(959656755200),(0),(0)),((639681691648),(639771170134),(-7296532187),(0)))
] }
theorem Line12m1_far : farOK pts Line12m1 := by decide +kernel
theorem Line12m1_ok : axisOK pts Line12m1 = true := by decide +kernel
def Line12m2 : Macro := { x0 := (959723864064), y0 := (0), i0 := 1200, i1 := 1200, fd := ((6648868811125716570762813959),(4745981194848364536389238784),(4830839380049285021696),(0),(886973340089086509056),(4341196924570482)), boxes := [
    (((959656755200),(959790972928),(0),(0)),((639771170133),(639860648619),(-7296568149),(0)))
] }
theorem Line12m2_far : farOK pts Line12m2 := by decide +kernel
theorem Line12m2_ok : axisOK pts Line12m2 = true := by decide +kernel
def Line12m3 : Macro := { x0 := (959858081792), y0 := (0), i0 := 1200, i1 := 1200, fd := ((6667411526809946110448873766),(4745424063456862668440928256),(4831415840801588445184),(0),(886973340089086509056),(4340146991509916)), boxes := [
    (((959790972928),(959925190656),(0),(0)),((639860648618),(639950127104),(-7296604579),(0)))
] }
theorem Line12m3_far : farOK pts Line12m3 := by decide +kernel
theorem Line12m3_ok : axisOK pts Line12m3 = true := by decide +kernel
def Line12m4 : Macro := { x0 := (959992299520), y0 := (0), i0 := 1200, i1 := 1200, fd := ((6685949722763662824598252514),(4744867299415278511459860480),(4831992301553891868672),(0),(886973340089086509056),(4339097655348903)), boxes := [
    (((959925190656),(960059408384),(0),(0)),((639950127104),(640039605590),(-7296639385),(0)))
] }
theorem Line12m4_far : farOK pts Line12m4 := by decide +kernel
theorem Line12m4_ok : axisOK pts Line12m4 = true := by decide +kernel
def Line12m5 : Macro := { x0 := (960126517248), y0 := (0), i0 := 1200, i1 := 1200, fd := ((6704480096018522780936874114),(4744310721639864851046858752),(4832568762306195292160),(0),(886973340089086509056),(4338048757233591)), boxes := [
    (((960059408384),(960193626112),(0),(0)),((640039605589),(640129084075),(-7296675159),(0)))
] }
theorem Line12m5_far : farOK pts Line12m5 := by decide +kernel
theorem Line12m5_ok : axisOK pts Line12m5 = true := by decide +kernel
def Line12m6 : Macro := { x0 := (960260734976), y0 := (0), i0 := 1200, i1 := 1200, fd := ((6723006565088390010446127972),(4743754102957800143613919232),(4833145223058498715648),(0),(886973340089086509056),(4337000075241238)), boxes := [
    (((960193626112),(960327843840),(0),(0)),((640129084074),(640218562560),(-7296712523),(0)))
] }
theorem Line12m6_far : farOK pts Line12m6 := by decide +kernel
theorem Line12m6_ok : axisOK pts Line12m6 = true := by decide +kernel
def Line12m7 : Macro := { x0 := (960394952704), y0 := (0), i0 := 1200, i1 := 1200, fd := ((6741537527616633563169250503),(4743197686598939306562879488),(4833721683810802139136),(0),(886973340089086509056),(4335951855920332)), boxes := [
    (((960327843840),(960462061568),(0),(0)),((640218562560),(640308041046),(-7296747322),(0)))
] }
theorem Line12m7_far : farOK pts Line12m7 := by decide +kernel
theorem Line12m7_ok : axisOK pts Line12m7 = true := by decide +kernel
def Line12Data : List Macro := [Line12m0,Line12m1,Line12m2,Line12m3,Line12m4,Line12m5,Line12m6,Line12m7]
theorem Line12_farAll : ∀ m ∈ Line12Data, farOK pts m := by
  intro m hm
  simp only [Line12Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line12m0_far,Line12m1_far,Line12m2_far,Line12m3_far,Line12m4_far,Line12m5_far,Line12m6_far,Line12m7_far]
theorem Line12_okAll : ∀ m ∈ Line12Data, axisOK pts m = true := by
  intro m hm
  simp only [Line12Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line12m0_ok,Line12m1_ok,Line12m2_ok,Line12m3_ok,Line12m4_ok,Line12m5_ok,Line12m6_ok,Line12m7_ok]
end CatalanCore.Cert.SigmaQuarter
