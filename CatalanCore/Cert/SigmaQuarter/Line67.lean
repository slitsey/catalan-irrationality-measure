module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line67m0 : Macro := { x0 := (987976695808), y0 := (0), i0 := 1200, i1 := 1200, fd := ((10503920842491932483323405493),(4631561972227019040273793024),(4952184368409155665920),(0),(886973340089086509056),(4128376269623571)), boxes := [
    (((987842478080),(988110913536),(0),(0)),((658561652053),(658740609024),(-7295234382),(0)))
] }
theorem Line67m0_far : farOK pts Line67m0 := by decide +kernel
theorem Line67m0_ok : axisOK pts Line67m0 = true := by decide +kernel
def Line67m1 : Macro := { x0 := (988245131264), y0 := (0), i0 := 1200, i1 := 1200, fd := ((10540101574908336874795727293),(4630501309567473547336613888),(4953337289913762512896),(0),(886973340089086509056),(4126430145318939)), boxes := [
    (((988110913536),(988379348992),(0),(0)),((658740609024),(658919565995),(-7295101756),(0)))
] }
theorem Line67m1_far : farOK pts Line67m1 := by decide +kernel
theorem Line67m1_ok : axisOK pts Line67m1 = true := by decide +kernel
def Line67m2 : Macro := { x0 := (988513566720), y0 := (0), i0 := 1200, i1 := 1200, fd := ((10576275371038317781473658751),(4629441026395029449084108800),(4954490211418369359872),(0),(886973340089086509056),(4124485314331468)), boxes := [
    (((988379348992),(988647784448),(0),(0)),((658919565994),(659098522966),(-7294970871),(0)))
] }
theorem Line67m2_far : farOK pts Line67m2 := by decide +kernel
theorem Line67m2_ok : axisOK pts Line67m2 = true := by decide +kernel
def Line67m3 : Macro := { x0 := (988782002176), y0 := (0), i0 := 1200, i1 := 1200, fd := ((10612440090551697036820581238),(4628381385194529317360041984),(4955643132922976206848),(0),(886973340089086509056),(4122541992196603)), boxes := [
    (((988647784448),(988916219904),(0),(0)),((659098522965),(659277479936),(-7294838329),(0)))
] }
theorem Line67m3_far : farOK pts Line67m3 := by decide +kernel
theorem Line67m3_ok : axisOK pts Line67m3 = true := by decide +kernel
def Line67m4 : Macro := { x0 := (989050437632), y0 := (0), i0 := 1200, i1 := 1200, fd := ((10648579913861941881655543378),(4627322242551987547688534016),(4956796054427583053824),(0),(886973340089086509056),(4120600062533968)), boxes := [
    (((988916219904),(989184655360),(0),(0)),((659277479936),(659456436907),(-7294708536),(0)))
] }
theorem Line67m4_far : farOK pts Line67m4 := by decide +kernel
theorem Line67m4_ok : axisOK pts Line67m4 = true := by decide +kernel
def Line67m5 : Macro := { x0 := (989318873088), y0 := (0), i0 := 1200, i1 := 1200, fd := ((10684730655316155961418837943),(4626263493540133681772691456),(4957948975932189900800),(0),(886973340089086509056),(4118659436306893)), boxes := [
    (((989184655360),(989453090816),(0),(0)),((659456436906),(659635393878),(-7294567497),(0)))
] }
theorem Line67m5_far : farOK pts Line67m5 := by decide +kernel
theorem Line67m5_ok : axisOK pts Line67m5 = true := by decide +kernel
def Line67m6 : Macro := { x0 := (989721526272), y0 := (0), i0 := 1200, i1 := 1200, fd := ((10738932068930395536781844516),(4624676434692334337065418752),(4959678358189100171264),(0),(886973340089086509056),(4115751216997311)), boxes := [
    (((989453090816),(989989961728),(0),(0)),((659635393877),(659993307819),(-7297026952),(0)))
] }
theorem Line67m6_far : farOK pts Line67m6 := by decide +kernel
theorem Line67m6_ok : axisOK pts Line67m6 = true := by decide +kernel
def Line67m7 : Macro := { x0 := (990258397184), y0 := (0), i0 := 1200, i1 := 1200, fd := ((10811194361175110675396277069),(4622562050126071234967306240),(4961984201198313865216),(0),(886973340089086509056),(4111878369734810)), boxes := [
    (((989989961728),(990526832640),(0),(0)),((659993307818),(660351221760),(-7296741835),(0)))
] }
theorem Line67m7_far : farOK pts Line67m7 := by decide +kernel
theorem Line67m7_ok : axisOK pts Line67m7 = true := by decide +kernel
def Line67Data : List Macro := [Line67m0,Line67m1,Line67m2,Line67m3,Line67m4,Line67m5,Line67m6,Line67m7]
theorem Line67_farAll : ∀ m ∈ Line67Data, farOK pts m := by
  intro m hm
  simp only [Line67Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line67m0_far,Line67m1_far,Line67m2_far,Line67m3_far,Line67m4_far,Line67m5_far,Line67m6_far,Line67m7_far]
theorem Line67_okAll : ∀ m ∈ Line67Data, axisOK pts m = true := by
  intro m hm
  simp only [Line67Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line67m0_ok,Line67m1_ok,Line67m2_ok,Line67m3_ok,Line67m4_ok,Line67m5_ok,Line67m6_ok,Line67m7_ok]
end CatalanCore.Cert.SigmaQuarter
