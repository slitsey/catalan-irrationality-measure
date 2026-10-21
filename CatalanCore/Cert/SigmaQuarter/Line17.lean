module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line17m0 : Macro := { x0 := (963448406016), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7162484250286552317685757703),(4730574372450863189078900736),(4846836165925705023488),(0),(886973340089086509056),(4312207319831788)), boxes := [
    (((963414851584),(963481960448),(0),(0)),((642276567722),(642321306966),(-7296752626),(0)))
] }
theorem Line17m0_far : farOK pts Line17m0 := by decide +kernel
theorem Line17m0_ok : axisOK pts Line17m0 = true := by decide +kernel
def Line17m1 : Macro := { x0 := (963515514880), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7171725812066090190250405935),(4730297805742422304001687552),(4847124396301856735232),(0),(886973340089086509056),(4311687764818559)), boxes := [
    (((963481960448),(963549069312),(0),(0)),((642321306965),(642366046208),(-7296764628),(0)))
] }
theorem Line17m1_far : farOK pts Line17m1 := by decide +kernel
theorem Line17m1_ok : axisOK pts Line17m1 = true := by decide +kernel
def Line17m2 : Macro := { x0 := (963582623744), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7180965661493328768931997283),(4730021125219061253370675200),(4847412626678008446976),(0),(886973340089086509056),(4311168171376594)), boxes := [
    (((963549069312),(963616178176),(0),(0)),((642366046208),(642410785451),(-7296773294),(0)))
] }
theorem Line17m2_far : farOK pts Line17m2 := by decide +kernel
theorem Line17m2_ok : axisOK pts Line17m2 = true := by decide +kernel
def Line17m3 : Macro := { x0 := (963649732608), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7190209755183739182091073611),(4729744574387810675245187072),(4847700857054160158720),(0),(886973340089086509056),(4310648756075430)), boxes := [
    (((963616178176),(963683287040),(0),(0)),((642410785450),(642455524694),(-7296784942),(0)))
] }
theorem Line17m3_far : farOK pts Line17m3 := by decide +kernel
theorem Line17m3_ok : axisOK pts Line17m3 = true := by decide +kernel
def Line17m4 : Macro := { x0 := (963716841472), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7199446762670658374997320357),(4729467897944371345757372416),(4847989087430311870464),(0),(886973340089086509056),(4310129309461674)), boxes := [
    (((963683287040),(963750395904),(0),(0)),((642455524693),(642500263936),(-7296795957),(0)))
] }
theorem Line17m4_far : farOK pts Line17m4 := by decide +kernel
theorem Line17m4_ok : axisOK pts Line17m4 = true := by decide +kernel
def Line17m5 : Macro := { x0 := (963783950336), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7208680859925222447034653764),(4729191439643936879301165056),(4848277317806463582208),(0),(886973340089086509056),(4309610108697388)), boxes := [
    (((963750395904),(963817504768),(0),(0)),((642500263936),(642545003179),(-7296807197),(0)))
] }
theorem Line17m5_far : farOK pts Line17m5 := by decide +kernel
theorem Line17m5_ok : axisOK pts Line17m5 = true := by decide +kernel
def Line17m6 : Macro := { x0 := (963851059200), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7217919945070349416252566561),(4728914994647292349047963648),(4848565548182615293952),(0),(886973340089086509056),(4309090984869964)), boxes := [
    (((963817504768),(963884613632),(0),(0)),((642545003178),(642589742422),(-7296818217),(0)))
] }
theorem Line17m6_far : farOK pts Line17m6 := by decide +kernel
theorem Line17m6_ok : axisOK pts Line17m6 = true := by decide +kernel
def Line17m7 : Macro := { x0 := (963918168064), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7227155137584276495585944950),(4728638435284405893579407360),(4848853778558767005696),(0),(886973340089086509056),(4308571835556562)), boxes := [
    (((963884613632),(963951722496),(0),(0)),((642589742421),(642634481664),(-7296829423),(0)))
] }
theorem Line17m7_far : farOK pts Line17m7 := by decide +kernel
theorem Line17m7_ok : axisOK pts Line17m7 = true := by decide +kernel
def Line17Data : List Macro := [Line17m0,Line17m1,Line17m2,Line17m3,Line17m4,Line17m5,Line17m6,Line17m7]
theorem Line17_farAll : ∀ m ∈ Line17Data, farOK pts m := by
  intro m hm
  simp only [Line17Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line17m0_far,Line17m1_far,Line17m2_far,Line17m3_far,Line17m4_far,Line17m5_far,Line17m6_far,Line17m7_far]
theorem Line17_okAll : ∀ m ∈ Line17Data, axisOK pts m = true := by
  intro m hm
  simp only [Line17Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line17m0_ok,Line17m1_ok,Line17m2_ok,Line17m3_ok,Line17m4_ok,Line17m5_ok,Line17m6_ok,Line17m7_ok]
end CatalanCore.Cert.SigmaQuarter
