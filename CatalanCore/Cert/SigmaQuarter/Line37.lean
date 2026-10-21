module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line37m0 : Macro := { x0 := (970243178496), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8095228673527899628286200591),(4702724229399235825819516928),(4876019491511065837568),(0),(886973340089086509056),(4260067149237154)), boxes := [
    (((970226401280),(970259955712),(0),(0)),((646817600853),(646839970475),(-7297041655),(0)))
] }
theorem Line37m0_far : farOK pts Line37m0 := by decide +kernel
theorem Line37m0_ok : axisOK pts Line37m0 = true := by decide +kernel
def Line37m1 : Macro := { x0 := (970276732928), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8099822631378696758636766665),(4702587621344978431751553024),(4876163606699141693440),(0),(886973340089086509056),(4259812118083495)), boxes := [
    (((970259955712),(970293510144),(0),(0)),((646839970474),(646862340096),(-7297041856),(0)))
] }
theorem Line37m1_far : farOK pts Line37m1 := by decide +kernel
theorem Line37m1_ok : axisOK pts Line37m1 = true := by decide +kernel
def Line37m2 : Macro := { x0 := (970310287360), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8104417341293793149691720206),(4702450795941808866085961728),(4876307721887217549312),(0),(886973340089086509056),(4259556923045815)), boxes := [
    (((970293510144),(970327064576),(0),(0)),((646862340096),(646884709718),(-7297042108),(0)))
] }
theorem Line37m2_far : farOK pts Line37m2 := by decide +kernel
theorem Line37m2_ok : axisOK pts Line37m2 = true := by decide +kernel
def Line37m3 : Macro := { x0 := (970343841792), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8109011735122679097472577772),(4702314219204982824017592320),(4876451837075293405184),(0),(886973340089086509056),(4259301950876120)), boxes := [
    (((970327064576),(970360619008),(0),(0)),((646884709717),(646907079339),(-7297042373),(0)))
] }
theorem Line37m3_far : farOK pts Line37m3 := by decide +kernel
theorem Line37m3_ok : axisOK pts Line37m3 = true := by decide +kernel
def Line37m4 : Macro := { x0 := (970377396224), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8113600413383916310155748049),(4702177470020941410515812352),(4876595952263369261056),(0),(886973340089086509056),(4259046853765418)), boxes := [
    (((970360619008),(970394173440),(0),(0)),((646907079338),(646929448960),(-7297039319),(0)))
] }
theorem Line37m4_far : farOK pts Line37m4 := by decide +kernel
theorem Line37m4_ok : axisOK pts Line37m4 = true := by decide +kernel
def Line37m5 : Macro := { x0 := (970410950656), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8118194021236331389249078339),(4702040851870646638583676928),(4876740067451445116928),(0),(886973340089086509056),(4258791885237468)), boxes := [
    (((970394173440),(970427727872),(0),(0)),((646929448960),(646951818582),(-7297039274),(0)))
] }
theorem Line37m5_far : farOK pts Line37m5 := by decide +kernel
theorem Line37m5_ok : axisOK pts Line37m5 = true := by decide +kernel
def Line37m6 : Macro := { x0 := (970444505088), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8122782917441501862493100738),(4701904009878298637491240960),(4876884182639520972800),(0),(886973340089086509056),(4258536722558351)), boxes := [
    (((970427727872),(970461282304),(0),(0)),((646951818581),(646974188203),(-7297039094),(0)))
] }
theorem Line37m6_far : farOK pts Line37m6 := by decide +kernel
theorem Line37m6_ok : axisOK pts Line37m6 = true := by decide +kernel
def Line37m7 : Macro := { x0 := (970478059520), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8127375209983477737571772786),(4701767370700707437306183680),(4877028297827596828672),(0),(886973340089086509056),(4258281776555914)), boxes := [
    (((970461282304),(970494836736),(0),(0)),((646974188202),(646996557824),(-7297039053),(0)))
] }
theorem Line37m7_far : farOK pts Line37m7 := by decide +kernel
theorem Line37m7_ok : axisOK pts Line37m7 = true := by decide +kernel
def Line37Data : List Macro := [Line37m0,Line37m1,Line37m2,Line37m3,Line37m4,Line37m5,Line37m6,Line37m7]
theorem Line37_farAll : ∀ m ∈ Line37Data, farOK pts m := by
  intro m hm
  simp only [Line37Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line37m0_far,Line37m1_far,Line37m2_far,Line37m3_far,Line37m4_far,Line37m5_far,Line37m6_far,Line37m7_far]
theorem Line37_okAll : ∀ m ∈ Line37Data, axisOK pts m = true := by
  intro m hm
  simp only [Line37Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line37m0_ok,Line37m1_ok,Line37m2_ok,Line37m3_ok,Line37m4_ok,Line37m5_ok,Line37m6_ok,Line37m7_ok]
end CatalanCore.Cert.SigmaQuarter
