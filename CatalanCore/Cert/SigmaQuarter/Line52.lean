module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line52m0 : Macro := { x0 := (974269710336), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8645373492586276387181398078),(4686374930664529761854095360),(4893313314080168542208),(0),(886973340089086509056),(4229616169941786)), boxes := [
    (((974252933120),(974286487552),(0),(0)),((649501955413),(649524325035),(-7296844583),(0)))
] }
theorem Line52m0_far : farOK pts Line52m0 := by decide +kernel
theorem Line52m0_ok : axisOK pts Line52m0 = true := by decide +kernel
def Line52m1 : Macro := { x0 := (974303264768), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8649953732088874199613621106),(4686239086273702528552337408),(4893457429268244398080),(0),(886973340089086509056),(4229363713884898)), boxes := [
    (((974286487552),(974320041984),(0),(0)),((649524325034),(649546694656),(-7296841055),(0)))
] }
theorem Line52m1_far : farOK pts Line52m1 := by decide +kernel
theorem Line52m1_ok : axisOK pts Line52m1 = true := by decide +kernel
def Line52m2 : Macro := { x0 := (974336819200), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8654525055135036817991225939),(4686103509896337589105328128),(4893601544456320253952),(0),(886973340089086509056),(4229111526452530)), boxes := [
    (((974320041984),(974353596416),(0),(0)),((649546694656),(649569064278),(-7296837187),(0)))
] }
theorem Line52m2_far : farOK pts Line52m2 := by decide +kernel
theorem Line52m2_ok : axisOK pts Line52m2 = true := by decide +kernel
def Line52m3 : Macro := { x0 := (974370373632), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8659103715724586465030094825),(4685967682318809431451762688),(4893745659644396109824),(0),(886973340089086509056),(4228859115274655)), boxes := [
    (((974353596416),(974387150848),(0),(0)),((649569064277),(649591433899),(-7296833593),(0)))
] }
theorem Line52m3_far : farOK pts Line52m3 := by decide +kernel
theorem Line52m3_ok : axisOK pts Line52m3 = true := by decide +kernel
def Line52m4 : Macro := { x0 := (974403928064), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8663683399979602784411617614),(4685831920946280754035949568),(4893889774832471965696),(0),(886973340089086509056),(4228606790144955)), boxes := [
    (((974387150848),(974420705280),(0),(0)),((649591433898),(649613803520),(-7296830059),(0)))
] }
theorem Line52m4_far : farOK pts Line52m4 := by decide +kernel
theorem Line52m4_ok : axisOK pts Line52m4 = true := by decide +kernel
def Line52m5 : Macro := { x0 := (974437482496), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8668253411250595019347825427),(4685696146242231308726173696),(4894033890020547821568),(0),(886973340089086509056),(4228354470008675)), boxes := [
    (((974420705280),(974454259712),(0),(0)),((649613803520),(649636173142),(-7296825819),(0)))
] }
theorem Line52m5_far : farOK pts Line52m5 := by decide +kernel
theorem Line52m5_ok : axisOK pts Line52m5 = true := by decide +kernel
def Line52m6 : Macro := { x0 := (974471036928), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8672828069024536540506774078),(4685560430884966759249149952),(4894178005208623677440),(0),(886973340089086509056),(4228102205295230)), boxes := [
    (((974454259712),(974487814144),(0),(0)),((649636173141),(649658542763),(-7296822010),(0)))
] }
theorem Line52m6_far : farOK pts Line52m6 := by decide +kernel
theorem Line52m6_ok : axisOK pts Line52m6 = true := by decide +kernel
def Line52m7 : Macro := { x0 := (974521368576), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8679691706484860418754034103),(4685356758928781546034692096),(4894394177990737461248),(0),(886973340089086509056),(4227723773995599)), boxes := [
    (((974487814144),(974554923008),(0),(0)),((649658542762),(649703282006),(-7297146938),(0)))
] }
theorem Line52m7_far : farOK pts Line52m7 := by decide +kernel
theorem Line52m7_ok : axisOK pts Line52m7 = true := by decide +kernel
def Line52Data : List Macro := [Line52m0,Line52m1,Line52m2,Line52m3,Line52m4,Line52m5,Line52m6,Line52m7]
theorem Line52_farAll : ∀ m ∈ Line52Data, farOK pts m := by
  intro m hm
  simp only [Line52Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line52m0_far,Line52m1_far,Line52m2_far,Line52m3_far,Line52m4_far,Line52m5_far,Line52m6_far,Line52m7_far]
theorem Line52_okAll : ∀ m ∈ Line52Data, axisOK pts m = true := by
  intro m hm
  simp only [Line52Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line52m0_ok,Line52m1_ok,Line52m2_ok,Line52m3_ok,Line52m4_ok,Line52m5_ok,Line52m6_ok,Line52m7_ok]
end CatalanCore.Cert.SigmaQuarter
