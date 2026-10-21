module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line4m0 : Macro := { x0 := (934692257792), y0 := (0), i0 := 1200, i1 := 1200, fd := ((3152936482262459573755105696),(4852189814449365032756969472),(4723329449744696541184),(0),(886973340089086509056),(4543871389275791)), boxes := [
    (((934155386880),(935229128704),(0),(0)),((622770257920),(623486085803),(-7291262823),(0)))
] }
theorem Line4m0_far : farOK pts Line4m0 := by decide +kernel
theorem Line4m0_ok : axisOK pts Line4m0 = true := by decide +kernel
def Line4m1 : Macro := { x0 := (935765999616), y0 := (0), i0 := 1200, i1 := 1200, fd := ((3304479391074751433978771555),(4847536356284977458970034176),(4727941135763123929088),(0),(886973340089086509056),(4534887581714963)), boxes := [
    (((935229128704),(936302870528),(0),(0)),((623486085802),(624201913686),(-7292190046),(0)))
] }
theorem Line4m1_far : farOK pts Line4m1 := by decide +kernel
theorem Line4m1_ok : axisOK pts Line4m1 = true := by decide +kernel
def Line4m2 : Macro := { x0 := (936839741440), y0 := (0), i0 := 1200, i1 := 1200, fd := ((3455910536919864193189343373),(4842891799366900745947774976),(4732552821781551316992),(0),(886973340089086509056),(4525930480740459)), boxes := [
    (((936302870528),(937376612352),(0),(0)),((624201913685),(624917741568),(-7293091695),(0)))
] }
theorem Line4m2_far : farOK pts Line4m2 := by decide +kernel
theorem Line4m2_ok : axisOK pts Line4m2 = true := by decide +kernel
def Line4m3 : Macro := { x0 := (937913483264), y0 := (0), i0 := 1200, i1 := 1200, fd := ((3607161003847481939609519489),(4838256067063436385636450304),(4737164507799978704896),(0),(886973340089086509056),(4516999951696652)), boxes := [
    (((937376612352),(938450354176),(0),(0)),((624917741568),(625633569451),(-7293960273),(0)))
] }
theorem Line4m3_far : farOK pts Line4m3 := by decide +kernel
theorem Line4m3_ok : axisOK pts Line4m3 = true := by decide +kernel
def Line4m4 : Macro := { x0 := (938987225088), y0 := (0), i0 := 1200, i1 := 1200, fd := ((3758304157783865684004381869),(4833629240949548887794843648),(4741776193818406092800),(0),(886973340089086509056),(4508095952410118)), boxes := [
    (((938450354176),(939524096000),(0),(0)),((625633569450),(626349397334),(-7294804774),(0)))
] }
theorem Line4m4_far : farOK pts Line4m4 := by decide +kernel
theorem Line4m4_ok : axisOK pts Line4m4 = true := by decide +kernel
def Line4m5 : Macro := { x0 := (940060966912), y0 := (0), i0 := 1200, i1 := 1200, fd := ((3909264222528987199068854720),(4829011398287940771195650048),(4746387879836833480704),(0),(886973340089086509056),(4499218506110795)), boxes := [
    (((939524096000),(940597837824),(0),(0)),((626349397333),(627065225216),(-7295624759),(0)))
] }
theorem Line4m5_far : farOK pts Line4m5 := by decide +kernel
theorem Line4m5_ok : axisOK pts Line4m5 = true := by decide +kernel
def Line4m6 : Macro := { x0 := (941134708736), y0 := (0), i0 := 1200, i1 := 1200, fd := ((4060123669150580660646165514),(4824402229545771649710817280),(4750999565855260868608),(0),(886973340089086509056),(4490367208049005)), boxes := [
    (((940597837824),(941671579648),(0),(0)),((627065225216),(627781053099),(-7296416825),(0)))
] }
theorem Line4m6_far : farOK pts Line4m6 := by decide +kernel
theorem Line4m6_ok : axisOK pts Line4m6 = true := by decide +kernel
def Line4m7 : Macro := { x0 := (941940015104), y0 := (0), i0 := 1200, i1 := 1200, fd := ((4173126047182923746842589158),(4820951256906956094925373440),(4754458330369081409536),(0),(886973340089086509056),(4483746058478346)), boxes := [
    (((941671579648),(942208450560),(0),(0)),((627781053098),(628138967040),(-7291772487),(0)))
] }
theorem Line4m7_far : farOK pts Line4m7 := by decide +kernel
theorem Line4m7_ok : axisOK pts Line4m7 = true := by decide +kernel
def Line4Data : List Macro := [Line4m0,Line4m1,Line4m2,Line4m3,Line4m4,Line4m5,Line4m6,Line4m7]
theorem Line4_farAll : ∀ m ∈ Line4Data, farOK pts m := by
  intro m hm
  simp only [Line4Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line4m0_far,Line4m1_far,Line4m2_far,Line4m3_far,Line4m4_far,Line4m5_far,Line4m6_far,Line4m7_far]
theorem Line4_okAll : ∀ m ∈ Line4Data, axisOK pts m = true := by
  intro m hm
  simp only [Line4Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line4m0_ok,Line4m1_ok,Line4m2_ok,Line4m3_ok,Line4m4_ok,Line4m5_ok,Line4m6_ok,Line4m7_ok]
end CatalanCore.Cert.SigmaQuarter
