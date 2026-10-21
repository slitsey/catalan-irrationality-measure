module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line42m0 : Macro := { x0 := (971585355776), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8278821070804571360631823862),(4697261981353201854428676096),(4881784099034100072448),(0),(886973340089086509056),(4249880404247866)), boxes := [
    (((971568578560),(971602132992),(0),(0)),((647712385706),(647734755328),(-7297020964),(0)))
] }
theorem Line42m0_far : farOK pts Line42m0 := by decide +kernel
theorem Line42m0_ok : axisOK pts Line42m0 = true := by decide +kernel
def Line42m1 : Macro := { x0 := (971618910208), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8283411684891974922686107103),(4697125438254507179090575360),(4881928214222175928320),(0),(886973340089086509056),(4249626081673156)), boxes := [
    (((971602132992),(971635687424),(0),(0)),((647734755328),(647757124950),(-7297020005),(0)))
] }
theorem Line42m1_far : farOK pts Line42m1 := by decide +kernel
theorem Line42m1_ok : axisOK pts Line42m1 = true := by decide +kernel
def Line42m2 : Macro := { x0 := (971652464640), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8287997455428897633028802929),(4696989182620383405488799744),(4882072329410251784192),(0),(886973340089086509056),(4249372018210657)), boxes := [
    (((971635687424),(971669241856),(0),(0)),((647757124949),(647779494571),(-7297018588),(0)))
] }
theorem Line42m2_far : farOK pts Line42m2 := by decide +kernel
theorem Line42m2_ok : axisOK pts Line42m2 = true := by decide +kernel
def Line42m3 : Macro := { x0 := (971686019072), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8292580161285250835023136011),(4696852755203861601084178432),(4882216444598327640064),(0),(886973340089086509056),(4249117821996754)), boxes := [
    (((971669241856),(971702796288),(0),(0)),((647779494570),(647801864192),(-7297017264),(0)))
] }
theorem Line42m3_far : farOK pts Line42m3 := by decide +kernel
theorem Line42m3_ok : axisOK pts Line42m3 = true := by decide +kernel
def Line42m4 : Macro := { x0 := (971719573504), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8297169201081816236120953311),(4696716260623006678965485568),(4882360559786403495936),(0),(886973340089086509056),(4248863575785698)), boxes := [
    (((971702796288),(971736350720),(0),(0)),((647801864192),(647824233814),(-7297016179),(0)))
] }
theorem Line42m4_far : farOK pts Line42m4 := by decide +kernel
theorem Line42m4_ok : axisOK pts Line42m4 = true := by decide +kernel
def Line42m5 : Macro := { x0 := (971753127936), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8301757038779766315098199066),(4696580017664641963356061696),(4882504674974479351808),(0),(886973340089086509056),(4248609575300652)), boxes := [
    (((971736350720),(971769905152),(0),(0)),((647824233813),(647846603435),(-7297015079),(0)))
] }
theorem Line42m5_far : farOK pts Line42m5 := by decide +kernel
theorem Line42m5_ok : axisOK pts Line42m5 = true := by decide +kernel
def Line42m6 : Macro := { x0 := (971786682368), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8306344692022921815733865194),(4696443649853855523772891136),(4882648790162555207680),(0),(886973340089086509056),(4248355484054183)), boxes := [
    (((971769905152),(971803459584),(0),(0)),((647846603434),(647868973056),(-7297013997),(0)))
] }
theorem Line42m6_far : farOK pts Line42m6 := by decide +kernel
theorem Line42m6_ok : axisOK pts Line42m6 = true := by decide +kernel
def Line42m7 : Macro := { x0 := (971820236800), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8310923139812116490660187574),(4696307331911456178980585472),(4882792905350631063552),(0),(886973340089086509056),(4248101443734418)), boxes := [
    (((971803459584),(971837014016),(0),(0)),((647868973056),(647891342678),(-7297012204),(0)))
] }
theorem Line42m7_far : farOK pts Line42m7 := by decide +kernel
theorem Line42m7_ok : axisOK pts Line42m7 = true := by decide +kernel
def Line42Data : List Macro := [Line42m0,Line42m1,Line42m2,Line42m3,Line42m4,Line42m5,Line42m6,Line42m7]
theorem Line42_farAll : ∀ m ∈ Line42Data, farOK pts m := by
  intro m hm
  simp only [Line42Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line42m0_far,Line42m1_far,Line42m2_far,Line42m3_far,Line42m4_far,Line42m5_far,Line42m6_far,Line42m7_far]
theorem Line42_okAll : ∀ m ∈ Line42Data, axisOK pts m = true := by
  intro m hm
  simp only [Line42Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line42m0_ok,Line42m1_ok,Line42m2_ok,Line42m3_ok,Line42m4_ok,Line42m5_ok,Line42m6_ok,Line42m7_ok]
end CatalanCore.Cert.SigmaQuarter
