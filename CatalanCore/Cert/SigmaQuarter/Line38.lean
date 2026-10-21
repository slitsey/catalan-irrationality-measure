module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line38m0 : Macro := { x0 := (970511613952), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8131967635009295624663902668),(4701630795329901330313248768),(4877172413015672684544),(0),(886973340089086509056),(4258026892387023)), boxes := [
    (((970494836736),(970528391168),(0),(0)),((646996557824),(647018927446),(-7297038695),(0)))
] }
theorem Line38m0_far : farOK pts Line38m0 := by decide +kernel
theorem Line38m0_ok : axisOK pts Line38m0 = true := by decide +kernel
def Line38m1 : Macro := { x0 := (970545168384), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8136553413952374067668652116),(4701494190472880974493712384),(4877316528203748540416),(0),(886973340089086509056),(4257771992534900)), boxes := [
    (((970528391168),(970561945600),(0),(0)),((647018927445),(647041297067),(-7297038339),(0)))
] }
theorem Line38m1_far : farOK pts Line38m1 := by decide +kernel
theorem Line38m1_ok : axisOK pts Line38m1 = true := by decide +kernel
def Line38m2 : Macro := { x0 := (970578722816), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8141149803044854045699270120),(4701357487470184102903808000),(4877460643391824396288),(0),(886973340089086509056),(4257517023987742)), boxes := [
    (((970561945600),(970595500032),(0),(0)),((647041297066),(647063666688),(-7297038367),(0)))
] }
theorem Line38m2_far : farOK pts Line38m2 := by decide +kernel
theorem Line38m2_ok : axisOK pts Line38m2 = true := by decide +kernel
def Line38m3 : Macro := { x0 := (970612277248), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8145745674558879282749192395),(4701220894376549574501269504),(4877604758579900252160),(0),(886973340089086509056),(4257262178151307)), boxes := [
    (((970595500032),(970629054464),(0),(0)),((647063666688),(647086036310),(-7297038402),(0)))
] }
theorem Line38m3_far : farOK pts Line38m3 := by decide +kernel
theorem Line38m3_ok : axisOK pts Line38m3 = true := by decide +kernel
def Line38m4 : Macro := { x0 := (970645831680), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8150340882218428062397718123),(4701084189850725648237068288),(4877748873767976108032),(0),(886973340089086509056),(4257007237154517)), boxes := [
    (((970629054464),(970662608896),(0),(0)),((647086036309),(647108405931),(-7297041390),(0)))
] }
theorem Line38m4_far : farOK pts Line38m4 := by decide +kernel
theorem Line38m4_ok : axisOK pts Line38m4 = true := by decide +kernel
def Line38m5 : Macro := { x0 := (970679386112), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8154919974609332559050559221),(4700947639068018870260269056),(4877892988956051963904),(0),(886973340089086509056),(4256752460961061)), boxes := [
    (((970662608896),(970696163328),(0),(0)),((647108405930),(647130775552),(-7297040287),(0)))
] }
theorem Line38m5_far : farOK pts Line38m5 := by decide +kernel
theorem Line38m5_ok : axisOK pts Line38m5 = true := by decide +kernel
def Line38m6 : Macro := { x0 := (970712940544), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8159508398984156254144929634),(4700811066830988710177013760),(4878037104144127819776),(0),(886973340089086509056),(4256497667959254)), boxes := [
    (((970696163328),(970729717760),(0),(0)),((647130775552),(647153145174),(-7297039835),(0)))
] }
theorem Line38m6_far : farOK pts Line38m6 := by decide +kernel
theorem Line38m6_ok : axisOK pts Line38m6 = true := by decide +kernel
def Line38m7 : Macro := { x0 := (970746494976), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8164103646160887847933081243),(4700674492753481445680021504),(4878181219332203675648),(0),(886973340089086509056),(4256242898752841)), boxes := [
    (((970729717760),(970763272192),(0),(0)),((647153145173),(647175514795),(-7297039639),(0)))
] }
theorem Line38m7_far : farOK pts Line38m7 := by decide +kernel
theorem Line38m7_ok : axisOK pts Line38m7 = true := by decide +kernel
def Line38Data : List Macro := [Line38m0,Line38m1,Line38m2,Line38m3,Line38m4,Line38m5,Line38m6,Line38m7]
theorem Line38_farAll : ∀ m ∈ Line38Data, farOK pts m := by
  intro m hm
  simp only [Line38Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line38m0_far,Line38m1_far,Line38m2_far,Line38m3_far,Line38m4_far,Line38m5_far,Line38m6_far,Line38m7_far]
theorem Line38_okAll : ∀ m ∈ Line38Data, axisOK pts m = true := by
  intro m hm
  simp only [Line38Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line38m0_ok,Line38m1_ok,Line38m2_ok,Line38m3_ok,Line38m4_ok,Line38m5_ok,Line38m6_ok,Line38m7_ok]
end CatalanCore.Cert.SigmaQuarter
