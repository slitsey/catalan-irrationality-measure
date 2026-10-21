module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line31m0 : Macro := { x0 := (968632565760), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7874636591636068925933828054),(4709296258708964759160487936),(4869101962483424755712),(0),(886973340089086509056),(4272340316974602)), boxes := [
    (((968615788544),(968649342976),(0),(0)),((645743859029),(645766228651),(-7297002511),(0)))
] }
theorem Line31m0_far : farOK pts Line31m0 := by decide +kernel
theorem Line31m0_ok : axisOK pts Line31m0 = true := by decide +kernel
def Line31m1 : Macro := { x0 := (968666120192), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7879236821667722680272821296),(4709158850315880506150092800),(4869246077671500611584),(0),(886973340089086509056),(4272083806352250)), boxes := [
    (((968649342976),(968682897408),(0),(0)),((645766228650),(645788598272),(-7297003655),(0)))
] }
theorem Line31m1_far : farOK pts Line31m1 := by decide +kernel
theorem Line31m1_ok : axisOK pts Line31m1 = true := by decide +kernel
def Line31m2 : Macro := { x0 := (968699674624), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7883826587350697083959118129),(4709021859268943075103408128),(4869390192859576467456),(0),(886973340089086509056),(4271827686123958)), boxes := [
    (((968682897408),(968716451840),(0),(0)),((645788598272),(645810967894),(-7297004663),(0)))
] }
theorem Line31m2_far : farOK pts Line31m2 := by decide +kernel
theorem Line31m2_ok : axisOK pts Line31m2 = true := by decide +kernel
def Line31m3 : Macro := { x0 := (968733229056), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7888417075773218211080421383),(4708884723993219153622990848),(4869534308047652323328),(0),(886973340089086509056),(4271571463410564)), boxes := [
    (((968716451840),(968750006272),(0),(0)),((645810967893),(645833337515),(-7297005721),(0)))
] }
theorem Line31m3_far : farOK pts Line31m3 := by decide +kernel
theorem Line31m3_ok : axisOK pts Line31m3 = true := by decide +kernel
def Line31m4 : Macro := { x0 := (968766783488), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7893021330164692779630796003),(4708747716535163841131184128),(4869678423235728179200),(0),(886973340089086509056),(4271315365474211)), boxes := [
    (((968750006272),(968783560704),(0),(0)),((645833337514),(645855707136),(-7297007269),(0)))
] }
theorem Line31m4_far : farOK pts Line31m4 := by decide +kernel
theorem Line31m4_ok : axisOK pts Line31m4 = true := by decide +kernel
def Line31m5 : Macro := { x0 := (968800337920), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7897614971295816840714975661),(4708610655667570434117730304),(4869822538423804035072),(0),(886973340089086509056),(4271059243083292)), boxes := [
    (((968783560704),(968817115136),(0),(0)),((645855707136),(645878076758),(-7297008175),(0)))
] }
theorem Line31m5_far : farOK pts Line31m5 := by decide +kernel
theorem Line31m5_ok : axisOK pts Line31m5 = true := by decide +kernel
def Line31m6 : Macro := { x0 := (968833892352), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7902203342421886855425184056),(4708473631070705643989499904),(4869966653611879890944),(0),(886973340089086509056),(4270803149354085)), boxes := [
    (((968817115136),(968850669568),(0),(0)),((645878076757),(645900446379),(-7297009093),(0)))
] }
theorem Line31m6_far : farOK pts Line31m6 := by decide +kernel
theorem Line31m6_ok : axisOK pts Line31m6 = true := by decide +kernel
def Line31m7 : Macro := { x0 := (968867446784), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7906794422757557239595456837),(4708336487505170486107045888),(4870110768799955746816),(0),(886973340089086509056),(4270546983195340)), boxes := [
    (((968850669568),(968884224000),(0),(0)),((645900446378),(645922816000),(-7297010127),(0)))
] }
theorem Line31m7_far : farOK pts Line31m7 := by decide +kernel
theorem Line31m7_ok : axisOK pts Line31m7 = true := by decide +kernel
def Line31Data : List Macro := [Line31m0,Line31m1,Line31m2,Line31m3,Line31m4,Line31m5,Line31m6,Line31m7]
theorem Line31_farAll : ∀ m ∈ Line31Data, farOK pts m := by
  intro m hm
  simp only [Line31Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line31m0_far,Line31m1_far,Line31m2_far,Line31m3_far,Line31m4_far,Line31m5_far,Line31m6_far,Line31m7_far]
theorem Line31_okAll : ∀ m ∈ Line31Data, axisOK pts m = true := by
  intro m hm
  simp only [Line31Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line31m0_ok,Line31m1_ok,Line31m2_ok,Line31m3_ok,Line31m4_ok,Line31m5_ok,Line31m6_ok,Line31m7_ok]
end CatalanCore.Cert.SigmaQuarter
