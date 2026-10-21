module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line6m0 : Macro := { x0 := (946771853312), y0 := (0), i0 := 1200, i1 := 1200, fd := ((4849637547277158880617682557),(4800348314073671246285897728),(4775210917452004655104),(0),(886973340089086509056),(4444325853910819)), boxes := [
    (((946503417856),(947040288768),(0),(0)),((631002278570),(631360192512),(-7294901724),(0)))
] }
theorem Line6m0_far : farOK pts Line6m0 := by decide +kernel
theorem Line6m0_ok : axisOK pts Line6m0 = true := by decide +kernel
def Line6m1 : Macro := { x0 := (947308724224), y0 := (0), i0 := 1200, i1 := 1200, fd := ((4924629427905589223971681698),(4798069976011004762146340864),(4777516760461218349056),(0),(886973340089086509056),(4439978086386783)), boxes := [
    (((947040288768),(947577159680),(0),(0)),((631360192512),(631718106454),(-7295210451),(0)))
] }
theorem Line6m1_far : farOK pts Line6m1 := by decide +kernel
theorem Line6m1_ok : axisOK pts Line6m1 = true := by decide +kernel
def Line6m2 : Macro := { x0 := (947845595136), y0 := (0), i0 := 1200, i1 := 1200, fd := ((4999582060332299789162292494),(4795793961436761802091855872),(4779822603470432043008),(0),(886973340089086509056),(4435636866593830)), boxes := [
    (((947577159680),(948114030592),(0),(0)),((631718106453),(632076020395),(-7295523246),(0)))
] }
theorem Line6m2_far : farOK pts Line6m2 := by decide +kernel
theorem Line6m2_ok : axisOK pts Line6m2 = true := by decide +kernel
def Line6m3 : Macro := { x0 := (948382466048), y0 := (0), i0 := 1200, i1 := 1200, fd := ((5074480584884765220714787568),(4793519829785861212643524608),(4782128446479645736960),(0),(886973340089086509056),(4431301774817650)), boxes := [
    (((948114030592),(948650901504),(0),(0)),((632076020394),(632433934336),(-7295816821),(0)))
] }
theorem Line6m3_far : farOK pts Line6m3 := by decide +kernel
theorem Line6m3_ok : axisOK pts Line6m3 = true := by decide +kernel
def Line6m4 : Macro := { x0 := (948919336960), y0 := (0), i0 := 1200, i1 := 1200, fd := ((5149372708944204532170067278),(4791247953806665363960365056),(4784434289488859430912),(0),(886973340089086509056),(4426973160336447)), boxes := [
    (((948650901504),(949187772416),(0),(0)),((632433934336),(632791848278),(-7296112581),(0)))
] }
theorem Line6m4_far : farOK pts Line6m4 := by decide +kernel
theorem Line6m4_ok : axisOK pts Line6m4 = true := by decide +kernel
def Line6m5 : Macro := { x0 := (949456207872), y0 := (0), i0 := 1200, i1 := 1200, fd := ((5224226421921784288260807344),(4788978276087032236782518272),(4786740132498073124864),(0),(886973340089086509056),(4422650949854198)), boxes := [
    (((949187772416),(949724643328),(0),(0)),((632791848277),(633149762219),(-7296397650),(0)))
] }
theorem Line6m5_far : farOK pts Line6m5 := by decide +kernel
theorem Line6m5_ok : axisOK pts Line6m5 = true := by decide +kernel
def Line6m6 : Macro := { x0 := (949993078784), y0 := (0), i0 := 1200, i1 := 1200, fd := ((5299038646855467783970138238),(4786710712518136910117011456),(4789045975507286818816),(0),(886973340089086509056),(4418335053712050)), boxes := [
    (((949724643328),(950261514240),(0),(0)),((633149762218),(633507676160),(-7296675407),(0)))
] }
theorem Line6m6_far : farOK pts Line6m6 := by decide +kernel
theorem Line6m6_ok : axisOK pts Line6m6 = true := by decide +kernel
def Line6m7 : Macro := { x0 := (950529949696), y0 := (0), i0 := 1200, i1 := 1200, fd := ((5373794656249295696508391178),(4784445426682150026819731456),(4791351818516500512768),(0),(886973340089086509056),(4414025621236994)), boxes := [
    (((950261514240),(950798385152),(0),(0)),((633507676160),(633865590102),(-7296944586),(0)))
] }
theorem Line6m7_far : farOK pts Line6m7 := by decide +kernel
theorem Line6m7_ok : axisOK pts Line6m7 = true := by decide +kernel
def Line6Data : List Macro := [Line6m0,Line6m1,Line6m2,Line6m3,Line6m4,Line6m5,Line6m6,Line6m7]
theorem Line6_farAll : ∀ m ∈ Line6Data, farOK pts m := by
  intro m hm
  simp only [Line6Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line6m0_far,Line6m1_far,Line6m2_far,Line6m3_far,Line6m4_far,Line6m5_far,Line6m6_far,Line6m7_far]
theorem Line6_okAll : ∀ m ∈ Line6Data, axisOK pts m = true := by
  intro m hm
  simp only [Line6Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line6m0_ok,Line6m1_ok,Line6m2_ok,Line6m3_ok,Line6m4_ok,Line6m5_ok,Line6m6_ok,Line6m7_ok]
end CatalanCore.Cert.SigmaQuarter
