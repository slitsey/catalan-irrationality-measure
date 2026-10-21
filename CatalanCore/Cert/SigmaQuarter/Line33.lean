module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line33m0 : Macro := { x0 := (969169436672), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7948189927801866355300840320),(4707103581749764869645598720),(4871407805492638449664),(0),(886973340089086509056),(4268243387400083)), boxes := [
    (((969152659456),(969186213888),(0),(0)),((646101772970),(646124142592),(-7297021166),(0)))
] }
theorem Line33m0_far : farOK pts Line33m0 := by decide +kernel
theorem Line33m0_ok : axisOK pts Line33m0 = true := by decide +kernel
def Line33m1 : Macro := { x0 := (969202991104), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7952790491128316947759133460),(4706966409365553175825219584),(4871551920680714305536),(0),(886973340089086509056),(4267987351094530)), boxes := [
    (((969186213888),(969219768320),(0),(0)),((646124142592),(646146512214),(-7297022484),(0)))
] }
theorem Line33m1_far : farOK pts Line33m1 := by decide +kernel
theorem Line33m1_ok : axisOK pts Line33m1 = true := by decide +kernel
def Line33m2 : Macro := { x0 := (969236545536), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7957392076989823583011199100),(4706829693578134647545593856),(4871696035868790161408),(0),(886973340089086509056),(4267731743107615)), boxes := [
    (((969219768320),(969253322752),(0),(0)),((646146512213),(646168881835),(-7297023500),(0)))
] }
theorem Line33m2_far : farOK pts Line33m2 := by decide +kernel
theorem Line33m2_ok : axisOK pts Line33m2 = true := by decide +kernel
def Line33m3 : Macro := { x0 := (969270099968), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7961982313160739109869755741),(4706692540873475066886029312),(4871840151056866017280),(0),(886973340089086509056),(4267475748393161)), boxes := [
    (((969253322752),(969286877184),(0),(0)),((646168881834),(646191251456),(-7297024375),(0)))
] }
theorem Line33m3_far : farOK pts Line33m3 := by decide +kernel
theorem Line33m3_ok : axisOK pts Line33m3 = true := by decide +kernel
def Line33m4 : Macro := { x0 := (969303654400), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7966583457367084272815001387),(4706555546094404178986532864),(4871984266244941873152),(0),(886973340089086509056),(4267219912150457)), boxes := [
    (((969286877184),(969320431616),(0),(0)),((646191251456),(646213621078),(-7297025645),(0)))
] }
theorem Line33m4_far : farOK pts Line33m4 := by decide +kernel
theorem Line33m4_ok : axisOK pts Line33m4 = true := by decide +kernel
def Line33m5 : Macro := { x0 := (969337208832), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7971180269910787539196210778),(4706418732061137097610821632),(4872128381433017729024),(0),(886973340089086509056),(4266964256301893)), boxes := [
    (((969320431616),(969353986048),(0),(0)),((646213621077),(646235990699),(-7297026793),(0)))
] }
theorem Line33m5_far : farOK pts Line33m5 := by decide +kernel
theorem Line33m5_ok : axisOK pts Line33m5 = true := by decide +kernel
def Line33m6 : Macro := { x0 := (969370763264), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7975776782368032373739792143),(4706281888792283957027536896),(4872272496621093584896),(0),(886973340089086509056),(4266708590495062)), boxes := [
    (((969353986048),(969387540480),(0),(0)),((646235990698),(646258360320),(-7297027624),(0)))
] }
theorem Line33m6_far : farOK pts Line33m6 := by decide +kernel
theorem Line33m6_ok : axisOK pts Line33m6 = true := by decide +kernel
def Line33m7 : Macro := { x0 := (969404317696), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7980364374713308182994389886),(4706144754243467702438002688),(4872416611809169440768),(0),(886973340089086509056),(4266452684240354)), boxes := [
    (((969387540480),(969421094912),(0),(0)),((646258360320),(646280729942),(-7297025586),(0)))
] }
theorem Line33m7_far : farOK pts Line33m7 := by decide +kernel
theorem Line33m7_ok : axisOK pts Line33m7 = true := by decide +kernel
def Line33Data : List Macro := [Line33m0,Line33m1,Line33m2,Line33m3,Line33m4,Line33m5,Line33m6,Line33m7]
theorem Line33_farAll : ∀ m ∈ Line33Data, farOK pts m := by
  intro m hm
  simp only [Line33Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line33m0_far,Line33m1_far,Line33m2_far,Line33m3_far,Line33m4_far,Line33m5_far,Line33m6_far,Line33m7_far]
theorem Line33_okAll : ∀ m ∈ Line33Data, axisOK pts m = true := by
  intro m hm
  simp only [Line33Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line33m0_ok,Line33m1_ok,Line33m2_ok,Line33m3_ok,Line33m4_ok,Line33m5_ok,Line33m6_ok,Line33m7_ok]
end CatalanCore.Cert.SigmaQuarter
