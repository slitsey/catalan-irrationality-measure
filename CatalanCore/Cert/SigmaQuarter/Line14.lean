module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line14m0 : Macro := { x0 := (961602912256), y0 := (0), i0 := 1200, i1 := 1200, fd := ((6908203699199159776997068080),(4738195784848469400154537984),(4838909830581532950528),(0),(886973340089086509056),(4326534912328992)), boxes := [
    (((961535803392),(961670021120),(0),(0)),((641023868928),(641113347414),(-7297036036),(0)))
] }
theorem Line14m0_far : farOK pts Line14m0 := by decide +kernel
theorem Line14m0_ok : axisOK pts Line14m0 = true := by decide +kernel
def Line14m1 : Macro := { x0 := (961737129984), y0 := (0), i0 := 1200, i1 := 1200, fd := ((6926715405184680113466644957),(4737640782765479232733249536),(4839486291333836374016),(0),(886973340089086509056),(4325490591266663)), boxes := [
    (((961670021120),(961804238848),(0),(0)),((641113347413),(641202825899),(-7297066048),(0)))
] }
theorem Line14m1_far : farOK pts Line14m1 := by decide +kernel
theorem Line14m1_ok : axisOK pts Line14m1 = true := by decide +kernel
def Line14m2 : Macro := { x0 := (961871347712), y0 := (0), i0 := 1200, i1 := 1200, fd := ((6945214015950949916905934028),(4737085825198004353204092928),(4840062752086139797504),(0),(886973340089086509056),(4324446575142182)), boxes := [
    (((961804238848),(961938456576),(0),(0)),((641202825898),(641292304384),(-7297093963),(0)))
] }
theorem Line14m2_far : farOK pts Line14m2 := by decide +kernel
theorem Line14m2_ok : axisOK pts Line14m2 = true := by decide +kernel
def Line14m3 : Macro := { x0 := (962005565440), y0 := (0), i0 := 1200, i1 := 1200, fd := ((6963725937278445778872178284),(4736530935821553709367099392),(4840639212838443220992),(0),(886973340089086509056),(4323402872991005)), boxes := [
    (((961938456576),(962072674304),(0),(0)),((641292304384),(641381782870),(-7297123726),(0)))
] }
theorem Line14m3_far : farOK pts Line14m3 := by decide +kernel
theorem Line14m3_ok : axisOK pts Line14m3 = true := by decide +kernel
def Line14m4 : Macro := { x0 := (962106228736), y0 := (0), i0 := 1200, i1 := 1200, fd := ((6977603273849132812603192861),(4736114672868567502822768640),(4841071558402670788608),(0),(886973340089086509056),(4322620188963581)), boxes := [
    (((962072674304),(962139783168),(0),(0)),((641381782869),(641426522112),(-7296490343),(0)))
] }
theorem Line14m4_far : farOK pts Line14m4 := by decide +kernel
theorem Line14m4_ok : axisOK pts Line14m4 = true := by decide +kernel
def Line14m5 : Macro := { x0 := (962173337600), y0 := (0), i0 := 1200, i1 := 1200, fd := ((6986859311637145199049252027),(4735837555704134321533943808),(4841359788778822500352),(0),(886973340089086509056),(4322098831695400)), boxes := [
    (((962139783168),(962206892032),(0),(0)),((641426522112),(641471261355),(-7296504588),(0)))
] }
theorem Line14m5_far : farOK pts Line14m5 := by decide +kernel
theorem Line14m5_ok : axisOK pts Line14m5 = true := by decide +kernel
def Line14m6 : Macro := { x0 := (962240446464), y0 := (0), i0 := 1200, i1 := 1200, fd := ((6996096788203600219905427821),(4735560179110260717633404928),(4841648019154974212096),(0),(886973340089086509056),(4321577308116469)), boxes := [
    (((962206892032),(962274000896),(0),(0)),((641471261354),(641516000598),(-7296517787),(0)))
] }
theorem Line14m6_far : farOK pts Line14m6 := by decide +kernel
theorem Line14m6_ok : axisOK pts Line14m6 = true := by decide +kernel
def Line14m7 : Macro := { x0 := (962307555328), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7005340983574304275799074273),(4735283178593525382048579584),(4841936249531125923840),(0),(886973340089086509056),(4321056188701602)), boxes := [
    (((962274000896),(962341109760),(0),(0)),((641516000597),(641560739840),(-7296531565),(0)))
] }
theorem Line14m7_far : farOK pts Line14m7 := by decide +kernel
theorem Line14m7_ok : axisOK pts Line14m7 = true := by decide +kernel
def Line14Data : List Macro := [Line14m0,Line14m1,Line14m2,Line14m3,Line14m4,Line14m5,Line14m6,Line14m7]
theorem Line14_farAll : ∀ m ∈ Line14Data, farOK pts m := by
  intro m hm
  simp only [Line14Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line14m0_far,Line14m1_far,Line14m2_far,Line14m3_far,Line14m4_far,Line14m5_far,Line14m6_far,Line14m7_far]
theorem Line14_okAll : ∀ m ∈ Line14Data, axisOK pts m = true := by
  intro m hm
  simp only [Line14Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line14m0_ok,Line14m1_ok,Line14m2_ok,Line14m3_ok,Line14m4_ok,Line14m5_ok,Line14m6_ok,Line14m7_ok]
end CatalanCore.Cert.SigmaQuarter
