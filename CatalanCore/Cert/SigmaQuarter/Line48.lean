module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line48m0 : Macro := { x0 := (973195968512), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8498839196435686326784430163),(4690723554623193429810413568),(4888701628061741154304),(0),(886973340089086509056),(4237704253469922)), boxes := [
    (((973179191296),(973212745728),(0),(0)),((648786127530),(648808497152),(-7296939281),(0)))
] }
theorem Line48m0_far : farOK pts Line48m0 := by decide +kernel
theorem Line48m0_ok : axisOK pts Line48m0 = true := by decide +kernel
def Line48m1 : Macro := { x0 := (973229522944), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8503421227063896328948373043),(4690587646364291682915385344),(4888845743249817010176),(0),(886973340089086509056),(4237451239980579)), boxes := [
    (((973212745728),(973246300160),(0),(0)),((648808497152),(648830866774),(-7296936891),(0)))
] }
theorem Line48m1_far : farOK pts Line48m1 := by decide +kernel
theorem Line48m1_ok : axisOK pts Line48m1 = true := by decide +kernel
def Line48m2 : Macro := { x0 := (973263077376), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8508005931181165977599976157),(4690451581486833116207775744),(4888989858437892866048),(0),(886973340089086509056),(4237198114916148)), boxes := [
    (((973246300160),(973279854592),(0),(0)),((648830866773),(648853236395),(-7296934224),(0)))
] }
theorem Line48m2_far : farOK pts Line48m2 := by decide +kernel
theorem Line48m2_ok : axisOK pts Line48m2 = true := by decide +kernel
def Line48m3 : Macro := { x0 := (973296631808), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8512586670565424482235259470),(4690315597058621158028279808),(4889133973625968721920),(0),(886973340089086509056),(4236945067910606)), boxes := [
    (((973279854592),(973313409024),(0),(0)),((648853236394),(648875606016),(-7296931689),(0)))
] }
theorem Line48m3_far : farOK pts Line48m3 := by decide +kernel
theorem Line48m3_ok : axisOK pts Line48m3 = true := by decide +kernel
def Line48m4 : Macro := { x0 := (973330186240), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8517168609539103840626489406),(4690179555502536359801913344),(4889278088814044577792),(0),(886973340089086509056),(4236691979514742)), boxes := [
    (((973313409024),(973346963456),(0),(0)),((648875606016),(648897975638),(-7296926351),(0)))
] }
theorem Line48m4_far : farOK pts Line48m4 := by decide +kernel
theorem Line48m4_ok : axisOK pts Line48m4 = true := by decide +kernel
def Line48m5 : Macro := { x0 := (973363740672), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8521752618978252204063376930),(4690043568202040215845273600),(4889422204002120433664),(0),(886973340089086509056),(4236438977929632)), boxes := [
    (((973346963456),(973380517888),(0),(0)),((648897975637),(648920345259),(-7296923787),(0)))
] }
theorem Line48m5_far : farOK pts Line48m5 := by decide +kernel
theorem Line48m5_ok : axisOK pts Line48m5 = true := by decide +kernel
def Line48m6 : Macro := { x0 := (973397295104), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8526331799210772396572350845),(4689907515347202204183494656),(4889566319190196289536),(0),(886973340089086509056),(4236185914457794)), boxes := [
    (((973380517888),(973414072320),(0),(0)),((648920345258),(648942714880),(-7296920745),(0)))
] }
theorem Line48m6_far : farOK pts Line48m6 := by decide +kernel
theorem Line48m6_ok : axisOK pts Line48m6 = true := by decide +kernel
def Line48m7 : Macro := { x0 := (973430849536), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8530911186210701540743988340),(4689771659992127808575766528),(4889710434378272145408),(0),(886973340089086509056),(4235933045042959)), boxes := [
    (((973414072320),(973447626752),(0),(0)),((648942714880),(648965084502),(-7296917923),(0)))
] }
theorem Line48m7_far : farOK pts Line48m7 := by decide +kernel
theorem Line48m7_ok : axisOK pts Line48m7 = true := by decide +kernel
def Line48Data : List Macro := [Line48m0,Line48m1,Line48m2,Line48m3,Line48m4,Line48m5,Line48m6,Line48m7]
theorem Line48_farAll : ∀ m ∈ Line48Data, farOK pts m := by
  intro m hm
  simp only [Line48Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line48m0_far,Line48m1_far,Line48m2_far,Line48m3_far,Line48m4_far,Line48m5_far,Line48m6_far,Line48m7_far]
theorem Line48_okAll : ∀ m ∈ Line48Data, axisOK pts m = true := by
  intro m hm
  simp only [Line48Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line48m0_ok,Line48m1_ok,Line48m2_ok,Line48m3_ok,Line48m4_ok,Line48m5_ok,Line48m6_ok,Line48m7_ok]
end CatalanCore.Cert.SigmaQuarter
