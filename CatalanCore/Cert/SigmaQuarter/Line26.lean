module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line26m0 : Macro := { x0 := (967290388480), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7690561694671867137804478704),(4714786560229946347217747968),(4863337354960390520832),(0),(886973340089086509056),(4282608278948601)), boxes := [
    (((967273611264),(967307165696),(0),(0)),((644849074176),(644871443798),(-7296919995),(0)))
] }
theorem Line26m0_far : farOK pts Line26m0 := by decide +kernel
theorem Line26m0_ok : axisOK pts Line26m0 = true := by decide +kernel
def Line26m1 : Macro := { x0 := (967323942912), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7695170404388791023307978175),(4714649312314986180992434176),(4863481470148466376704),(0),(886973340089086509056),(4282351276221408)), boxes := [
    (((967307165696),(967340720128),(0),(0)),((644871443797),(644893813419),(-7296922762),(0)))
] }
theorem Line26m1_far : farOK pts Line26m1 := by decide +kernel
theorem Line26m1_ok : axisOK pts Line26m1 = true := by decide +kernel
def Line26m2 : Macro := { x0 := (967357497344), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7699776201294455102227966763),(4714511753399155223114612736),(4863625585336542232576),(0),(886973340089086509056),(4282094004613404)), boxes := [
    (((967340720128),(967374274560),(0),(0)),((644893813418),(644916183040),(-7296925456),(0)))
] }
theorem Line26m2_far : farOK pts Line26m2 := by decide +kernel
theorem Line26m2_ok : axisOK pts Line26m2 = true := by decide +kernel
def Line26m3 : Macro := { x0 := (967391051776), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7704375696268194305414368110),(4714374321668957211111849984),(4863769700524618088448),(0),(886973340089086509056),(4281836884179639)), boxes := [
    (((967374274560),(967407828992),(0),(0)),((644916183040),(644938552662),(-7296927960),(0)))
] }
theorem Line26m3_far : farOK pts Line26m3 := by decide +kernel
theorem Line26m3_ok : axisOK pts Line26m3 = true := by decide +kernel
def Line26m4 : Macro := { x0 := (967424606208), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7708983826294250093953746247),(4714237098967229158648643584),(4863913815712693944320),(0),(886973340089086509056),(4281579931510003)), boxes := [
    (((967407828992),(967441383424),(0),(0)),((644938552661),(644960922283),(-7296930368),(0)))
] }
theorem Line26m4_far : farOK pts Line26m4 := by decide +kernel
theorem Line26m4_ok : axisOK pts Line26m4 = true := by decide +kernel
def Line26m5 : Macro := { x0 := (967458160640), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7713582769115614342351642839),(4714099615133455347381239808),(4864057930900769800192),(0),(886973340089086509056),(4281322785722398)), boxes := [
    (((967441383424),(967474937856),(0),(0)),((644960922282),(644983291904),(-7296929982),(0)))
] }
theorem Line26m5_far : farOK pts Line26m5 := by decide +kernel
theorem Line26m5_ok : axisOK pts Line26m5 = true := by decide +kernel
def Line26m6 : Macro := { x0 := (967491715072), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7718187101298299345884079921),(4713962206505509040448208896),(4864202046088845656064),(0),(886973340089086509056),(4281065726764715)), boxes := [
    (((967474937856),(967508492288),(0),(0)),((644983291904),(645005661526),(-7296932398),(0)))
] }
theorem Line26m6_far : farOK pts Line26m6 := by decide +kernel
theorem Line26m6_ok : axisOK pts Line26m6 = true := by decide +kernel
def Line26m7 : Macro := { x0 := (967525269504), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7722794993522759759568472064),(4713824859089898336138493952),(4864346161276921511936),(0),(886973340089086509056),(4280808718901779)), boxes := [
    (((967508492288),(967542046720),(0),(0)),((645005661525),(645028031147),(-7296934960),(0)))
] }
theorem Line26m7_far : farOK pts Line26m7 := by decide +kernel
theorem Line26m7_ok : axisOK pts Line26m7 = true := by decide +kernel
def Line26Data : List Macro := [Line26m0,Line26m1,Line26m2,Line26m3,Line26m4,Line26m5,Line26m6,Line26m7]
theorem Line26_farAll : ∀ m ∈ Line26Data, farOK pts m := by
  intro m hm
  simp only [Line26Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line26m0_far,Line26m1_far,Line26m2_far,Line26m3_far,Line26m4_far,Line26m5_far,Line26m6_far,Line26m7_far]
theorem Line26_okAll : ∀ m ∈ Line26Data, axisOK pts m = true := by
  intro m hm
  simp only [Line26Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line26m0_ok,Line26m1_ok,Line26m2_ok,Line26m3_ok,Line26m4_ok,Line26m5_ok,Line26m6_ok,Line26m7_ok]
end CatalanCore.Cert.SigmaQuarter
