module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line28m0 : Macro := { x0 := (967827259392), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7764213183638044265960382067),(4712588778582671032423088128),(4865643197969604214784),(0),(886973340089086509056),(4278496530893344)), boxes := [
    (((967810482176),(967844036608),(0),(0)),((645206988117),(645229357739),(-7296954545),(0)))
] }
theorem Line28m0_far : farOK pts Line28m0 := by decide +kernel
theorem Line28m0_ok : axisOK pts Line28m0 = true := by decide +kernel
def Line28m1 : Macro := { x0 := (967860813824), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7768816985537909153218882323),(4712451567287176501276966912),(4865787313157680070656),(0),(886973340089086509056),(4278239808899366)), boxes := [
    (((967844036608),(967877591040),(0),(0)),((645229357738),(645251727360),(-7296956795),(0)))
] }
theorem Line28m1_far : farOK pts Line28m1 := by decide +kernel
theorem Line28m1_ok : axisOK pts Line28m1 = true := by decide +kernel
def Line28m2 : Macro := { x0 := (967894368256), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7773423081398194866463519511),(4712314245249502504952659968),(4865931428345755926528),(0),(886973340089086509056),(4277983021752367)), boxes := [
    (((967877591040),(967911145472),(0),(0)),((645251727360),(645274096982),(-7296959148),(0)))
] }
theorem Line28m2_far : farOK pts Line28m2 := by decide +kernel
theorem Line28m2_ok : axisOK pts Line28m2 = true := by decide +kernel
def Line28m3 : Macro := { x0 := (967927922688), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7778024146404597139132774075),(4712177008684036642828648448),(4866075543533831782400),(0),(886973340089086509056),(4277726313687693)), boxes := [
    (((967911145472),(967944699904),(0),(0)),((645274096981),(645296466603),(-7296961354),(0)))
] }
theorem Line28m3_far : farOK pts Line28m3 := by decide +kernel
theorem Line28m3_ok : axisOK pts Line28m3 = true := by decide +kernel
def Line28m4 : Macro := { x0 := (967961477120), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7782629847473391149280543527),(4712039768681402128834822144),(4866219658721907638272),(0),(886973340089086509056),(4277469614008665)), boxes := [
    (((967944699904),(967978254336),(0),(0)),((645296466602),(645318836224),(-7296963419),(0)))
] }
theorem Line28m4_far : farOK pts Line28m4 := by decide +kernel
theorem Line28m4_ok : axisOK pts Line28m4 = true := by decide +kernel
def Line28m5 : Macro := { x0 := (967995031552), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7787234649700403004599364943),(4711902568290592968822161408),(4866363773909983494144),(0),(886973340089086509056),(4277212980730289)), boxes := [
    (((967978254336),(968011808768),(0),(0)),((645318836224),(645341205846),(-7296965662),(0)))
] }
theorem Line28m5_far : farOK pts Line28m5 := by decide +kernel
theorem Line28m5_ok : axisOK pts Line28m5 = true := by decide +kernel
def Line28m6 : Macro := { x0 := (968028585984), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7791838185730477924674636578),(4711765309262493135325757440),(4866507889098059350016),(0),(886973340089086509056),(4276956296845504)), boxes := [
    (((968011808768),(968045363200),(0),(0)),((645341205845),(645363575467),(-7296967886),(0)))
] }
theorem Line28m6_far : farOK pts Line28m6 := by decide +kernel
theorem Line28m6_ok : axisOK pts Line28m6 = true := by decide +kernel
def Line28m7 : Macro := { x0 := (968062140416), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7796432971460522335724324614),(4711627950408016375930224640),(4866652004286135205888),(0),(886973340089086509056),(4276699558653275)), boxes := [
    (((968045363200),(968078917632),(0),(0)),((645363575466),(645385945088),(-7296969838),(0)))
] }
theorem Line28m7_far : farOK pts Line28m7 := by decide +kernel
theorem Line28m7_ok : axisOK pts Line28m7 = true := by decide +kernel
def Line28Data : List Macro := [Line28m0,Line28m1,Line28m2,Line28m3,Line28m4,Line28m5,Line28m6,Line28m7]
theorem Line28_farAll : ∀ m ∈ Line28Data, farOK pts m := by
  intro m hm
  simp only [Line28Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line28m0_far,Line28m1_far,Line28m2_far,Line28m3_far,Line28m4_far,Line28m5_far,Line28m6_far,Line28m7_far]
theorem Line28_okAll : ∀ m ∈ Line28Data, axisOK pts m = true := by
  intro m hm
  simp only [Line28Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line28m0_ok,Line28m1_ok,Line28m2_ok,Line28m3_ok,Line28m4_ok,Line28m5_ok,Line28m6_ok,Line28m7_ok]
end CatalanCore.Cert.SigmaQuarter
