module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line30m0 : Macro := { x0 := (968364130304), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7837838819639077494487600053),(4710393153437495929325223936),(4867949040978817908736),(0),(886973340089086509056),(4274390813761441)), boxes := [
    (((968347353088),(968380907520),(0),(0)),((645564902058),(645587271680),(-7296994017),(0)))
] }
theorem Line30m0_far : farOK pts Line30m0 := by decide +kernel
theorem Line30m0_ok : axisOK pts Line30m0 = true := by decide +kernel
def Line30m1 : Macro := { x0 := (968397684736), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7842440204992278190734792552),(4710255913316370799989489664),(4868093156166893764608),(0),(886973340089086509056),(4274134330621983)), boxes := [
    (((968380907520),(968414461952),(0),(0)),((645587271680),(645609641302),(-7296995418),(0)))
] }
theorem Line30m1_far : farOK pts Line30m1 := by decide +kernel
theorem Line30m1_ok : axisOK pts Line30m1 = true := by decide +kernel
def Line30m2 : Macro := { x0 := (968431239168), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7847044204792962474331331557),(4710118905894291442422579200),(4868237271354969620480),(0),(886973340089086509056),(4273878067091892)), boxes := [
    (((968414461952),(968448016384),(0),(0)),((645609641301),(645632010923),(-7296994397),(0)))
] }
theorem Line30m2_far : farOK pts Line30m2 := by decide +kernel
theorem Line30m2_ok : axisOK pts Line30m2 = true := by decide +kernel
def Line30m3 : Macro := { x0 := (968464793600), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7851644041410303291041378521),(4709981694560063124986462208),(4868381386543045476352),(0),(886973340089086509056),(4273621651110836)), boxes := [
    (((968448016384),(968481570816),(0),(0)),((645632010922),(645654380544),(-7296995856),(0)))
] }
theorem Line30m3_far : farOK pts Line30m3 := by decide +kernel
theorem Line30m3_ok : axisOK pts Line30m3 = true := by decide +kernel
def Line30m4 : Macro := { x0 := (968498348032), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7856244272310512501229968744),(4709844720749334820121149440),(4868525501731121332224),(0),(886973340089086509056),(4273365446916517)), boxes := [
    (((968481570816),(968515125248),(0),(0)),((645654380544),(645676750166),(-7296997353),(0)))
] }
theorem Line30m4_far : farOK pts Line30m4 := by decide +kernel
theorem Line30m4_ok : axisOK pts Line30m4 = true := by decide +kernel
def Line30m5 : Macro := { x0 := (968531902464), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7860839198869684823487733656),(4709707410147487625548267520),(4868669616919197188096),(0),(886973340089086509056),(4273108966021334)), boxes := [
    (((968515125248),(968548679680),(0),(0)),((645676750165),(645699119787),(-7296998333),(0)))
] }
theorem Line30m5_far : farOK pts Line30m5 := by decide +kernel
theorem Line30m5_ok : axisOK pts Line30m5 = true := by decide +kernel
def Line30m6 : Macro := { x0 := (968565456896), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7865441686117147755519830456),(4709570390810077307560591360),(4868813732107273043968),(0),(886973340089086509056),(4272852762357529)), boxes := [
    (((968548679680),(968582234112),(0),(0)),((645699119786),(645721489408),(-7296999815),(0)))
] }
theorem Line30m6_far : farOK pts Line30m6 := by decide +kernel
theorem Line30m6_ok : axisOK pts Line30m6 = true := by decide +kernel
def Line30m7 : Macro := { x0 := (968599011328), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7870038241862248683530850450),(4709433184777089945124798464),(4868957847295348899840),(0),(886973340089086509056),(4272596401087532)), boxes := [
    (((968582234112),(968615788544),(0),(0)),((645721489408),(645743859030),(-7297001120),(0)))
] }
theorem Line30m7_far : farOK pts Line30m7 := by decide +kernel
theorem Line30m7_ok : axisOK pts Line30m7 = true := by decide +kernel
def Line30Data : List Macro := [Line30m0,Line30m1,Line30m2,Line30m3,Line30m4,Line30m5,Line30m6,Line30m7]
theorem Line30_farAll : ∀ m ∈ Line30Data, farOK pts m := by
  intro m hm
  simp only [Line30Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line30m0_far,Line30m1_far,Line30m2_far,Line30m3_far,Line30m4_far,Line30m5_far,Line30m6_far,Line30m7_far]
theorem Line30_okAll : ∀ m ∈ Line30Data, axisOK pts m = true := by
  intro m hm
  simp only [Line30Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line30m0_ok,Line30m1_ok,Line30m2_ok,Line30m3_ok,Line30m4_ok,Line30m5_ok,Line30m6_ok,Line30m7_ok]
end CatalanCore.Cert.SigmaQuarter
