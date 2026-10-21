module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line27m0 : Macro := { x0 := (967558823936), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7727399602088890909307471727),(4713687588988601481497608192),(4864490276464997367808),(0),(886973340089086509056),(4280551817905493)), boxes := [
    (((967542046720),(967575601152),(0),(0)),((645028031146),(645050400768),(-7296937041),(0)))
] }
theorem Line27m0_far : farOK pts Line27m0 := by decide +kernel
theorem Line27m0_ok : axisOK pts Line27m0 = true := by decide +kernel
def Line27m1 : Macro := { x0 := (967592378368), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7732004037454420029415648694),(4713550074822188475096432640),(4864634391653073223680),(0),(886973340089086509056),(4280294704167846)), boxes := [
    (((967575601152),(967609155584),(0),(0)),((645050400768),(645072770390),(-7296939396),(0)))
] }
theorem Line27m1_far : farOK pts Line27m1 := by decide +kernel
theorem Line27m1_ok : axisOK pts Line27m1 = true := by decide +kernel
def Line27m2 : Macro := { x0 := (967625932800), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7736605443763545509793454178),(4713412803693545869291094016),(4864778506841149079552),(0),(886973340089086509056),(4280037819887450)), boxes := [
    (((967609155584),(967642710016),(0),(0)),((645072770389),(645095140011),(-7296941672),(0)))
] }
theorem Line27m2_far : farOK pts Line27m2 := by decide +kernel
theorem Line27m2_ok : axisOK pts Line27m2 = true := by decide +kernel
def Line27m3 : Macro := { x0 := (967659487232), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7741194501393933385057083785),(4713275472489711680641368064),(4864922622029224935424),(0),(886973340089086509056),(4279780905337982)), boxes := [
    (((967642710016),(967676264448),(0),(0)),((645095140010),(645117509632),(-7296943554),(0)))
] }
theorem Line27m3_far : farOK pts Line27m3 := by decide +kernel
theorem Line27m3_ok : axisOK pts Line27m3 = true := by decide +kernel
def Line27m4 : Macro := { x0 := (967693041664), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7745799380172720696053422445),(4713138257981689322566975488),(4865066737217300791296),(0),(886973340089086509056),(4279524099956265)), boxes := [
    (((967676264448),(967709818880),(0),(0)),((645117509632),(645139879254),(-7296945626),(0)))
] }
theorem Line27m4_far : farOK pts Line27m4 := by decide +kernel
theorem Line27m4_ok : axisOK pts Line27m4 = true := by decide +kernel
def Line27m5 : Macro := { x0 := (967726596096), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7750401394558303506226207458),(4713000777615772428396920832),(4865210852405376647168),(0),(886973340089086509056),(4279267088529814)), boxes := [
    (((967709818880),(967743373312),(0),(0)),((645139879253),(645162248875),(-7296947858),(0)))
] }
theorem Line27m5_far : farOK pts Line27m5 := by decide +kernel
theorem Line27m5_ok : axisOK pts Line27m5 = true := by decide +kernel
def Line27m6 : Macro := { x0 := (967760150528), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7754999805360569278623530484),(4712863539038170071782522880),(4865354967593452503040),(0),(886973340089086509056),(4279010307350551)), boxes := [
    (((967743373312),(967776927744),(0),(0)),((645162248874),(645184618496),(-7296949991),(0)))
] }
theorem Line27m6_far : farOK pts Line27m6 := by decide +kernel
theorem Line27m6_ok : axisOK pts Line27m6 = true := by decide +kernel
def Line27m7 : Macro := { x0 := (967793704960), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7759605832149014417086278559),(4712726312656423551373869056),(4865499082781528358912),(0),(886973340089086509056),(4278753545024996)), boxes := [
    (((967776927744),(967810482176),(0),(0)),((645184618496),(645206988118),(-7296952407),(0)))
] }
theorem Line27m7_far : farOK pts Line27m7 := by decide +kernel
theorem Line27m7_ok : axisOK pts Line27m7 = true := by decide +kernel
def Line27Data : List Macro := [Line27m0,Line27m1,Line27m2,Line27m3,Line27m4,Line27m5,Line27m6,Line27m7]
theorem Line27_farAll : ∀ m ∈ Line27Data, farOK pts m := by
  intro m hm
  simp only [Line27Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line27m0_far,Line27m1_far,Line27m2_far,Line27m3_far,Line27m4_far,Line27m5_far,Line27m6_far,Line27m7_far]
theorem Line27_okAll : ∀ m ∈ Line27Data, axisOK pts m = true := by
  intro m hm
  simp only [Line27Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line27m0_ok,Line27m1_ok,Line27m2_ok,Line27m3_ok,Line27m4_ok,Line27m5_ok,Line27m6_ok,Line27m7_ok]
end CatalanCore.Cert.SigmaQuarter
