module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line9m0 : Macro := { x0 := (955227570176), y0 := (0), i0 := 1200, i1 := 1200, fd := ((6026580420760679018526608552),(4764714247369010459757969408),(4811527944847120334848),(0),(886973340089086509056),(4376585648483436)), boxes := [
    (((955093352448),(955361787904),(0),(0)),((636728901632),(636907858603),(-7296403652),(0)))
] }
theorem Line9m0_far : farOK pts Line9m0 := by decide +kernel
theorem Line9m0_ok : axisOK pts Line9m0 = true := by decide +kernel
def Line9m1 : Macro := { x0 := (955496005632), y0 := (0), i0 := 1200, i1 := 1200, fd := ((6063811593919542190087093715),(4763591974575074267001389056),(4812680866351727181824),(0),(886973340089086509056),(4374460967839607)), boxes := [
    (((955361787904),(955630223360),(0),(0)),((636907858602),(637086815574),(-7296505590),(0)))
] }
theorem Line9m1_far : farOK pts Line9m1 := by decide +kernel
theorem Line9m1_ok : axisOK pts Line9m1 = true := by decide +kernel
def Line9m2 : Macro := { x0 := (955764441088), y0 := (0), i0 := 1200, i1 := 1200, fd := ((6101020846972561649863467577),(4762469691843707429903335424),(4813833787856334028800),(0),(886973340089086509056),(4372337343041595)), boxes := [
    (((955630223360),(955898658816),(0),(0)),((637086815573),(637265772544),(-7296603592),(0)))
] }
theorem Line9m2_far : farOK pts Line9m2 := by decide +kernel
theorem Line9m2_ok : axisOK pts Line9m2 = true := by decide +kernel
def Line9m3 : Macro := { x0 := (956032876544), y0 := (0), i0 := 1200, i1 := 1200, fd := ((6138226456454092546689633410),(4761348452191730287459041280),(4814986709360940875776),(0),(886973340089086509056),(4370215738028360)), boxes := [
    (((955898658816),(956167094272),(0),(0)),((637265772544),(637444729515),(-7296702264),(0)))
] }
theorem Line9m3_far : farOK pts Line9m3 := by decide +kernel
theorem Line9m3_ok : axisOK pts Line9m3 = true := by decide +kernel
def Line9m4 : Macro := { x0 := (956301312000), y0 := (0), i0 := 1200, i1 := 1200, fd := ((6175413014411663974958478666),(4760227382363693945418874880),(4816139630865547722752),(0),(886973340089086509056),(4368095351100671)), boxes := [
    (((956167094272),(956435529728),(0),(0)),((637444729514),(637623686486),(-7296804183),(0)))
] }
theorem Line9m4_far : farOK pts Line9m4 := by decide +kernel
theorem Line9m4_ok : axisOK pts Line9m4 = true := by decide +kernel
def Line9m5 : Macro := { x0 := (956569747456), y0 := (0), i0 := 1200, i1 := 1200, fd := ((6212590452381410858662647625),(4759106834016734267252801536),(4817292552370154569728),(0),(886973340089086509056),(4365976519957736)), boxes := [
    (((956435529728),(956703965184),(0),(0)),((637623686485),(637802643456),(-7296898063),(0)))
] }
theorem Line9m5_far : farOK pts Line9m5 := by decide +kernel
theorem Line9m5_ok : axisOK pts Line9m5 = true := by decide +kernel
def Line9m6 : Macro := { x0 := (956838182912), y0 := (0), i0 := 1200, i1 := 1200, fd := ((6249767073884739837797599116),(4757987017546677911755489280),(4818445473874761416704),(0),(886973340089086509056),(4363859405622246)), boxes := [
    (((956703965184),(956972400640),(0),(0)),((637802643456),(637981600427),(-7296988077),(0)))
] }
theorem Line9m6_far : farOK pts Line9m6 := by decide +kernel
theorem Line9m6_ok : axisOK pts Line9m6 = true := by decide +kernel
def Line9m7 : Macro := { x0 := (957106618368), y0 := (0), i0 := 1200, i1 := 1200, fd := ((6286931179095033822207152296),(4756867611893619341572833280),(4819598395379368263680),(0),(886973340089086509056),(4361743744312637)), boxes := [
    (((956972400640),(957240836096),(0),(0)),((637981600426),(638160557398),(-7297079083),(0)))
] }
theorem Line9m7_far : farOK pts Line9m7 := by decide +kernel
theorem Line9m7_ok : axisOK pts Line9m7 = true := by decide +kernel
def Line9Data : List Macro := [Line9m0,Line9m1,Line9m2,Line9m3,Line9m4,Line9m5,Line9m6,Line9m7]
theorem Line9_farAll : ∀ m ∈ Line9Data, farOK pts m := by
  intro m hm
  simp only [Line9Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line9m0_far,Line9m1_far,Line9m2_far,Line9m3_far,Line9m4_far,Line9m5_far,Line9m6_far,Line9m7_far]
theorem Line9_okAll : ∀ m ∈ Line9Data, axisOK pts m = true := by
  intro m hm
  simp only [Line9Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line9m0_ok,Line9m1_ok,Line9m2_ok,Line9m3_ok,Line9m4_ok,Line9m5_ok,Line9m6_ok,Line9m7_ok]
end CatalanCore.Cert.SigmaQuarter
