module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line61m0 : Macro := { x0 := (979185434624), y0 := (0), i0 := 1200, i1 := 1200, fd := ((9314398802344176241248175900),(4666568600067041766070747136),(4914426189133281427456),(0),(886973340089086509056),(4192882754461467)), boxes := [
    (((979118325760),(979252543488),(0),(0)),((652745550506),(652835028992),(-7297014387),(0)))
] }
theorem Line61m0_far : farOK pts Line61m0 := by decide +kernel
theorem Line61m0_ok : axisOK pts Line61m0 = true := by decide +kernel
def Line61m1 : Macro := { x0 := (979319652352), y0 := (0), i0 := 1200, i1 := 1200, fd := ((9332627217234039029569828575),(4666030212020868157813293056),(4915002649885584850944),(0),(886973340089086509056),(4191886580105775)), boxes := [
    (((979252543488),(979386761216),(0),(0)),((652835028992),(652924507478),(-7296982988),(0)))
] }
theorem Line61m1_far : farOK pts Line61m1 := by decide +kernel
theorem Line61m1_ok : axisOK pts Line61m1 = true := by decide +kernel
def Line61m2 : Macro := { x0 := (979453870080), y0 := (0), i0 := 1200, i1 := 1200, fd := ((9350865437444771482409232766),(4665492018529268823524704256),(4915579110637888274432),(0),(886973340089086509056),(4190890831965312)), boxes := [
    (((979386761216),(979520978944),(0),(0)),((652924507477),(653013985963),(-7296950235),(0)))
] }
theorem Line61m2_far : farOK pts Line61m2 := by decide +kernel
theorem Line61m2_ok : axisOK pts Line61m2 = true := by decide +kernel
def Line61m3 : Macro := { x0 := (979588087808), y0 := (0), i0 := 1200, i1 := 1200, fd := ((9369090766720446237270729758),(4664953614464148823565991936),(4916155571390191697920),(0),(886973340089086509056),(4189895140569322)), boxes := [
    (((979520978944),(979655196672),(0),(0)),((653013985962),(653103464448),(-7296916887),(0)))
] }
theorem Line61m3_far : farOK pts Line61m3 := by decide +kernel
theorem Line61m3_ok : axisOK pts Line61m3 = true := by decide +kernel
def Line61m4 : Macro := { x0 := (979722305536), y0 := (0), i0 := 1200, i1 := 1200, fd := ((9387310989855837705783910356),(4664415625059768857359679488),(4916732032142495121408),(0),(886973340089086509056),(4188900056248641)), boxes := [
    (((979655196672),(979789414400),(0),(0)),((653103464448),(653192942934),(-7296883210),(0)))
] }
theorem Line61m4_far : farOK pts Line61m4 := by decide +kernel
theorem Line61m4_ok : axisOK pts Line61m4 = true := by decide +kernel
def Line61m5 : Macro := { x0 := (979856523264), y0 := (0), i0 := 1200, i1 := 1200, fd := ((9405533720528090422110795469),(4663877638247413081892454400),(4917308492894798544896),(0),(886973340089086509056),(4187905228918273)), boxes := [
    (((979789414400),(979923632128),(0),(0)),((653192942933),(653282421419),(-7296849462),(0)))
] }
theorem Line61m5_far : farOK pts Line61m5 := by decide +kernel
theorem Line61m5_ok : axisOK pts Line61m5 = true := by decide +kernel
def Line61m6 : Macro := { x0 := (979990740992), y0 := (0), i0 := 1200, i1 := 1200, fd := ((9423760093069943294240718626),(4663339682114380800162791424),(4917884953647101968384),(0),(886973340089086509056),(4186910668540372)), boxes := [
    (((979923632128),(980057849856),(0),(0)),((653282421418),(653371899904),(-7296815680),(0)))
] }
theorem Line61m6_far : farOK pts Line61m6 := by decide +kernel
theorem Line61m6_ok : axisOK pts Line61m6 = true := by decide +kernel
def Line61m7 : Macro := { x0 := (980124958720), y0 := (0), i0 := 1200, i1 := 1200, fd := ((9441970258011105042939164821),(4662802248429404603923496960),(4918461414399405391872),(0),(886973340089086509056),(4185916825158579)), boxes := [
    (((980057849856),(980192067584),(0),(0)),((653371899904),(653461378390),(-7296781192),(0)))
] }
theorem Line61m7_far : farOK pts Line61m7 := by decide +kernel
theorem Line61m7_ok : axisOK pts Line61m7 = true := by decide +kernel
def Line61Data : List Macro := [Line61m0,Line61m1,Line61m2,Line61m3,Line61m4,Line61m5,Line61m6,Line61m7]
theorem Line61_farAll : ∀ m ∈ Line61Data, farOK pts m := by
  intro m hm
  simp only [Line61Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line61m0_far,Line61m1_far,Line61m2_far,Line61m3_far,Line61m4_far,Line61m5_far,Line61m6_far,Line61m7_far]
theorem Line61_okAll : ∀ m ∈ Line61Data, axisOK pts m = true := by
  intro m hm
  simp only [Line61Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line61m0_ok,Line61m1_ok,Line61m2_ok,Line61m3_ok,Line61m4_ok,Line61m5_ok,Line61m6_ok,Line61m7_ok]
end CatalanCore.Cert.SigmaQuarter
