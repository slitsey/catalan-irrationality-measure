module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line15m0 : Macro := { x0 := (962374664192), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7014593296326522963347780773),(4735005678486410918402457600),(4842224479907277635584),(0),(886973340089086509056),(4320534690223739)), boxes := [
    (((962341109760),(962408218624),(0),(0)),((641560739840),(641605479083),(-7296545200),(0)))
] }
theorem Line15m0_far : farOK pts Line15m0 := by decide +kernel
theorem Line15m0_ok : axisOK pts Line15m0 = true := by decide +kernel
def Line15m1 : Macro := { x0 := (962441773056), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7023837882433430877019273516),(4734728549488795822089633792),(4842512710283429347328),(0),(886973340089086509056),(4320013578904134)), boxes := [
    (((962408218624),(962475327488),(0),(0)),((641605479082),(641650218326),(-7296558925),(0)))
] }
theorem Line15m1_far : farOK pts Line15m1 := by decide +kernel
theorem Line15m1_ok : axisOK pts Line15m1 = true := by decide +kernel
def Line15m2 : Macro := { x0 := (962508881920), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7033086533167066541241785372),(4734451429855197547267031040),(4842800940659581059072),(0),(886973340089086509056),(4319492539459510)), boxes := [
    (((962475327488),(962542436352),(0),(0)),((641650218325),(641694957568),(-7296572370),(0)))
] }
theorem Line15m2_far : farOK pts Line15m2 := by decide +kernel
theorem Line15m2_ok : axisOK pts Line15m2 = true := by decide +kernel
def Line15m3 : Macro := { x0 := (962575990784), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7042326757680144208213927598),(4734174140562916649946120192),(4843089171035732770816),(0),(886973340089086509056),(4318971424111478)), boxes := [
    (((962542436352),(962609545216),(0),(0)),((641694957568),(641739696811),(-7296585881),(0)))
] }
theorem Line15m3_far : farOK pts Line15m3 := by decide +kernel
theorem Line15m3_ok : axisOK pts Line15m3 = true := by decide +kernel
def Line15m4 : Macro := { x0 := (962643099648), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7051561671662880248288747497),(4733897202726366836662009856),(4843377401411884482560),(0),(886973340089086509056),(4318450685520485)), boxes := [
    (((962609545216),(962676654080),(0),(0)),((641739696810),(641784436054),(-7296595771),(0)))
] }
theorem Line15m4_far : farOK pts Line15m4 := by decide +kernel
theorem Line15m4_ok : axisOK pts Line15m4 = true := by decide +kernel
def Line15m5 : Macro := { x0 := (962710208512), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7060807931876585581242975132),(4733620052631183030893215744),(4843665631788036194304),(0),(886973340089086509056),(4317929821777515)), boxes := [
    (((962676654080),(962743762944),(0),(0)),((641784436053),(641829175296),(-7296609051),(0)))
] }
theorem Line15m5_far : farOK pts Line15m5 := by decide +kernel
theorem Line15m5_ok : axisOK pts Line15m5 = true := by decide +kernel
def Line15m6 : Macro := { x0 := (962777317376), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7070057954442823816237228332),(4733342979716387164401041408),(4843953862164187906048),(0),(886973340089086509056),(4317409103194204)), boxes := [
    (((962743762944),(962810871808),(0),(0)),((641829175296),(641873914539),(-7296622042),(0)))
] }
theorem Line15m6_far : farOK pts Line15m6 := by decide +kernel
theorem Line15m6_ok : axisOK pts Line15m6 = true := by decide +kernel
def Line15m7 : Macro := { x0 := (962844426240), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7079306014488872697755072666),(4733065925976898036198539264),(4844242092540339617792),(0),(886973340089086509056),(4316888451366401)), boxes := [
    (((962810871808),(962877980672),(0),(0)),((641873914538),(641918653782),(-7296635315),(0)))
] }
theorem Line15m7_far : farOK pts Line15m7 := by decide +kernel
theorem Line15m7_ok : axisOK pts Line15m7 = true := by decide +kernel
def Line15Data : List Macro := [Line15m0,Line15m1,Line15m2,Line15m3,Line15m4,Line15m5,Line15m6,Line15m7]
theorem Line15_farAll : ∀ m ∈ Line15Data, farOK pts m := by
  intro m hm
  simp only [Line15Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line15m0_far,Line15m1_far,Line15m2_far,Line15m3_far,Line15m4_far,Line15m5_far,Line15m6_far,Line15m7_far]
theorem Line15_okAll : ∀ m ∈ Line15Data, axisOK pts m = true := by
  intro m hm
  simp only [Line15Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line15m0_ok,Line15m1_ok,Line15m2_ok,Line15m3_ok,Line15m4_ok,Line15m5_ok,Line15m6_ok,Line15m7_ok]
end CatalanCore.Cert.SigmaQuarter
