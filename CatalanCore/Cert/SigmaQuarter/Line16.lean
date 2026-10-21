module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line16m0 : Macro := { x0 := (962911535104), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7088556125889794794264870602),(4732789019737219508588773376),(4844530322916491329536),(0),(886973340089086509056),(4316368012467655)), boxes := [
    (((962877980672),(962945089536),(0),(0)),((641918653781),(641963393024),(-7296651880),(0)))
] }
theorem Line16m0_far : farOK pts Line16m0 := by decide +kernel
theorem Line16m0_ok : axisOK pts Line16m0 = true := by decide +kernel
def Line16m1 : Macro := { x0 := (962978643968), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7097795495528264089750888393),(4732512065017894494280941568),(4844818553292643041280),(0),(886973340089086509056),(4315847582300976)), boxes := [
    (((962945089536),(963012198400),(0),(0)),((641963393024),(642008132267),(-7296664416),(0)))
] }
theorem Line16m1_far : farOK pts Line16m1 := by decide +kernel
theorem Line16m1_ok : axisOK pts Line16m1 = true := by decide +kernel
def Line16m2 : Macro := { x0 := (963045752832), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7107037320199923061568831606),(4732235252838981896802009088),(4845106783668794753024),(0),(886973340089086509056),(4315327348655262)), boxes := [
    (((963012198400),(963079307264),(0),(0)),((642008132266),(642052871510),(-7296676622),(0)))
] }
theorem Line16m2_far : farOK pts Line16m2 := by decide +kernel
theorem Line16m2_ok : axisOK pts Line16m2 = true := by decide +kernel
def Line16m3 : Macro := { x0 := (963112861696), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7116278637987682452493322336),(4731958421074696246728982528),(4845395014044946464768),(0),(886973340089086509056),(4314807171832959)), boxes := [
    (((963079307264),(963146416128),(0),(0)),((642052871509),(642097610752),(-7296689156),(0)))
] }
theorem Line16m3_far : farOK pts Line16m3 := by decide +kernel
theorem Line16m3_ok : axisOK pts Line16m3 = true := by decide +kernel
def Line16m4 : Macro := { x0 := (963179970560), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7125528956885447234638583864),(4731681371368211769564921856),(4845683244421098176512),(0),(886973340089086509056),(4314286845386531)), boxes := [
    (((963146416128),(963213524992),(0),(0)),((642097610752),(642142349995),(-7296701585),(0)))
] }
theorem Line16m4_far : farOK pts Line16m4 := by decide +kernel
theorem Line16m4_ok : axisOK pts Line16m4 = true := by decide +kernel
def Line16m5 : Macro := { x0 := (963247079424), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7134768856777569771889034283),(4731404603024162008414617600),(4845971474797249888256),(0),(886973340089086509056),(4313766851944203)), boxes := [
    (((963213524992),(963280633856),(0),(0)),((642142349994),(642187089238),(-7296714002),(0)))
] }
theorem Line16m5_far : farOK pts Line16m5 := by decide +kernel
theorem Line16m5_ok : axisOK pts Line16m5 = true := by decide +kernel
def Line16m6 : Macro := { x0 := (963314188288), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7144006758838492421254842638),(4731127905236078938817757184),(4846259705173401600000),(0),(886973340089086509056),(4313246981487717)), boxes := [
    (((963280633856),(963347742720),(0),(0)),((642187089237),(642231828480),(-7296725945),(0)))
] }
theorem Line16m6_far : farOK pts Line16m6 := by decide +kernel
theorem Line16m6_ok : axisOK pts Line16m6 = true := by decide +kernel
def Line16m7 : Macro := { x0 := (963381297152), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7153244567629071158371592631),(4730850959409470730957946880),(4846547935549553311744),(0),(886973340089086509056),(4312726963240078)), boxes := [
    (((963347742720),(963414851584),(0),(0)),((642231828480),(642276567723),(-7296741021),(0)))
] }
theorem Line16m7_far : farOK pts Line16m7 := by decide +kernel
theorem Line16m7_ok : axisOK pts Line16m7 = true := by decide +kernel
def Line16Data : List Macro := [Line16m0,Line16m1,Line16m2,Line16m3,Line16m4,Line16m5,Line16m6,Line16m7]
theorem Line16_farAll : ∀ m ∈ Line16Data, farOK pts m := by
  intro m hm
  simp only [Line16Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line16m0_far,Line16m1_far,Line16m2_far,Line16m3_far,Line16m4_far,Line16m5_far,Line16m6_far,Line16m7_far]
theorem Line16_okAll : ∀ m ∈ Line16Data, axisOK pts m = true := by
  intro m hm
  simp only [Line16Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line16m0_ok,Line16m1_ok,Line16m2_ok,Line16m3_ok,Line16m4_ok,Line16m5_ok,Line16m6_ok,Line16m7_ok]
end CatalanCore.Cert.SigmaQuarter
