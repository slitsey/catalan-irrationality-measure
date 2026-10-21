module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line29m0 : Macro := { x0 := (968095694848), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7801034639320892338582053838),(4711490794937357811159334912),(4866796119474211061760),(0),(886973340089086509056),(4276443003148464)), boxes := [
    (((968078917632),(968112472064),(0),(0)),((645385945088),(645408314710),(-7296971749),(0)))
] }
theorem Line29m0_far : farOK pts Line29m0 := by decide +kernel
theorem Line29m0_ok : axisOK pts Line29m0 = true := by decide +kernel
def Line29m1 : Macro := { x0 := (968129249280), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7805636109436163613359326512),(4711353586395661102365868032),(4866940234662286917632),(0),(886973340089086509056),(4276186419142720)), boxes := [
    (((968112472064),(968146026496),(0),(0)),((645408314709),(645430684331),(-7296973837),(0)))
] }
theorem Line29m1_far : farOK pts Line29m1 := by decide +kernel
theorem Line29m1_ok : axisOK pts Line29m1 = true := by decide +kernel
def Line29m2 : Macro := { x0 := (968162803712), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7810234957231640743898362605),(4711216366741645724245753856),(4867084349850362773504),(0),(886973340089086509056),(4275929845578177)), boxes := [
    (((968146026496),(968179580928),(0),(0)),((645430684330),(645453053952),(-7296975860),(0)))
] }
theorem Line29m2_far : farOK pts Line29m2 := by decide +kernel
theorem Line29m2_ok : axisOK pts Line29m2 = true := by decide +kernel
def Line29m3 : Macro := { x0 := (968196358144), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7814837481599011757364986037),(4711079129686050153904340992),(4867228465038438629376),(0),(886973340089086509056),(4275673269076787)), boxes := [
    (((968179580928),(968213135360),(0),(0)),((645453053952),(645475423574),(-7296978033),(0)))
] }
theorem Line29m3_far : farOK pts Line29m3 := by decide +kernel
theorem Line29m3_ok : axisOK pts Line29m3 = true := by decide +kernel
def Line29m4 : Macro := { x0 := (968229912576), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7819440471541981694702731761),(4710941984746129153939800064),(4867372580226514485248),(0),(886973340089086509056),(4275416787369055)), boxes := [
    (((968213135360),(968246689792),(0),(0)),((645475423573),(645497793195),(-7296983121),(0)))
] }
theorem Line29m4_far : farOK pts Line29m4 := by decide +kernel
theorem Line29m4_ok : axisOK pts Line29m4 = true := by decide +kernel
def Line29m5 : Macro := { x0 := (968263467008), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7824045080393116290344978190),(4710804785251652762400129024),(4867516695414590341120),(0),(886973340089086509056),(4275160278263047)), boxes := [
    (((968246689792),(968280244224),(0),(0)),((645497793194),(645520162816),(-7296984834),(0)))
] }
theorem Line29m5_far : farOK pts Line29m5 := by decide +kernel
theorem Line29m5_ok : axisOK pts Line29m5 = true := by decide +kernel
def Line29m6 : Macro := { x0 := (968297021440), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7828643451277298124142164376),(4710667534863755595922800640),(4867660810602666196992),(0),(886973340089086509056),(4274903740975157)), boxes := [
    (((968280244224),(968313798656),(0),(0)),((645520162816),(645542532438),(-7296986635),(0)))
] }
theorem Line29m6_far : farOK pts Line29m6 := by decide +kernel
theorem Line29m6_ok : axisOK pts Line29m6 = true := by decide +kernel
def Line29m7 : Macro := { x0 := (968330575872), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7833238326240360317569147144),(4710530302279039257742934016),(4867804925790742052864),(0),(886973340089086509056),(4274647225378955)), boxes := [
    (((968313798656),(968347353088),(0),(0)),((645542532437),(645564902059),(-7296988341),(0)))
] }
theorem Line29m7_far : farOK pts Line29m7 := by decide +kernel
theorem Line29m7_ok : axisOK pts Line29m7 = true := by decide +kernel
def Line29Data : List Macro := [Line29m0,Line29m1,Line29m2,Line29m3,Line29m4,Line29m5,Line29m6,Line29m7]
theorem Line29_farAll : ∀ m ∈ Line29Data, farOK pts m := by
  intro m hm
  simp only [Line29Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line29m0_far,Line29m1_far,Line29m2_far,Line29m3_far,Line29m4_far,Line29m5_far,Line29m6_far,Line29m7_far]
theorem Line29_okAll : ∀ m ∈ Line29Data, axisOK pts m = true := by
  intro m hm
  simp only [Line29Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line29m0_ok,Line29m1_ok,Line29m2_ok,Line29m3_ok,Line29m4_ok,Line29m5_ok,Line29m6_ok,Line29m7_ok]
end CatalanCore.Cert.SigmaQuarter
