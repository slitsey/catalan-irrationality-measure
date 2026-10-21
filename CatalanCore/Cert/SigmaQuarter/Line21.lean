module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line21m0 : Macro := { x0 := (965595889664), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7457875920528449273874967410),(4721736788362487445836922880),(4856059537962559799296),(0),(886973340089086509056),(4295625101368619)), boxes := [
    (((965562335232),(965629444096),(0),(0)),((643708223488),(643752962731),(-7297070862),(0)))
] }
theorem Line21m0_far : farOK pts Line21m0 := by decide +kernel
theorem Line21m0_ok : axisOK pts Line21m0 = true := by decide +kernel
def Line21m1 : Macro := { x0 := (965662998528), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7467087489478102051942131998),(4721461185963524667744256000),(4856347768338711511040),(0),(886973340089086509056),(4295108489190142)), boxes := [
    (((965629444096),(965696552960),(0),(0)),((643752962730),(643797701974),(-7297082490),(0)))
] }
theorem Line21m1_far : farOK pts Line21m1 := by decide +kernel
theorem Line21m1_ok : axisOK pts Line21m1 = true := by decide +kernel
def Line21m2 : Macro := { x0 := (965730107392), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7476313976060927134980127786),(4721185406114433590646996992),(4856635998714863222784),(0),(886973340089086509056),(4294591784860700)), boxes := [
    (((965696552960),(965763661824),(0),(0)),((643797701973),(643842441216),(-7297090374),(0)))
] }
theorem Line21m2_far : farOK pts Line21m2 := by decide +kernel
theorem Line21m2_ok : axisOK pts Line21m2 = true := by decide +kernel
def Line21m3 : Macro := { x0 := (965797216256), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7485541801165156936803780876),(4720910028028166796771328000),(4856924229091014934528),(0),(886973340089086509056),(4294075503498545)), boxes := [
    (((965763661824),(965830770688),(0),(0)),((643842441216),(643887180459),(-7297101414),(0)))
] }
theorem Line21m3_far : farOK pts Line21m3 := by decide +kernel
theorem Line21m3_ok : axisOK pts Line21m3 = true := by decide +kernel
def Line21m4 : Macro := { x0 := (965864325120), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7494764607237717409851421892),(4720634535500495155364560896),(4857212459467166646272),(0),(886973340089086509056),(4293559184495873)), boxes := [
    (((965830770688),(965897879552),(0),(0)),((643887180458),(643931919702),(-7297108779),(0)))
] }
theorem Line21m4_far : farOK pts Line21m4 := by decide +kernel
theorem Line21m4_ok : axisOK pts Line21m4 = true := by decide +kernel
def Line21m5 : Macro := { x0 := (965931433984), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7503985659361021411501556150),(4720358835246926432566050816),(4857500689843318358016),(0),(886973340089086509056),(4293042744903197)), boxes := [
    (((965897879552),(965964988416),(0),(0)),((643931919701),(643976658944),(-7297116247),(0)))
] }
theorem Line21m5_far : farOK pts Line21m5 := by decide +kernel
theorem Line21m5_ok : axisOK pts Line21m5 = true := by decide +kernel
def Line21m6 : Macro := { x0 := (965998542848), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7513200470584861505476754500),(4720083343251852017249878016),(4857788920219470069760),(0),(886973340089086509056),(4292526562010706)), boxes := [
    (((965964988416),(966032097280),(0),(0)),((643976658944),(644021398187),(-7297123280),(0)))
] }
theorem Line21m6_far : farOK pts Line21m6 := by decide +kernel
theorem Line21m6_ok : axisOK pts Line21m6 = true := by decide +kernel
def Line21m7 : Macro := { x0 := (966065651712), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7522428134263135551534952342),(4719808007715399624469184512),(4858077150595621781504),(0),(886973340089086509056),(4292010573112114)), boxes := [
    (((966032097280),(966099206144),(0),(0)),((644021398186),(644066137430),(-7297130894),(0)))
] }
theorem Line21m7_far : farOK pts Line21m7 := by decide +kernel
theorem Line21m7_ok : axisOK pts Line21m7 = true := by decide +kernel
def Line21Data : List Macro := [Line21m0,Line21m1,Line21m2,Line21m3,Line21m4,Line21m5,Line21m6,Line21m7]
theorem Line21_farAll : ∀ m ∈ Line21Data, farOK pts m := by
  intro m hm
  simp only [Line21Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line21m0_far,Line21m1_far,Line21m2_far,Line21m3_far,Line21m4_far,Line21m5_far,Line21m6_far,Line21m7_far]
theorem Line21_okAll : ∀ m ∈ Line21Data, axisOK pts m = true := by
  intro m hm
  simp only [Line21Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line21m0_ok,Line21m1_ok,Line21m2_ok,Line21m3_ok,Line21m4_ok,Line21m5_ok,Line21m6_ok,Line21m7_ok]
end CatalanCore.Cert.SigmaQuarter
