module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line51m0 : Macro := { x0 := (974001274880), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8608755926647798554760443474),(4687461346092387524712464384),(4892160392575561695232),(0),(886973340089086509056),(4231636026265710)), boxes := [
    (((973984497664),(974018052096),(0),(0)),((649322998442),(649345368064),(-7296870742),(0)))
] }
theorem Line51m0_far : farOK pts Line51m0 := by decide +kernel
theorem Line51m0_ok : axisOK pts Line51m0 = true := by decide +kernel
def Line51m1 : Macro := { x0 := (974034829312), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8613330153447849548361389059),(4687325480449029500630859776),(4892304507763637551104),(0),(886973340089086509056),(4231383428967372)), boxes := [
    (((974018052096),(974051606528),(0),(0)),((649345368064),(649367737686),(-7296867406),(0)))
] }
theorem Line51m1_far : farOK pts Line51m1 := by decide +kernel
theorem Line51m1_ok : axisOK pts Line51m1 = true := by decide +kernel
def Line51m2 : Macro := { x0 := (974068383744), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8617903029697600236328869376),(4687189731591593974165143552),(4892448622951713406976),(0),(886973340089086509056),(4231130953613409)), boxes := [
    (((974051606528),(974085160960),(0),(0)),((649367737685),(649390107307),(-7296864049),(0)))
] }
theorem Line51m2_far : farOK pts Line51m2 := by decide +kernel
theorem Line51m2_ok : axisOK pts Line51m2 = true := by decide +kernel
def Line51m3 : Macro := { x0 := (974101938176), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8622478842675075966118990905),(4687053918150761167901032448),(4892592738139789262848),(0),(886973340089086509056),(4230878442184499)), boxes := [
    (((974085160960),(974118715392),(0),(0)),((649390107306),(649412476928),(-7296860817),(0)))
] }
theorem Line51m3_far : farOK pts Line51m3 := by decide +kernel
theorem Line51m3_ok : axisOK pts Line51m3 = true := by decide +kernel
def Line51m4 : Macro := { x0 := (974135492608), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8627058351133313035660967138),(4686917926535942453439430656),(4892736853327865118720),(0),(886973340089086509056),(4230625774175255)), boxes := [
    (((974118715392),(974152269824),(0),(0)),((649412476928),(649434846550),(-7296857368),(0)))
] }
theorem Line51m4_far : farOK pts Line51m4 := by decide +kernel
theorem Line51m4_ok : axisOK pts Line51m4 = true := by decide +kernel
def Line51m5 : Macro := { x0 := (974169047040), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8631639448394538088938142946),(4686782332028071670876012544),(4892880968515940974592),(0),(886973340089086509056),(4230373492266502)), boxes := [
    (((974152269824),(974185824256),(0),(0)),((649434846549),(649457216171),(-7296854212),(0)))
] }
theorem Line51m5_far : farOK pts Line51m5 := by decide +kernel
theorem Line51m5_ok : axisOK pts Line51m5 = true := by decide +kernel
def Line51m6 : Macro := { x0 := (974202601472), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8636217523554480885600422723),(4686646525748044027173601280),(4893025083704016830464),(0),(886973340089086509056),(4230121020638115)), boxes := [
    (((974185824256),(974219378688),(0),(0)),((649457216170),(649479585792),(-7296850979),(0)))
] }
theorem Line51m6_far : farOK pts Line51m6 := by decide +kernel
theorem Line51m6_ok : axisOK pts Line51m6 = true := by decide +kernel
def Line51m7 : Macro := { x0 := (974236155904), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8640795166672467332501968239),(4686510703024344882262507520),(4893169198892092686336),(0),(886973340089086509056),(4229868574212798)), boxes := [
    (((974219378688),(974252933120),(0),(0)),((649479585792),(649501955414),(-7296847757),(0)))
] }
theorem Line51m7_far : farOK pts Line51m7 := by decide +kernel
theorem Line51m7_ok : axisOK pts Line51m7 = true := by decide +kernel
def Line51Data : List Macro := [Line51m0,Line51m1,Line51m2,Line51m3,Line51m4,Line51m5,Line51m6,Line51m7]
theorem Line51_farAll : ∀ m ∈ Line51Data, farOK pts m := by
  intro m hm
  simp only [Line51Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line51m0_far,Line51m1_far,Line51m2_far,Line51m3_far,Line51m4_far,Line51m5_far,Line51m6_far,Line51m7_far]
theorem Line51_okAll : ∀ m ∈ Line51Data, axisOK pts m = true := by
  intro m hm
  simp only [Line51Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line51m0_ok,Line51m1_ok,Line51m2_ok,Line51m3_ok,Line51m4_ok,Line51m5_ok,Line51m6_ok,Line51m7_ok]
end CatalanCore.Cert.SigmaQuarter
