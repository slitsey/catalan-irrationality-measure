module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line39m0 : Macro := { x0 := (970780049408), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8168689175691450009912801770),(4700537749648844639297273856),(4878325334520279531520),(0),(886973340089086509056),(4255987995682765)), boxes := [
    (((970763272192),(970796826624),(0),(0)),((647175514794),(647197884416),(-7297039138),(0)))
] }
theorem Line39m0_far : farOK pts Line39m0 := by decide +kernel
theorem Line39m0_ok : axisOK pts Line39m0 = true := by decide +kernel
def Line39m1 : Macro := { x0 := (970813603840), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8173276088152001510696099492),(4700401154406595961503219712),(4878469449708355387392),(0),(886973340089086509056),(4255733237868582)), boxes := [
    (((970796826624),(970830381056),(0),(0)),((647197884416),(647220254038),(-7297038292),(0)))
] }
theorem Line39m1_far : farOK pts Line39m1 := by decide +kernel
theorem Line39m1_ok : axisOK pts Line39m1 = true := by decide +kernel
def Line39m2 : Macro := { x0 := (970847158272), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8177859521036305428596918662),(4700264494265380075261984768),(4878613564896431243264),(0),(886973340089086509056),(4255478439870602)), boxes := [
    (((970830381056),(970863935488),(0),(0)),((647220254037),(647242623659),(-7297037624),(0)))
] }
theorem Line39m2_far : farOK pts Line39m2 := by decide +kernel
theorem Line39m2_ok : axisOK pts Line39m2 = true := by decide +kernel
def Line39m3 : Macro := { x0 := (970880712704), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8182442207806035113231585180),(4700127961454851099748925440),(4878757680084507099136),(0),(886973340089086509056),(4255223760734960)), boxes := [
    (((970863935488),(970897489920),(0),(0)),((647242623658),(647264993280),(-7297036956),(0)))
] }
theorem Line39m3_far : farOK pts Line39m3 := by decide +kernel
theorem Line39m3_ok : axisOK pts Line39m3 = true := by decide +kernel
def Line39m4 : Macro := { x0 := (970914267136), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8187031109891735908721873003),(4699991579178699702865362944),(4878901795272582955008),(0),(886973340089086509056),(4254969238242125)), boxes := [
    (((970897489920),(970931044352),(0),(0)),((647264993280),(647287362902),(-7297036524),(0)))
] }
theorem Line39m4_far : farOK pts Line39m4 := by decide +kernel
theorem Line39m4_ok : axisOK pts Line39m4 = true := by decide +kernel
def Line39m5 : Macro := { x0 := (970947821568), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8191621842782165549680477704),(4699854935246860869765890048),(4879045910460658810880),(0),(886973340089086509056),(4254714506848029)), boxes := [
    (((970931044352),(970964598784),(0),(0)),((647287362901),(647309732523),(-7297035799),(0)))
] }
theorem Line39m5_far : farOK pts Line39m5 := by decide +kernel
theorem Line39m5_ok : axisOK pts Line39m5 = true := by decide +kernel
def Line39m6 : Macro := { x0 := (970981376000), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8196211759229683225494954991),(4699718445256947903588073472),(4879190025648734666752),(0),(886973340089086509056),(4254459916380602)), boxes := [
    (((970964598784),(970998153216),(0),(0)),((647309732522),(647332102144),(-7297035305),(0)))
] }
theorem Line39m6_far : farOK pts Line39m6 := by decide +kernel
theorem Line39m6_ok : axisOK pts Line39m6 = true := by decide +kernel
def Line39m7 : Macro := { x0 := (971014930432), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8200800568297154436563762922),(4699582148345219461856034816),(4879334140836810522624),(0),(886973340089086509056),(4254205513792040)), boxes := [
    (((970998153216),(971031707648),(0),(0)),((647332102144),(647354471766),(-7297034798),(0)))
] }
theorem Line39m7_far : farOK pts Line39m7 := by decide +kernel
theorem Line39m7_ok : axisOK pts Line39m7 = true := by decide +kernel
def Line39Data : List Macro := [Line39m0,Line39m1,Line39m2,Line39m3,Line39m4,Line39m5,Line39m6,Line39m7]
theorem Line39_farAll : ∀ m ∈ Line39Data, farOK pts m := by
  intro m hm
  simp only [Line39Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line39m0_far,Line39m1_far,Line39m2_far,Line39m3_far,Line39m4_far,Line39m5_far,Line39m6_far,Line39m7_far]
theorem Line39_okAll : ∀ m ∈ Line39Data, axisOK pts m = true := by
  intro m hm
  simp only [Line39Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line39m0_ok,Line39m1_ok,Line39m2_ok,Line39m3_ok,Line39m4_ok,Line39m5_ok,Line39m6_ok,Line39m7_ok]
end CatalanCore.Cert.SigmaQuarter
