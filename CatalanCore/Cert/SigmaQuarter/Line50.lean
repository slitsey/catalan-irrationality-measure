module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line50m0 : Macro := { x0 := (973732839424), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8572128204893774369850653089),(4688548225724382296486641664),(4891007471070954848256),(0),(886973340089086509056),(4233657292299316)), boxes := [
    (((973716062208),(973749616640),(0),(0)),((649144041472),(649166411094),(-7296892012),(0)))
] }
theorem Line50m0_far : farOK pts Line50m0 := by decide +kernel
theorem Line50m0_ok : axisOK pts Line50m0 = true := by decide +kernel
def Line50m1 : Macro := { x0 := (973766393856), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8576704073850202391398417754),(4688412355911007922581012480),(4891151586259030704128),(0),(886973340089086509056),(4233404576647371)), boxes := [
    (((973749616640),(973783171072),(0),(0)),((649166411093),(649188780715),(-7296889019),(0)))
] }
theorem Line50m1_far : farOK pts Line50m1 := by decide +kernel
theorem Line50m1_ok : axisOK pts Line50m1 = true := by decide +kernel
def Line50m2 : Macro := { x0 := (973799948288), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8581282996525142998635152674),(4688276434420119666923798528),(4891295701447106560000),(0),(886973340089086509056),(4233151817093739)), boxes := [
    (((973783171072),(973816725504),(0),(0)),((649188780714),(649211150336),(-7296886154),(0)))
] }
theorem Line50m2_far : farOK pts Line50m2 := by decide +kernel
theorem Line50m2_ok : axisOK pts Line50m2 = true := by decide +kernel
def Line50m3 : Macro := { x0 := (973833502720), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8585866494613292054040647711),(4688140594518929341947445248),(4891439816635182415872),(0),(886973340089086509056),(4232899154741321)), boxes := [
    (((973816725504),(973850279936),(0),(0)),((649211150336),(649233519958),(-7296887169),(0)))
] }
theorem Line50m3_far : farOK pts Line50m3 := by decide +kernel
theorem Line50m3_ok : axisOK pts Line50m3 = true := by decide +kernel
def Line50m4 : Macro := { x0 := (973867057152), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8590442804541658262996187001),(4688004808819413952651853824),(4891583931823258271744),(0),(886973340089086509056),(4232646548074181)), boxes := [
    (((973850279936),(973883834368),(0),(0)),((649233519957),(649255889579),(-7296883602),(0)))
] }
theorem Line50m4_far : farOK pts Line50m4 := by decide +kernel
theorem Line50m4_ok : axisOK pts Line50m4 = true := by decide +kernel
def Line50m5 : Macro := { x0 := (973900611584), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8595024304061041136093449098),(4687868847592981053203939328),(4891728047011334127616),(0),(886973340089086509056),(4232393814057813)), boxes := [
    (((973883834368),(973917388800),(0),(0)),((649255889578),(649278259200),(-7296880564),(0)))
] }
theorem Line50m5_far : farOK pts Line50m5 := by decide +kernel
theorem Line50m5_ok : axisOK pts Line50m5 = true := by decide +kernel
def Line50m6 : Macro := { x0 := (973934166016), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8599597562624129645892025647),(4687732908339402686147919872),(4891872162199409983488),(0),(886973340089086509056),(4232141103952544)), boxes := [
    (((973917388800),(973950943232),(0),(0)),((649278259200),(649300628822),(-7296877273),(0)))
] }
theorem Line50m6_far : farOK pts Line50m6 := by decide +kernel
theorem Line50m6_ok : axisOK pts Line50m6 = true := by decide +kernel
def Line50m7 : Macro := { x0 := (973967720448), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8604180025583999235727868136),(4687597027815270202205405184),(4892016277387485839360),(0),(886973340089086509056),(4231888463380480)), boxes := [
    (((973950943232),(973984497664),(0),(0)),((649300628821),(649322998443),(-7296874318),(0)))
] }
theorem Line50m7_far : farOK pts Line50m7 := by decide +kernel
theorem Line50m7_ok : axisOK pts Line50m7 = true := by decide +kernel
def Line50Data : List Macro := [Line50m0,Line50m1,Line50m2,Line50m3,Line50m4,Line50m5,Line50m6,Line50m7]
theorem Line50_farAll : ∀ m ∈ Line50Data, farOK pts m := by
  intro m hm
  simp only [Line50Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line50m0_far,Line50m1_far,Line50m2_far,Line50m3_far,Line50m4_far,Line50m5_far,Line50m6_far,Line50m7_far]
theorem Line50_okAll : ∀ m ∈ Line50Data, axisOK pts m = true := by
  intro m hm
  simp only [Line50Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line50m0_ok,Line50m1_ok,Line50m2_ok,Line50m3_ok,Line50m4_ok,Line50m5_ok,Line50m6_ok,Line50m7_ok]
end CatalanCore.Cert.SigmaQuarter
