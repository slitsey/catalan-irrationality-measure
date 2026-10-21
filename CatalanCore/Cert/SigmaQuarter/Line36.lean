module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line36m0 : Macro := { x0 := (969974743040), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8058480082760069723297668882),(4703818303887732176758374400),(4874866570006458990592),(0),(886973340089086509056),(4262108992220079)), boxes := [
    (((969957965824),(969991520256),(0),(0)),((646638643882),(646661013504),(-7297040186),(0)))
] }
theorem Line36m0_far : farOK pts Line36m0 := by decide +kernel
theorem Line36m0_ok : axisOK pts Line36m0 = true := by decide +kernel
def Line36m1 : Macro := { x0 := (970008297472), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8063075124762683689278309620),(4703681703626352542710628352),(4875010685194534846464),(0),(886973340089086509056),(4261853846463347)), boxes := [
    (((969991520256),(970025074688),(0),(0)),((646661013504),(646683383126),(-7297040514),(0)))
] }
theorem Line36m1_far : farOK pts Line36m1 := by decide +kernel
theorem Line36m1_ok : axisOK pts Line36m1 = true := by decide +kernel
def Line36m2 : Macro := { x0 := (970041851904), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8067672544406825889090965630),(4703544640991007127676846080),(4875154800382610702336),(0),(886973340089086509056),(4261598313815705)), boxes := [
    (((970025074688),(970058629120),(0),(0)),((646683383125),(646705752747),(-7297040947),(0)))
] }
theorem Line36m2_far : farOK pts Line36m2 := by decide +kernel
theorem Line36m2_ok : axisOK pts Line36m2 = true := by decide +kernel
def Line36m3 : Macro := { x0 := (970075406336), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8072271085691007434931289833),(4703408004768220040794079232),(4875298915570686558208),(0),(886973340089086509056),(4261343171972411)), boxes := [
    (((970058629120),(970092183552),(0),(0)),((646705752746),(646728122368),(-7297041133),(0)))
] }
theorem Line36m3_far : farOK pts Line36m3 := by decide +kernel
theorem Line36m3_ok : axisOK pts Line36m3 = true := by decide +kernel
def Line36m4 : Macro := { x0 := (970108960768), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8076868473964898967833009082),(4703271278417711026865504256),(4875443030758762414080),(0),(886973340089086509056),(4261087954852615)), boxes := [
    (((970092183552),(970125737984),(0),(0)),((646728122368),(646750491990),(-7297041471),(0)))
] }
theorem Line36m4_far : farOK pts Line36m4 := by decide +kernel
theorem Line36m4_ok : axisOK pts Line36m4 = true := by decide +kernel
def Line36m5 : Macro := { x0 := (970142515200), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8081463402736850606395207037),(4703134555207650143711133696),(4875587145946838269952),(0),(886973340089086509056),(4260832762100427)), boxes := [
    (((970125737984),(970159292416),(0),(0)),((646750491989),(646772861611),(-7297041750),(0)))
] }
theorem Line36m5_far : farOK pts Line36m5 := by decide +kernel
theorem Line36m5_ok : axisOK pts Line36m5 = true := by decide +kernel
def Line36m6 : Macro := { x0 := (970176069632), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8086050689488076395394547100),(4702997659063363763100319744),(4875731261134914125824),(0),(886973340089086509056),(4260577431058834)), boxes := [
    (((970159292416),(970192846848),(0),(0)),((646772861610),(646795231232),(-7297041795),(0)))
] }
theorem Line36m6_far : farOK pts Line36m6 := by decide +kernel
theorem Line36m6_ok : axisOK pts Line36m6 = true := by decide +kernel
def Line36m7 : Macro := { x0 := (970209624064), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8090636337219941293730735550),(4702861027917506114465366016),(4875875376322989981696),(0),(886973340089086509056),(4260322363769057)), boxes := [
    (((970192846848),(970226401280),(0),(0)),((646795231232),(646817600854),(-7297041809),(0)))
] }
theorem Line36m7_far : farOK pts Line36m7 := by decide +kernel
theorem Line36m7_ok : axisOK pts Line36m7 = true := by decide +kernel
def Line36Data : List Macro := [Line36m0,Line36m1,Line36m2,Line36m3,Line36m4,Line36m5,Line36m6,Line36m7]
theorem Line36_farAll : ∀ m ∈ Line36Data, farOK pts m := by
  intro m hm
  simp only [Line36Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line36m0_far,Line36m1_far,Line36m2_far,Line36m3_far,Line36m4_far,Line36m5_far,Line36m6_far,Line36m7_far]
theorem Line36_okAll : ∀ m ∈ Line36Data, axisOK pts m = true := by
  intro m hm
  simp only [Line36Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line36m0_ok,Line36m1_ok,Line36m2_ok,Line36m3_ok,Line36m4_ok,Line36m5_ok,Line36m6_ok,Line36m7_ok]
end CatalanCore.Cert.SigmaQuarter
