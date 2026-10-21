module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line19m0 : Macro := { x0 := (964522147840), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7310252749250335921485668333),(4726151327387241302165815296),(4851447851944132411392),(0),(886973340089086509056),(4303904085928814)), boxes := [
    (((964488593408),(964555702272),(0),(0)),((642992395605),(643037134848),(-7296925965),(0)))
] }
theorem Line19m0_far : farOK pts Line19m0 := by decide +kernel
theorem Line19m0_ok : axisOK pts Line19m0 = true := by decide +kernel
def Line19m1 : Macro := { x0 := (964589256704), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7319485079188945474078337037),(4725875385531457480508702720),(4851736082320284123136),(0),(886973340089086509056),(4303386124474207)), boxes := [
    (((964555702272),(964622811136),(0),(0)),((643037134848),(643081874091),(-7296938842),(0)))
] }
theorem Line19m1_far : farOK pts Line19m1 := by decide +kernel
theorem Line19m1_ok : axisOK pts Line19m1 = true := by decide +kernel
def Line19m2 : Macro := { x0 := (964656365568), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7328704332535429194532832120),(4725599233269305426070470656),(4852024312696435834880),(0),(886973340089086509056),(4302868046459607)), boxes := [
    (((964622811136),(964689920000),(0),(0)),((643081874090),(643126613334),(-7296947728),(0)))
] }
theorem Line19m2_far : farOK pts Line19m2 := by decide +kernel
theorem Line19m2_ok : axisOK pts Line19m2 = true := by decide +kernel
def Line19m3 : Macro := { x0 := (964723474432), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7337921046144123020530721246),(4725323159039158986694459392),(4852312543072587546624),(0),(886973340089086509056),(4302350100642094)), boxes := [
    (((964689920000),(964757028864),(0),(0)),((643126613333),(643171352576),(-7296956800),(0)))
] }
theorem Line19m3_far : farOK pts Line19m3 := by decide +kernel
theorem Line19m3_ok : axisOK pts Line19m3 = true := by decide +kernel
def Line19m4 : Macro := { x0 := (964790583296), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7347152289154597246438037126),(4725047062170878168656576512),(4852600773448739258368),(0),(886973340089086509056),(4301832210480253)), boxes := [
    (((964757028864),(964824137728),(0),(0)),((643171352576),(643216091819),(-7296966029),(0)))
] }
theorem Line19m4_far : farOK pts Line19m4 := by decide +kernel
theorem Line19m4_ok : axisOK pts Line19m4 = true := by decide +kernel
def Line19m5 : Macro := { x0 := (964857692160), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7356384244361224711659712326),(4724771060601833642923393024),(4852889003824890970112),(0),(886973340089086509056),(4301314464064588)), boxes := [
    (((964824137728),(964891246592),(0),(0)),((643216091818),(643260831062),(-7296975544),(0)))
] }
theorem Line19m5_far : farOK pts Line19m5 := by decide +kernel
theorem Line19m5_ok : axisOK pts Line19m5 = true := by decide +kernel
def Line19m6 : Macro := { x0 := (964924801024), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7365622164727641506804596461),(4724494940122909660929064960),(4853177234201042681856),(0),(886973340089086509056),(4300796683127507)), boxes := [
    (((964891246592),(964958355456),(0),(0)),((643260831061),(643305570304),(-7296984935),(0)))
] }
theorem Line19m6_far : farOK pts Line19m6 := by decide +kernel
theorem Line19m6_ok : axisOK pts Line19m6 = true := by decide +kernel
def Line19m7 : Macro := { x0 := (964991909888), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7374851346866252494311662354),(4724219080931707104832913408),(4853465464577194393600),(0),(886973340089086509056),(4300279188792829)), boxes := [
    (((964958355456),(965025464320),(0),(0)),((643305570304),(643350309547),(-7296994283),(0)))
] }
theorem Line19m7_far : farOK pts Line19m7 := by decide +kernel
theorem Line19m7_ok : axisOK pts Line19m7 = true := by decide +kernel
def Line19Data : List Macro := [Line19m0,Line19m1,Line19m2,Line19m3,Line19m4,Line19m5,Line19m6,Line19m7]
theorem Line19_farAll : ∀ m ∈ Line19Data, farOK pts m := by
  intro m hm
  simp only [Line19Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line19m0_far,Line19m1_far,Line19m2_far,Line19m3_far,Line19m4_far,Line19m5_far,Line19m6_far,Line19m7_far]
theorem Line19_okAll : ∀ m ∈ Line19Data, axisOK pts m = true := by
  intro m hm
  simp only [Line19Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line19m0_ok,Line19m1_ok,Line19m2_ok,Line19m3_ok,Line19m4_ok,Line19m5_ok,Line19m6_ok,Line19m7_ok]
end CatalanCore.Cert.SigmaQuarter
