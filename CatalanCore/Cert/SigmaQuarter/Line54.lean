module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line54m0 : Macro := { x0 := (975125348352), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8762012835007631338742255647),(4682915260846584295304003584),(4896988251376102866944),(0),(886973340089086509056),(4223187494433305)), boxes := [
    (((975091793920),(975158902784),(0),(0)),((650061195946),(650105935190),(-7297075228),(0)))
] }
theorem Line54m0_far : farOK pts Line54m0 := by decide +kernel
theorem Line54m0_ok : axisOK pts Line54m0 = true := by decide +kernel
def Line54m1 : Macro := { x0 := (975192457216), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8771164054678043668331752502),(4682644250334099630400733184),(4897276481752254578688),(0),(886973340089086509056),(4222684000684112)), boxes := [
    (((975158902784),(975226011648),(0),(0)),((650105935189),(650150674432),(-7297066987),(0)))
] }
theorem Line54m1_far : farOK pts Line54m1 := by decide +kernel
theorem Line54m1_ok : axisOK pts Line54m1 = true := by decide +kernel
def Line54m2 : Macro := { x0 := (975259566080), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8780315519600401654360476590),(4682373152295398042337411072),(4897564712128406290432),(0),(886973340089086509056),(4222180503850446)), boxes := [
    (((975226011648),(975293120512),(0),(0)),((650150674432),(650195413675),(-7297062534),(0)))
] }
theorem Line54m2_far : farOK pts Line54m2 := by decide +kernel
theorem Line54m2_ok : axisOK pts Line54m2 = true := by decide +kernel
def Line54m3 : Macro := { x0 := (975326674944), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8789455504971304777818647985),(4682101904028335306856988672),(4897852942504558002176),(0),(886973340089086509056),(4221676947106026)), boxes := [
    (((975293120512),(975360229376),(0),(0)),((650195413674),(650240152918),(-7297050348),(0)))
] }
theorem Line54m3_far : farOK pts Line54m3 := by decide +kernel
theorem Line54m3_ok : axisOK pts Line54m3 = true := by decide +kernel
def Line54m4 : Macro := { x0 := (975393783808), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8798601938398499349334121984),(4681830957144144400462905344),(4898141172880709713920),(0),(886973340089086509056),(4221173707433522)), boxes := [
    (((975360229376),(975427338240),(0),(0)),((650240152917),(650284892160),(-7297041436),(0)))
] }
theorem Line54m4_far : farOK pts Line54m4 := by decide +kernel
theorem Line54m4_ok : axisOK pts Line54m4 = true := by decide +kernel
def Line54m5 : Macro := { x0 := (975460892672), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8807750314209632238276637999),(4681559863286546228066648064),(4898429403256861425664),(0),(886973340089086509056),(4220670408838017)), boxes := [
    (((975427338240),(975494447104),(0),(0)),((650284892160),(650329631403),(-7297032262),(0)))
] }
theorem Line54m5_far : farOK pts Line54m5 := by decide +kernel
theorem Line54m5_ok : axisOK pts Line54m5 = true := by decide +kernel
def Line54m6 : Macro := { x0 := (975528001536), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8816890024943562732200998833),(4681289092631682042707574784),(4898717633633013137408),(0),(886973340089086509056),(4220167442738814)), boxes := [
    (((975494447104),(975561555968),(0),(0)),((650329631402),(650374370646),(-7297025859),(0)))
] }
theorem Line54m6_far : farOK pts Line54m6 := by decide +kernel
theorem Line54m6_ok : axisOK pts Line54m6 = true := by decide +kernel
def Line54m7 : Macro := { x0 := (975595110400), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8826040608019966832734373316),(4681017992639715524324753408),(4899005864009164849152),(0),(886973340089086509056),(4219664256474795)), boxes := [
    (((975561555968),(975628664832),(0),(0)),((650374370645),(650419109888),(-7297016393),(0)))
] }
theorem Line54m7_far : farOK pts Line54m7 := by decide +kernel
theorem Line54m7_ok : axisOK pts Line54m7 = true := by decide +kernel
def Line54Data : List Macro := [Line54m0,Line54m1,Line54m2,Line54m3,Line54m4,Line54m5,Line54m6,Line54m7]
theorem Line54_farAll : ∀ m ∈ Line54Data, farOK pts m := by
  intro m hm
  simp only [Line54Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line54m0_far,Line54m1_far,Line54m2_far,Line54m3_far,Line54m4_far,Line54m5_far,Line54m6_far,Line54m7_far]
theorem Line54_okAll : ∀ m ∈ Line54Data, axisOK pts m = true := by
  intro m hm
  simp only [Line54Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line54m0_ok,Line54m1_ok,Line54m2_ok,Line54m3_ok,Line54m4_ok,Line54m5_ok,Line54m6_ok,Line54m7_ok]
end CatalanCore.Cert.SigmaQuarter
