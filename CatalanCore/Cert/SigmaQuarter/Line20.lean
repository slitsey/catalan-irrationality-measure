module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line20m0 : Macro := { x0 := (965059018752), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7384077156037157814988950797),(4723943178249476046486634496),(4853753694953346105344),(0),(886973340089086509056),(4299761728661702)), boxes := [
    (((965025464320),(965092573184),(0),(0)),((643350309546),(643395048790),(-7297003201),(0)))
] }
theorem Line20m0_far : farOK pts Line20m0 := by decide +kernel
theorem Line20m0_ok : axisOK pts Line20m0 = true := by decide +kernel
def Line20m1 : Macro := { x0 := (965126127616), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7393297632579453330372791539),(4723667273897959143204913152),(4854041925329497817088),(0),(886973340089086509056),(4299244324961016)), boxes := [
    (((965092573184),(965159682048),(0),(0)),((643395048789),(643439788032),(-7297012179),(0)))
] }
theorem Line20m1_far : farOK pts Line20m1 := by decide +kernel
theorem Line20m1_ok : axisOK pts Line20m1 = true := by decide +kernel
def Line20m2 : Macro := { x0 := (965193236480), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7402528771724244246649469024),(4723391281329155892170194944),(4854330155705649528832),(0),(886973340089086509056),(4298726914528129)), boxes := [
    (((965159682048),(965226790912),(0),(0)),((643439788032),(643484527275),(-7297021215),(0)))
] }
theorem Line20m2_far : farOK pts Line20m2 := by decide +kernel
theorem Line20m2_ok : axisOK pts Line20m2 = true := by decide +kernel
def Line20m3 : Macro := { x0 := (965260345344), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7411760667483043915236083226),(4723115466192522483617431552),(4854618386081801240576),(0),(886973340089086509056),(4298209715130370)), boxes := [
    (((965226790912),(965293899776),(0),(0)),((643484527274),(643529266518),(-7297030506),(0)))
] }
theorem Line20m3_far : farOK pts Line20m3 := by decide +kernel
theorem Line20m3_ok : axisOK pts Line20m3 = true := by decide +kernel
def Line20m4 : Macro := { x0 := (965327454208), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7420986890768627856375313106),(4722839626544959822358642688),(4854906616457952952320),(0),(886973340089086509056),(4297692569649080)), boxes := [
    (((965293899776),(965361008640),(0),(0)),((643529266517),(643574005760),(-7297039313),(0)))
] }
theorem Line20m4_far : farOK pts Line20m4 := by decide +kernel
theorem Line20m4_ok : axisOK pts Line20m4 = true := by decide +kernel
def Line20m5 : Macro := { x0 := (965394563072), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7430206986705795623105158677),(4722563924585001086365335552),(4855194846834104664064),(0),(886973340089086509056),(4297175612238068)), boxes := [
    (((965361008640),(965428117504),(0),(0)),((643574005760),(643618745003),(-7297048129),(0)))
] }
theorem Line20m5_far : farOK pts Line20m5 := by decide +kernel
theorem Line20m5_ok : axisOK pts Line20m5 = true := by decide +kernel
def Line20m6 : Macro := { x0 := (965461671936), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7439428018694089530578859784),(4722288248619327638558736384),(4855483077210256375808),(0),(886973340089086509056),(4296658742394097)), boxes := [
    (((965428117504),(965495226368),(0),(0)),((643618745002),(643663484246),(-7297056697),(0)))
] }
theorem Line20m6_far : farOK pts Line20m6 := by decide +kernel
theorem Line20m6_ok : axisOK pts Line20m6 = true := by decide +kernel
def Line20m7 : Macro := { x0 := (965528780800), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7448647622296950173391837052),(4722012491684059318104293376),(4855771307586408087552),(0),(886973340089086509056),(4296141863642935)), boxes := [
    (((965495226368),(965562335232),(0),(0)),((643663484245),(643708223488),(-7297062482),(0)))
] }
theorem Line20m7_far : farOK pts Line20m7 := by decide +kernel
theorem Line20m7_ok : axisOK pts Line20m7 = true := by decide +kernel
def Line20Data : List Macro := [Line20m0,Line20m1,Line20m2,Line20m3,Line20m4,Line20m5,Line20m6,Line20m7]
theorem Line20_farAll : ∀ m ∈ Line20Data, farOK pts m := by
  intro m hm
  simp only [Line20Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line20m0_far,Line20m1_far,Line20m2_far,Line20m3_far,Line20m4_far,Line20m5_far,Line20m6_far,Line20m7_far]
theorem Line20_okAll : ∀ m ∈ Line20Data, axisOK pts m = true := by
  intro m hm
  simp only [Line20Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line20m0_ok,Line20m1_ok,Line20m2_ok,Line20m3_ok,Line20m4_ok,Line20m5_ok,Line20m6_ok,Line20m7_ok]
end CatalanCore.Cert.SigmaQuarter
