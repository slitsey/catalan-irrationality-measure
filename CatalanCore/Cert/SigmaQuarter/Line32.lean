module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line32m0 : Macro := { x0 := (968901001216), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7911395705374599892205293572),(4708199503284745038029586432),(4870254883988031602688),(0),(886973340089086509056),(4270290962909219)), boxes := [
    (((968884224000),(968917778432),(0),(0)),((645922816000),(645945185622),(-7297011532),(0)))
] }
theorem Line32m0_far : farOK pts Line32m0 := by decide +kernel
theorem Line32m0_ok : axisOK pts Line32m0 = true := by decide +kernel
def Line32m1 : Macro := { x0 := (968934555648), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7915994648747386531661394476),(4708062556005558268746530816),(4870398999176107458560),(0),(886973340089086509056),(4270034997348957)), boxes := [
    (((968917778432),(968951332864),(0),(0)),((645945185621),(645967555243),(-7297012882),(0)))
] }
theorem Line32m1_far : farOK pts Line32m1 := by decide +kernel
theorem Line32m1_ok : axisOK pts Line32m1 = true := by decide +kernel
def Line32m2 : Macro := { x0 := (968968110080), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7920595776448998817660225120),(4707925384611808999951106048),(4870543114364183314432),(0),(886973340089086509056),(4269778854086813)), boxes := [
    (((968951332864),(968984887296),(0),(0)),((645967555242),(645989924864),(-7297013910),(0)))
] }
theorem Line32m2_far : farOK pts Line32m2 := by decide +kernel
theorem Line32m2_ok : axisOK pts Line32m2 = true := by decide +kernel
def Line32m3 : Macro := { x0 := (969001664512), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7925192999024911655404479321),(4707788389506205512648294400),(4870687229552259170304),(0),(886973340089086509056),(4269522875433958)), boxes := [
    (((968984887296),(969018441728),(0),(0)),((645989924864),(646012294486),(-7297015109),(0)))
] }
theorem Line32m3_far : farOK pts Line32m3 := by decide +kernel
theorem Line32m3_ok : axisOK pts Line32m3 = true := by decide +kernel
def Line32m4 : Macro := { x0 := (969035218944), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7929795024074105931147470960),(4707651368741106403291955200),(4870831344740335026176),(0),(886973340089086509056),(4269266892693163)), boxes := [
    (((969018441728),(969051996160),(0),(0)),((646012294485),(646034664107),(-7297016495),(0)))
] }
theorem Line32m4_far : farOK pts Line32m4 := by decide +kernel
theorem Line32m4_ok : axisOK pts Line32m4 = true := by decide +kernel
def Line32m5 : Macro := { x0 := (969068773376), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7934393411360943090076379676),(4707514293754339289299484672),(4870975459928410882048),(0),(886973340089086509056),(4269010878495520)), boxes := [
    (((969051996160),(969085550592),(0),(0)),((646034664106),(646057033728),(-7297017784),(0)))
] }
theorem Line32m5_far : farOK pts Line32m5 := by decide +kernel
theorem Line32m5_ok : axisOK pts Line32m5 = true := by decide +kernel
def Line32m6 : Macro := { x0 := (969102327808), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7938992267293387878225877955),(4707377221639143122070929408),(4871119575116486737920),(0),(886973340089086509056),(4268754882076255)), boxes := [
    (((969085550592),(969119105024),(0),(0)),((646057033728),(646079403350),(-7297018720),(0)))
] }
theorem Line32m6_far : farOK pts Line32m6 := by decide +kernel
theorem Line32m6_ok : axisOK pts Line32m6 = true := by decide +kernel
def Line32m7 : Macro := { x0 := (969135882240), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7943593577859819339481518826),(4707240466691009944484118528),(4871263690304562593792),(0),(886973340089086509056),(4268499189949452)), boxes := [
    (((969119105024),(969152659456),(0),(0)),((646079403349),(646101772971),(-7297020015),(0)))
] }
theorem Line32m7_far : farOK pts Line32m7 := by decide +kernel
theorem Line32m7_ok : axisOK pts Line32m7 = true := by decide +kernel
def Line32Data : List Macro := [Line32m0,Line32m1,Line32m2,Line32m3,Line32m4,Line32m5,Line32m6,Line32m7]
theorem Line32_farAll : ∀ m ∈ Line32Data, farOK pts m := by
  intro m hm
  simp only [Line32Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line32m0_far,Line32m1_far,Line32m2_far,Line32m3_far,Line32m4_far,Line32m5_far,Line32m6_far,Line32m7_far]
theorem Line32_okAll : ∀ m ∈ Line32Data, axisOK pts m = true := by
  intro m hm
  simp only [Line32Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line32m0_ok,Line32m1_ok,Line32m2_ok,Line32m3_ok,Line32m4_ok,Line32m5_ok,Line32m6_ok,Line32m7_ok]
end CatalanCore.Cert.SigmaQuarter
