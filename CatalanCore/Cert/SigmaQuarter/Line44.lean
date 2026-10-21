module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line44m0 : Macro := { x0 := (972122226688), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8352200177313143365402842550),(4695080400673434597674975232),(4884089942043313766400),(0),(886973340089086509056),(4245815769328963)), boxes := [
    (((972105449472),(972139003904),(0),(0)),((648070299648),(648092669270),(-7297002148),(0)))
] }
theorem Line44m0_far : farOK pts Line44m0 := by decide +kernel
theorem Line44m0_ok : axisOK pts Line44m0 = true := by decide +kernel
def Line44m1 : Macro := { x0 := (972155781120), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8356789351841199700879385738),(4694944130361177202194055168),(4884234057231389622272),(0),(886973340089086509056),(4245561926640380)), boxes := [
    (((972139003904),(972172558336),(0),(0)),((648092669269),(648115038891),(-7297000784),(0)))
] }
theorem Line44m1_far : farOK pts Line44m1 := by decide +kernel
theorem Line44m1_ok : axisOK pts Line44m1 = true := by decide +kernel
def Line44m2 : Macro := { x0 := (972189335552), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8361379419074100582350231121),(4694807816501350919705329664),(4884378172419465478144),(0),(886973340089086509056),(4245308073206360)), boxes := [
    (((972172558336),(972206112768),(0),(0)),((648115038890),(648137408512),(-7296999476),(0)))
] }
theorem Line44m2_far : farOK pts Line44m2 := by decide +kernel
theorem Line44m2_ok : axisOK pts Line44m2 = true := by decide +kernel
def Line44m3 : Macro := { x0 := (972222889984), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8365961134391594016402244258),(4694671559913764294431342592),(4884522287607541334016),(0),(886973340089086509056),(4245054283722531)), boxes := [
    (((972206112768),(972239667200),(0),(0)),((648137408512),(648159778134),(-7296997909),(0)))
] }
theorem Line44m3_far : farOK pts Line44m3 := by decide +kernel
theorem Line44m3_ok : axisOK pts Line44m3 = true := by decide +kernel
def Line44m4 : Macro := { x0 := (972256444416), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8370547940351125719396806152),(4694535446282191933599121408),(4884666402795617189888),(0),(886973340089086509056),(4244800627318305)), boxes := [
    (((972239667200),(972273221632),(0),(0)),((648159778133),(648182147755),(-7296996103),(0)))
] }
theorem Line44m4_far : farOK pts Line44m4 := by decide +kernel
theorem Line44m4_ok : axisOK pts Line44m4 = true := by decide +kernel
def Line44m5 : Macro := { x0 := (972289998848), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8375131384074027048296308631),(4694399137357961595398717440),(4884810517983693045760),(0),(886973340089086509056),(4244546827021494)), boxes := [
    (((972273221632),(972306776064),(0),(0)),((648182147754),(648204517376),(-7296994496),(0)))
] }
theorem Line44m5_far : farOK pts Line44m5 := by decide +kernel
theorem Line44m5_ok : axisOK pts Line44m5 = true := by decide +kernel
def Line44m6 : Macro := { x0 := (972323553280), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8379708507784423221372034932),(4694262814402564705024737280),(4884954633171768901632),(0),(886973340089086509056),(4244293022380238)), boxes := [
    (((972306776064),(972340330496),(0),(0)),((648204517376),(648226886998),(-7296992700),(0)))
] }
theorem Line44m6_far : farOK pts Line44m6 := by decide +kernel
theorem Line44m6_ok : axisOK pts Line44m6 = true := by decide +kernel
def Line44m7 : Macro := { x0 := (972357107712), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8384294713320556577437006360),(4694126736417694131372032000),(4885098748359844757504),(0),(886973340089086509056),(4244039453181941)), boxes := [
    (((972340330496),(972373884928),(0),(0)),((648226886997),(648249256619),(-7296988331),(0)))
] }
theorem Line44m7_far : farOK pts Line44m7 := by decide +kernel
theorem Line44m7_ok : axisOK pts Line44m7 = true := by decide +kernel
def Line44Data : List Macro := [Line44m0,Line44m1,Line44m2,Line44m3,Line44m4,Line44m5,Line44m6,Line44m7]
theorem Line44_farAll : ∀ m ∈ Line44Data, farOK pts m := by
  intro m hm
  simp only [Line44Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line44m0_far,Line44m1_far,Line44m2_far,Line44m3_far,Line44m4_far,Line44m5_far,Line44m6_far,Line44m7_far]
theorem Line44_okAll : ∀ m ∈ Line44Data, axisOK pts m = true := by
  intro m hm
  simp only [Line44Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line44m0_ok,Line44m1_ok,Line44m2_ok,Line44m3_ok,Line44m4_ok,Line44m5_ok,Line44m6_ok,Line44m7_ok]
end CatalanCore.Cert.SigmaQuarter
