module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line11m0 : Macro := { x0 := (958381686784), y0 := (0), i0 := 1200, i1 := 1200, fd := ((6463367194822894675979260282),(4751557752916126769261969408),(4825074772526250786816),(0),(886973340089086509056),(4351715511189170)), boxes := [
    (((958314577920),(958448795648),(0),(0)),((638876385280),(638965863766),(-7296178717),(0)))
] }
theorem Line11m0_far : farOK pts Line11m0 := by decide +kernel
theorem Line11m0_ok : axisOK pts Line11m0 = true := by decide +kernel
def Line11m1 : Macro := { x0 := (958515904512), y0 := (0), i0 := 1200, i1 := 1200, fd := ((6481924465282005997979423472),(4750999543407037179490598912),(4825651233278554210304),(0),(886973340089086509056),(4350661958548705)), boxes := [
    (((958448795648),(958583013376),(0),(0)),((638965863765),(639055342251),(-7296223111),(0)))
] }
theorem Line11m1_far : farOK pts Line11m1 := by decide +kernel
theorem Line11m1_ok : axisOK pts Line11m1 = true := by decide +kernel
def Line11m2 : Macro := { x0 := (958650122240), y0 := (0), i0 := 1200, i1 := 1200, fd := ((6500478594003399574478015450),(4750441339610878994094489600),(4826227694030857633792),(0),(886973340089086509056),(4349608678134103)), boxes := [
    (((958583013376),(958717231104),(0),(0)),((639055342250),(639144820736),(-7296262727),(0)))
] }
theorem Line11m2_far : farOK pts Line11m2 := by decide +kernel
theorem Line11m2_ok : axisOK pts Line11m2 = true := by decide +kernel
def Line11m3 : Macro := { x0 := (958784339968), y0 := (0), i0 := 1200, i1 := 1200, fd := ((6519032446168687609982234550),(4749883382901213859177627648),(4826804154783161057280),(0),(886973340089086509056),(4348555880392084)), boxes := [
    (((958717231104),(958851448832),(0),(0)),((639144820736),(639234299222),(-7296303955),(0)))
] }
theorem Line11m3_far : farOK pts Line11m3 := by decide +kernel
theorem Line11m3_ok : axisOK pts Line11m3 = true := by decide +kernel
def Line11m4 : Macro := { x0 := (958918557696), y0 := (0), i0 := 1200, i1 := 1200, fd := ((6537588238379765213116455365),(4749325373787149874380668928),(4827380615535464480768),(0),(886973340089086509056),(4347503314191776)), boxes := [
    (((958851448832),(958985666560),(0),(0)),((639234299221),(639323777707),(-7296341864),(0)))
] }
theorem Line11m4_far : farOK pts Line11m4 := by decide +kernel
theorem Line11m4_ok : axisOK pts Line11m4 = true := by decide +kernel
def Line11m5 : Macro := { x0 := (959052775424), y0 := (0), i0 := 1200, i1 := 1200, fd := ((6556131478875271910768732670),(4748767751052019083163205632),(4827957076287767904256),(0),(886973340089086509056),(4346451350931387)), boxes := [
    (((958985666560),(959119884288),(0),(0)),((639323777706),(639413256192),(-7296380409),(0)))
] }
theorem Line11m5_far : farOK pts Line11m5 := by decide +kernel
theorem Line11m5_ok : axisOK pts Line11m5 = true := by decide +kernel
def Line11m6 : Macro := { x0 := (959186993152), y0 := (0), i0 := 1200, i1 := 1200, fd := ((6574684373734486043596740814),(4748210214136138778932609024),(4828533537040071327744),(0),(886973340089086509056),(4345399733598880)), boxes := [
    (((959119884288),(959254102016),(0),(0)),((639413256192),(639502734678),(-7296417943),(0)))
] }
theorem Line11m6_far : farOK pts Line11m6 := by decide +kernel
theorem Line11m6_ok : axisOK pts Line11m6 = true := by decide +kernel
def Line11m7 : Macro := { x0 := (959321210880), y0 := (0), i0 := 1200, i1 := 1200, fd := ((6593233784448368500316126117),(4747652716872598563191586816),(4829109997792374751232),(0),(886973340089086509056),(4344348415823406)), boxes := [
    (((959254102016),(959388319744),(0),(0)),((639502734677),(639592213163),(-7296456469),(0)))
] }
theorem Line11m7_far : farOK pts Line11m7 := by decide +kernel
theorem Line11m7_ok : axisOK pts Line11m7 = true := by decide +kernel
def Line11Data : List Macro := [Line11m0,Line11m1,Line11m2,Line11m3,Line11m4,Line11m5,Line11m6,Line11m7]
theorem Line11_farAll : ∀ m ∈ Line11Data, farOK pts m := by
  intro m hm
  simp only [Line11Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line11m0_far,Line11m1_far,Line11m2_far,Line11m3_far,Line11m4_far,Line11m5_far,Line11m6_far,Line11m7_far]
theorem Line11_okAll : ∀ m ∈ Line11Data, axisOK pts m = true := by
  intro m hm
  simp only [Line11Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line11m0_ok,Line11m1_ok,Line11m2_ok,Line11m3_ok,Line11m4_ok,Line11m5_ok,Line11m6_ok,Line11m7_ok]
end CatalanCore.Cert.SigmaQuarter
