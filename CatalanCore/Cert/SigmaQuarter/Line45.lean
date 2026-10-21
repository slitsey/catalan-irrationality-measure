module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line45m0 : Macro := { x0 := (972390662144), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8388880056831835235685238672),(4693990547045753879763222528),(4885242863547920613376),(0),(886973340089086509056),(4243785811165935)), boxes := [
    (((972373884928),(972407439360),(0),(0)),((648249256618),(648271626240),(-7296986283),(0)))
] }
theorem Line45m0_far : farOK pts Line45m0 := by decide +kernel
theorem Line45m0_ok : axisOK pts Line45m0 = true := by decide +kernel
def Line45m1 : Macro := { x0 := (972424216576), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8393463885049050778707596974),(4693854397157155477099839488),(4885386978735996469248),(0),(886973340089086509056),(4243532202093716)), boxes := [
    (((972407439360),(972440993792),(0),(0)),((648271626240),(648293995862),(-7296984450),(0)))
] }
theorem Line45m1_far : farOK pts Line45m1 := by decide +kernel
theorem Line45m1_ok : axisOK pts Line45m1 = true := by decide +kernel
def Line45m2 : Macro := { x0 := (972457771008), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8398044243516638255677809142),(4693718009728995359299076096),(4885531093924072325120),(0),(886973340089086509056),(4243278394437686)), boxes := [
    (((972440993792),(972474548224),(0),(0)),((648293995861),(648316365483),(-7296982525),(0)))
] }
theorem Line45m2_far : farOK pts Line45m2 := by decide +kernel
theorem Line45m2_ok : axisOK pts Line45m2 = true := by decide +kernel
def Line45m3 : Macro := { x0 := (972491325440), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8402633671582908872322041228),(4693581818596120253757980672),(4885675209112148180992),(0),(886973340089086509056),(4243024795480088)), boxes := [
    (((972474548224),(972508102656),(0),(0)),((648316365482),(648338735104),(-7296984523),(0)))
] }
theorem Line45m3_far : farOK pts Line45m3 := by decide +kernel
theorem Line45m3_ok : axisOK pts Line45m3 = true := by decide +kernel
def Line45m4 : Macro := { x0 := (972524879872), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8407220270854522847740875198),(4693445713955186193979277312),(4885819324300224036864),(0),(886973340089086509056),(4242771284069865)), boxes := [
    (((972508102656),(972541657088),(0),(0)),((648338735104),(648361104726),(-7296982332),(0)))
] }
theorem Line45m4_far : farOK pts Line45m4 := by decide +kernel
theorem Line45m4_ok : axisOK pts Line45m4 = true := by decide +kernel
def Line45m5 : Macro := { x0 := (972558434304), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8411806511363678925880208841),(4693309460270699740718104576),(4885963439488299892736),(0),(886973340089086509056),(4242517651413424)), boxes := [
    (((972541657088),(972575211520),(0),(0)),((648361104725),(648383474347),(-7296980348),(0)))
] }
theorem Line45m5_far : farOK pts Line45m5 := by decide +kernel
theorem Line45m5_ok : axisOK pts Line45m5 = true := by decide +kernel
def Line45m6 : Macro := { x0 := (972591988736), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8416382781525319335421051020),(4693173445938059677643440128),(4886107554676375748608),(0),(886973340089086509056),(4242264248741852)), boxes := [
    (((972575211520),(972608765952),(0),(0)),((648383474346),(648405843968),(-7296978051),(0)))
] }
theorem Line45m6_far : farOK pts Line45m6 := by decide +kernel
theorem Line45m6_ok : axisOK pts Line45m6 = true := by decide +kernel
def Line45m7 : Macro := { x0 := (972625543168), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8420963283666315138659428701),(4693037061885331186276368384),(4886251669864451604480),(0),(886973340089086509056),(4242010531666847)), boxes := [
    (((972608765952),(972642320384),(0),(0)),((648405843968),(648428213590),(-7296975922),(0)))
] }
theorem Line45m7_far : farOK pts Line45m7 := by decide +kernel
theorem Line45m7_ok : axisOK pts Line45m7 = true := by decide +kernel
def Line45Data : List Macro := [Line45m0,Line45m1,Line45m2,Line45m3,Line45m4,Line45m5,Line45m6,Line45m7]
theorem Line45_farAll : ∀ m ∈ Line45Data, farOK pts m := by
  intro m hm
  simp only [Line45Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line45m0_far,Line45m1_far,Line45m2_far,Line45m3_far,Line45m4_far,Line45m5_far,Line45m6_far,Line45m7_far]
theorem Line45_okAll : ∀ m ∈ Line45Data, axisOK pts m = true := by
  intro m hm
  simp only [Line45Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line45m0_ok,Line45m1_ok,Line45m2_ok,Line45m3_ok,Line45m4_ok,Line45m5_ok,Line45m6_ok,Line45m7_ok]
end CatalanCore.Cert.SigmaQuarter
