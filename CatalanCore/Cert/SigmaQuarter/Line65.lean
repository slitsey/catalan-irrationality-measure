module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line65m0 : Macro := { x0 := (983681728512), y0 := (0), i0 := 1200, i1 := 1200, fd := ((9923900350265478556514296719),(4648598486441187699145375744),(4933737624335446114304),(0),(886973340089086509056),(4159702713781796)), boxes := [
    (((983547510784),(983815946240),(0),(0)),((655698340522),(655877297494),(-7297016610),(0)))
] }
theorem Line65m0_far : farOK pts Line65m0 := by decide +kernel
theorem Line65m0_ok : axisOK pts Line65m0 = true := by decide +kernel
def Line65m1 : Macro := { x0 := (983950163968), y0 := (0), i0 := 1200, i1 := 1200, fd := ((9960225834503204161917500805),(4647529949939585029740429312),(4934890545840052961280),(0),(886973340089086509056),(4157734280621022)), boxes := [
    (((983815946240),(984084381696),(0),(0)),((655877297493),(656056254464),(-7296920743),(0)))
] }
theorem Line65m1_far : farOK pts Line65m1 := by decide +kernel
theorem Line65m1_ok : axisOK pts Line65m1 = true := by decide +kernel
def Line65m2 : Macro := { x0 := (984218599424), y0 := (0), i0 := 1200, i1 := 1200, fd := ((9996533211558508529188263401),(4646461914793484043213733888),(4936043467344659808256),(0),(886973340089086509056),(4155767236734902)), boxes := [
    (((984084381696),(984352817152),(0),(0)),((656056254464),(656235211435),(-7296821414),(0)))
] }
theorem Line65m2_far : farOK pts Line65m2 := by decide +kernel
theorem Line65m2_ok : axisOK pts Line65m2 = true := by decide +kernel
def Line65m3 : Macro := { x0 := (984487034880), y0 := (0), i0 := 1200, i1 := 1200, fd := ((10032829788690478210594938686),(4645394565951647186700926976),(4937196388849266655232),(0),(886973340089086509056),(4153801774914860)), boxes := [
    (((984352817152),(984621252608),(0),(0)),((656235211434),(656414168406),(-7296719858),(0)))
] }
theorem Line65m3_far : farOK pts Line65m3 := by decide +kernel
theorem Line65m3_ok : axisOK pts Line65m3 = true := by decide +kernel
def Line65m4 : Macro := { x0 := (984755470336), y0 := (0), i0 := 1200, i1 := 1200, fd := ((10069111533478147400093619415),(4644327693725877106020253696),(4938349310353873502208),(0),(886973340089086509056),(4151837708017030)), boxes := [
    (((984621252608),(984889688064),(0),(0)),((656414168405),(656593125376),(-7296617512),(0)))
] }
theorem Line65m4_far : farOK pts Line65m4 := by decide +kernel
theorem Line65m4_ok : axisOK pts Line65m4 = true := by decide +kernel
def Line65m5 : Macro := { x0 := (985023905792), y0 := (0), i0 := 1200, i1 := 1200, fd := ((10105382733980987278308694957),(4643260974811263416927584256),(4939502231858480349184),(0),(886973340089086509056),(4149874735465380)), boxes := [
    (((984889688064),(985158123520),(0),(0)),((656593125376),(656772082347),(-7296515933),(0)))
] }
theorem Line65m5_far : farOK pts Line65m5 := by decide +kernel
theorem Line65m5_ok : axisOK pts Line65m5 = true := by decide +kernel
def Line65m6 : Macro := { x0 := (985292341248), y0 := (0), i0 := 1200, i1 := 1200, fd := ((10141658378223108319598926017),(4642194948715150127659220992),(4940655153363087196160),(0),(886973340089086509056),(4147913338117051)), boxes := [
    (((985158123520),(985426558976),(0),(0)),((656772082346),(656951039318),(-7296408557),(0)))
] }
theorem Line65m6_far : farOK pts Line65m6 := by decide +kernel
theorem Line65m6_ok : axisOK pts Line65m6 = true := by decide +kernel
def Line65m7 : Macro := { x0 := (985560776704), y0 := (0), i0 := 1200, i1 := 1200, fd := ((10177913505319282210238992384),(4641129635684375188674969600),(4941808074867694043136),(0),(886973340089086509056),(4145953533640325)), boxes := [
    (((985426558976),(985694994432),(0),(0)),((656951039317),(657129996288),(-7296298830),(0)))
] }
theorem Line65m7_far : farOK pts Line65m7 := by decide +kernel
theorem Line65m7_ok : axisOK pts Line65m7 = true := by decide +kernel
def Line65Data : List Macro := [Line65m0,Line65m1,Line65m2,Line65m3,Line65m4,Line65m5,Line65m6,Line65m7]
theorem Line65_farAll : ∀ m ∈ Line65Data, farOK pts m := by
  intro m hm
  simp only [Line65Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line65m0_far,Line65m1_far,Line65m2_far,Line65m3_far,Line65m4_far,Line65m5_far,Line65m6_far,Line65m7_far]
theorem Line65_okAll : ∀ m ∈ Line65Data, axisOK pts m = true := by
  intro m hm
  simp only [Line65Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line65m0_ok,Line65m1_ok,Line65m2_ok,Line65m3_ok,Line65m4_ok,Line65m5_ok,Line65m6_ok,Line65m7_ok]
end CatalanCore.Cert.SigmaQuarter
