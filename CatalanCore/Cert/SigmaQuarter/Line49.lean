module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line49m0 : Macro := { x0 := (973464403968), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8535492240277592903025094842),(4689635561053974816855949312),(4889854549566348001280),(0),(886973340089086509056),(4235679972582743)), boxes := [
    (((973447626752),(973481181184),(0),(0)),((648965084501),(648987454123),(-7296915183),(0)))
] }
theorem Line49m0_far : farOK pts Line49m0 := by decide +kernel
theorem Line49m0_ok : axisOK pts Line49m0 = true := by decide +kernel
def Line49m1 : Macro := { x0 := (973497958400), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8540073729257594320397730241),(4689499697302666287648014336),(4889998664754423857152),(0),(886973340089086509056),(4235427130158027)), boxes := [
    (((973481181184),(973514735616),(0),(0)),((648987454122),(649009823744),(-7296912483),(0)))
] }
theorem Line49m1_far : farOK pts Line49m1 := by decide +kernel
theorem Line49m1_ok : axisOK pts Line49m1 = true := by decide +kernel
def Line49m2 : Macro := { x0 := (973531512832), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8544650653368080380194519124),(4689363829428806108559835136),(4890142779942499713024),(0),(886973340089086509056),(4235174303484664)), boxes := [
    (((973514735616),(973548290048),(0),(0)),((649009823744),(649032193366),(-7296909653),(0)))
] }
theorem Line49m2_far : farOK pts Line49m2 := by decide +kernel
theorem Line49m2_ok : axisOK pts Line49m2 = true := by decide +kernel
def Line49m3 : Macro := { x0 := (973565067264), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8549234858152800989658416365),(4689227697468002725471322112),(4890286895130575568896),(0),(886973340089086509056),(4234921249970405)), boxes := [
    (((973548290048),(973581844480),(0),(0)),((649032193365),(649054562987),(-7296906657),(0)))
] }
theorem Line49m3_far : farOK pts Line49m3 := by decide +kernel
theorem Line49m3_ok : axisOK pts Line49m3 = true := by decide +kernel
def Line49m4 : Macro := { x0 := (973598621696), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8553810502012771628602138058),(4689091765468974905141231616),(4890431010318651424768),(0),(886973340089086509056),(4234668402449280)), boxes := [
    (((973581844480),(973615398912),(0),(0)),((649054562986),(649076932608),(-7296903682),(0)))
] }
theorem Line49m4_far : farOK pts Line49m4 := by decide +kernel
theorem Line49m4_ok : axisOK pts Line49m4 = true := by decide +kernel
def Line49m5 : Macro := { x0 := (973632176128), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8558393233837301965001590364),(4688955865214185230074970112),(4890575125506727280640),(0),(886973340089086509056),(4234415576904444)), boxes := [
    (((973615398912),(973648953344),(0),(0)),((649076932608),(649099302230),(-7296900973),(0)))
] }
theorem Line49m5_far : farOK pts Line49m5 := by decide +kernel
theorem Line49m5_ok : axisOK pts Line49m5 = true := by decide +kernel
def Line49m6 : Macro := { x0 := (973665730560), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8562970728173424427130663428),(4688820123788818892991430656),(4890719240694803136512),(0),(886973340089086509056),(4234162930339362)), boxes := [
    (((973648953344),(973682507776),(0),(0)),((649099302229),(649121671851),(-7296898111),(0)))
] }
theorem Line49m6_far : farOK pts Line49m6 := by decide +kernel
theorem Line49m6_ok : axisOK pts Line49m6 = true := by decide +kernel
def Line49m7 : Macro := { x0 := (973699284992), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8567554950373884384754478581),(4688684155660194216011431936),(4890863355882878992384),(0),(886973340089086509056),(4233910079740003)), boxes := [
    (((973682507776),(973716062208),(0),(0)),((649121671850),(649144041472),(-7296895120),(0)))
] }
theorem Line49m7_far : farOK pts Line49m7 := by decide +kernel
theorem Line49m7_ok : axisOK pts Line49m7 = true := by decide +kernel
def Line49Data : List Macro := [Line49m0,Line49m1,Line49m2,Line49m3,Line49m4,Line49m5,Line49m6,Line49m7]
theorem Line49_farAll : ∀ m ∈ Line49Data, farOK pts m := by
  intro m hm
  simp only [Line49Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line49m0_far,Line49m1_far,Line49m2_far,Line49m3_far,Line49m4_far,Line49m5_far,Line49m6_far,Line49m7_far]
theorem Line49_okAll : ∀ m ∈ Line49Data, axisOK pts m = true := by
  intro m hm
  simp only [Line49Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line49m0_ok,Line49m1_ok,Line49m2_ok,Line49m3_ok,Line49m4_ok,Line49m5_ok,Line49m6_ok,Line49m7_ok]
end CatalanCore.Cert.SigmaQuarter
