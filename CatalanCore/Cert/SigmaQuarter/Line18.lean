module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line18m0 : Macro := { x0 := (963985276928), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7236392751616753915624036698),(4728362014600849247028707328),(4849142008934918717440),(0),(886973340089086509056),(4308052863854843)), boxes := [
    (((963951722496),(964018831360),(0),(0)),((642634481664),(642679220907),(-7296840329),(0)))
] }
theorem Line18m0_far : farOK pts Line18m0 := by decide +kernel
theorem Line18m0_ok : axisOK pts Line18m0 = true := by decide +kernel
def Line18m1 : Macro := { x0 := (964052385792), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7245627860282127423139432981),(4728085522769277532139880448),(4849430239311070429184),(0),(886973340089086509056),(4307533901866698)), boxes := [
    (((964018831360),(964085940224),(0),(0)),((642679220906),(642723960150),(-7296851462),(0)))
] }
theorem Line18m1_far : farOK pts Line18m1 := by decide +kernel
theorem Line18m1_ok : axisOK pts Line18m1 = true := by decide +kernel
def Line18m2 : Macro := { x0 := (964119494656), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7254866446842785355017105977),(4727809091519986731860951040),(4849718469687222140928),(0),(886973340089086509056),(4307015046985228)), boxes := [
    (((964085940224),(964153049088),(0),(0)),((642723960149),(642768699392),(-7296862337),(0)))
] }
theorem Line18m2_far : farOK pts Line18m2 := by decide +kernel
theorem Line18m2_ok : axisOK pts Line18m2 = true := by decide +kernel
def Line18m3 : Macro := { x0 := (964186603520), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7264106009806176346240126085),(4727532747488369949126164480),(4850006700063373852672),(0),(886973340089086509056),(4306496346346067)), boxes := [
    (((964153049088),(964220157952),(0),(0)),((642768699392),(642813438635),(-7296873549),(0)))
] }
theorem Line18m3_far : farOK pts Line18m3 := by decide +kernel
theorem Line18m3_ok : axisOK pts Line18m3 = true := by decide +kernel
def Line18m4 : Macro := { x0 := (964253712384), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7273334375189145890694736803),(4727256580949902511517925376),(4850294930439525564416),(0),(886973340089086509056),(4305977867233536)), boxes := [
    (((964220157952),(964287266816),(0),(0)),((642813438634),(642858177878),(-7296887836),(0)))
] }
theorem Line18m4_far : farOK pts Line18m4 := by decide +kernel
theorem Line18m4_ok : axisOK pts Line18m4 = true := by decide +kernel
def Line18m5 : Macro := { x0 := (964320821248), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7282567057395176139289235981),(4726980247990559723534286848),(4850583160815677276160),(0),(886973340089086509056),(4305459304251284)), boxes := [
    (((964287266816),(964354375680),(0),(0)),((642858177877),(642902917120),(-7296898370),(0)))
] }
theorem Line18m5_far : farOK pts Line18m5 := by decide +kernel
theorem Line18m5_ok : axisOK pts Line18m5 = true := by decide +kernel
def Line18m6 : Macro := { x0 := (964387930112), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7291796890751146000902738468),(4726703961063770627015442432),(4850871391191828987904),(0),(886973340089086509056),(4304940842635885)), boxes := [
    (((964354375680),(964421484544),(0),(0)),((642902917120),(642947656363),(-7296908445),(0)))
] }
theorem Line18m6_far : farOK pts Line18m6 := by decide +kernel
theorem Line18m6_ok : axisOK pts Line18m6 = true := by decide +kernel
def Line18m7 : Macro := { x0 := (964455038976), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7301021368042933556664876642),(4726427674687892972025151488),(4851159621567980699648),(0),(886973340089086509056),(4304422454441621)), boxes := [
    (((964421484544),(964488593408),(0),(0)),((642947656362),(642992395606),(-7296918629),(0)))
] }
theorem Line18m7_far : farOK pts Line18m7 := by decide +kernel
theorem Line18m7_ok : axisOK pts Line18m7 = true := by decide +kernel
def Line18Data : List Macro := [Line18m0,Line18m1,Line18m2,Line18m3,Line18m4,Line18m5,Line18m6,Line18m7]
theorem Line18_farAll : ∀ m ∈ Line18Data, farOK pts m := by
  intro m hm
  simp only [Line18Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line18m0_far,Line18m1_far,Line18m2_far,Line18m3_far,Line18m4_far,Line18m5_far,Line18m6_far,Line18m7_far]
theorem Line18_okAll : ∀ m ∈ Line18Data, axisOK pts m = true := by
  intro m hm
  simp only [Line18Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line18m0_ok,Line18m1_ok,Line18m2_ok,Line18m3_ok,Line18m4_ok,Line18m5_ok,Line18m6_ok,Line18m7_ok]
end CatalanCore.Cert.SigmaQuarter
