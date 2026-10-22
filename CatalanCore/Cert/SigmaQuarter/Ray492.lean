module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Ray492m0 : Macro := { x0 := (-297990199706), y0 := (564117110784), i0 := 26, i1 := 1358, fd := ((-2466920946464678432503689421),(-397966357030294339112035424),(360997837942971868444),(478432179279853100165365760),(257851028966312116224),(848233928745346)), boxes := [
    (((-279065501082),(-277454886297),(502511173632),(507343011840)),((-186043667388),(-184969924198),(335007449088),(338228674560))),
    (((-280676113818),(-279065499033),(507343011840),(512174850048)),((-187117409212),(-186043666022),(338228674560),(341449900032))),
    (((-282286726554),(-280676111769),(512174850048),(517006688256)),((-188191151036),(-187117407846),(341449900032),(344671125504))),
    (((-283897339290),(-282286724505),(517006688256),(521838526464)),((-189264892860),(-188191149670),(344671125504),(347892350976)))
] }
theorem Ray492m0_far : farOK pts Ray492m0 := by decide +kernel
theorem Ray492m0_ok : rayOK pts (231169 / 100000) Ray492m0 = true := by decide +kernel
def Ray492Data : List Macro := [Ray492m0]
theorem Ray492_farAll : ∀ m ∈ Ray492Data, farOK pts m := by
  intro m hm
  simp only [Ray492Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl
  exacts [Ray492m0_far]
theorem Ray492_okAll : ∀ m ∈ Ray492Data, rayOK pts (231169 / 100000) m = true := by
  intro m hm
  simp only [Ray492Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl
  exacts [Ray492m0_ok]
end CatalanCore.Cert.SigmaQuarter
