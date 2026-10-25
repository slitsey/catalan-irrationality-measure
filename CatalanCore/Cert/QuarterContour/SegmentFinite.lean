module
public import CatalanCore.Cert.QuarterContour.SegmentLedgerBridge
public import CatalanCore.Cert.QuarterCompute.SegmentCellsBounded0
public import CatalanCore.Cert.QuarterCompute.SegmentCellsBounded1
public import CatalanCore.Cert.QuarterCompute.SegmentCellsBounded2
public import CatalanCore.Cert.QuarterCompute.SegmentCellsBounded3
public import CatalanCore.Cert.QuarterCompute.SegmentCellsBounded4
public import CatalanCore.Cert.QuarterCompute.SegmentCellsBounded5
public import CatalanCore.Cert.QuarterCompute.SegmentCellsBounded6
public import CatalanCore.Cert.QuarterCompute.SegmentCellsBounded7
public import CatalanCore.Cert.QuarterCompute.SegmentCellsBounded8
public import CatalanCore.Cert.QuarterCompute.SegmentCellsBounded9
public import CatalanCore.Cert.QuarterCompute.SegmentCellsBounded10
public import CatalanCore.Cert.QuarterCompute.SegmentCellsBounded11
public import CatalanCore.Cert.QuarterCompute.SegmentCellsBounded12
public import CatalanCore.Cert.QuarterCompute.SegmentCellsBounded13
public import CatalanCore.Cert.QuarterCompute.SegmentCellsBounded14
public import CatalanCore.Cert.QuarterCompute.SegmentCellsBounded15
public import CatalanCore.Cert.QuarterCompute.SegmentCellsBounded16
public import CatalanCore.Cert.QuarterCompute.SegmentCellsBounded17
public import CatalanCore.Cert.QuarterCompute.SegmentCellsBounded18
public import CatalanCore.Cert.QuarterCompute.SegmentCellsBounded19
public import CatalanCore.Cert.QuarterCompute.SegmentCellsBounded20
public import CatalanCore.Cert.QuarterCompute.SegmentCellsBounded21
public import CatalanCore.Cert.QuarterCompute.SegmentCellsBounded22
public import CatalanCore.Cert.QuarterCompute.SegmentCellsBounded23
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.SegmentFinite
open CatalanCore.Cert.QuarterCompute
open CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
def cells : List QBox := SegmentCellsBounded0.cells ++ SegmentCellsBounded1.cells ++ SegmentCellsBounded2.cells ++ SegmentCellsBounded3.cells ++ SegmentCellsBounded4.cells ++ SegmentCellsBounded5.cells ++ SegmentCellsBounded6.cells ++ SegmentCellsBounded7.cells ++ SegmentCellsBounded8.cells ++ SegmentCellsBounded9.cells ++ SegmentCellsBounded10.cells ++ SegmentCellsBounded11.cells ++ SegmentCellsBounded12.cells ++ SegmentCellsBounded13.cells ++ SegmentCellsBounded14.cells ++ SegmentCellsBounded15.cells ++ SegmentCellsBounded16.cells ++ SegmentCellsBounded17.cells ++ SegmentCellsBounded18.cells ++ SegmentCellsBounded19.cells ++ SegmentCellsBounded20.cells ++ SegmentCellsBounded21.cells ++ SegmentCellsBounded22.cells ++ SegmentCellsBounded23.cells
def SVAL : ℤ := -7295525068634537562430208
theorem shapes_checked : cells.all (fun b => decide (SegmentLedger.shape b)) = true := by
  simp only [cells,List.all_append,SegmentCellsBounded0.shape_checked,SegmentCellsBounded1.shape_checked,SegmentCellsBounded2.shape_checked,SegmentCellsBounded3.shape_checked,SegmentCellsBounded4.shape_checked,SegmentCellsBounded5.shape_checked,SegmentCellsBounded6.shape_checked,SegmentCellsBounded7.shape_checked,SegmentCellsBounded8.shape_checked,SegmentCellsBounded9.shape_checked,SegmentCellsBounded10.shape_checked,SegmentCellsBounded11.shape_checked,SegmentCellsBounded12.shape_checked,SegmentCellsBounded13.shape_checked,SegmentCellsBounded14.shape_checked,SegmentCellsBounded15.shape_checked,SegmentCellsBounded16.shape_checked,SegmentCellsBounded17.shape_checked,SegmentCellsBounded18.shape_checked,SegmentCellsBounded19.shape_checked,SegmentCellsBounded20.shape_checked,SegmentCellsBounded21.shape_checked,SegmentCellsBounded22.shape_checked,SegmentCellsBounded23.shape_checked,Bool.true_and]
theorem shape (b : QBox) (hb : b ∈ cells) : QuarterContour.segShape b := by
  exact of_decide_eq_true ((List.all_eq_true.mp shapes_checked) b hb)
theorem sval_checked : SegmentFold.svalues 115867 50000 cells = SVAL := by
  simp only [cells,SegmentFold.svalues_append]
  simp only [SegmentLedgerBridge.svalues_eq,SegmentCellsBounded0.sval_checked,SegmentCellsBounded1.sval_checked,SegmentCellsBounded2.sval_checked,SegmentCellsBounded3.sval_checked,SegmentCellsBounded4.sval_checked,SegmentCellsBounded5.sval_checked,SegmentCellsBounded6.sval_checked,SegmentCellsBounded7.sval_checked,SegmentCellsBounded8.sval_checked,SegmentCellsBounded9.sval_checked,SegmentCellsBounded10.sval_checked,SegmentCellsBounded11.sval_checked,SegmentCellsBounded12.sval_checked,SegmentCellsBounded13.sval_checked,SegmentCellsBounded14.sval_checked,SegmentCellsBounded15.sval_checked,SegmentCellsBounded16.sval_checked,SegmentCellsBounded17.sval_checked,SegmentCellsBounded18.sval_checked,SegmentCellsBounded19.sval_checked,SegmentCellsBounded20.sval_checked,SegmentCellsBounded21.sval_checked,SegmentCellsBounded22.sval_checked,SegmentCellsBounded23.sval_checked]
  decide +kernel
theorem scost : (-154489/5000000 : ℚ) ≤ (cells.map (QuarterContour.segCost (115867/50000))).sum := by
  have he : (115867/50000 : ℚ) = ((115867 : ℤ) : ℚ)/((50000 : ℤ) : ℚ) := by norm_num
  rw [he,SegmentFold.cost_sum_sval 115867 50000 (by norm_num) cells,sval_checked]
  norm_num [SVAL]
theorem cover : IntervalCovers (cells.map QuarterContour.axisInterval) (-107/1000) 0 := by
  have h0 : IntervalCovers (SegmentCellsBounded0.cells.map QuarterContour.axisInterval) ((SegmentCellsBounded0.lower : ℚ)/2^40) ((SegmentCellsBounded0.upper : ℚ)/2^40) := by
    have hp0 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded0.part0 (-117647744173 : ℤ) (-117341369840 : ℤ) SegmentCellsBounded0.cover0
    have hp1 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded0.part1 (-117341369840 : ℤ) (-117034995506 : ℤ) SegmentCellsBounded0.cover1
    have hp2 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded0.part2 (-117034995506 : ℤ) (-116728621172 : ℤ) SegmentCellsBounded0.cover2
    have hp3 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded0.part3 (-116728621172 : ℤ) (-116422246838 : ℤ) SegmentCellsBounded0.cover3
    have hp4 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded0.part4 (-116422246838 : ℤ) (-116115872505 : ℤ) SegmentCellsBounded0.cover4
    have hp5 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded0.part5 (-116115872505 : ℤ) (-115809498171 : ℤ) SegmentCellsBounded0.cover5
    have hp6 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded0.part6 (-115809498171 : ℤ) (-115503123837 : ℤ) SegmentCellsBounded0.cover6
    have hp7 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded0.part7 (-115503123837 : ℤ) (-115196749503 : ℤ) SegmentCellsBounded0.cover7
    have hp8 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded0.part8 (-115196749503 : ℤ) (-114890375169 : ℤ) SegmentCellsBounded0.cover8
    have hp9 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded0.part9 (-114890375169 : ℤ) (-114584000836 : ℤ) SegmentCellsBounded0.cover9
    have hp10 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded0.part10 (-114584000836 : ℤ) (-114277626502 : ℤ) SegmentCellsBounded0.cover10
    have hp11 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded0.part11 (-114277626502 : ℤ) (-113971252168 : ℤ) SegmentCellsBounded0.cover11
    have hp12 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded0.part12 (-113971252168 : ℤ) (-113664877834 : ℤ) SegmentCellsBounded0.cover12
    have hp13 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded0.part13 (-113664877834 : ℤ) (-113358503501 : ℤ) SegmentCellsBounded0.cover13
    have hp14 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded0.part14 (-113358503501 : ℤ) (-113052129167 : ℤ) SegmentCellsBounded0.cover14
    have hp15 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded0.part15 (-113052129167 : ℤ) (-112745754833 : ℤ) SegmentCellsBounded0.cover15
    simp only [SegmentCellsBounded0.cells,List.map_append,List.append_assoc]
    exact (intervalCovers_append hp0 (intervalCovers_append hp1 (intervalCovers_append hp2 (intervalCovers_append hp3 (intervalCovers_append hp4 (intervalCovers_append hp5 (intervalCovers_append hp6 (intervalCovers_append hp7 (intervalCovers_append hp8 (intervalCovers_append hp9 (intervalCovers_append hp10 (intervalCovers_append hp11 (intervalCovers_append hp12 (intervalCovers_append hp13 (intervalCovers_append hp14 hp15 (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num))
  have h1 : IntervalCovers (SegmentCellsBounded1.cells.map QuarterContour.axisInterval) ((SegmentCellsBounded1.lower : ℚ)/2^40) ((SegmentCellsBounded1.upper : ℚ)/2^40) := by
    have hp0 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded1.part0 (-112745754833 : ℤ) (-112439380499 : ℤ) SegmentCellsBounded1.cover0
    have hp1 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded1.part1 (-112439380499 : ℤ) (-112133006165 : ℤ) SegmentCellsBounded1.cover1
    have hp2 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded1.part2 (-112133006165 : ℤ) (-111826631832 : ℤ) SegmentCellsBounded1.cover2
    have hp3 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded1.part3 (-111826631832 : ℤ) (-111520257498 : ℤ) SegmentCellsBounded1.cover3
    have hp4 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded1.part4 (-111520257498 : ℤ) (-111213883164 : ℤ) SegmentCellsBounded1.cover4
    have hp5 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded1.part5 (-111213883164 : ℤ) (-110907508830 : ℤ) SegmentCellsBounded1.cover5
    have hp6 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded1.part6 (-110907508830 : ℤ) (-110601134496 : ℤ) SegmentCellsBounded1.cover6
    have hp7 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded1.part7 (-110601134496 : ℤ) (-110294760163 : ℤ) SegmentCellsBounded1.cover7
    have hp8 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded1.part8 (-110294760163 : ℤ) (-109988385829 : ℤ) SegmentCellsBounded1.cover8
    have hp9 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded1.part9 (-109988385829 : ℤ) (-109682011495 : ℤ) SegmentCellsBounded1.cover9
    have hp10 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded1.part10 (-109682011495 : ℤ) (-109375637161 : ℤ) SegmentCellsBounded1.cover10
    have hp11 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded1.part11 (-109375637161 : ℤ) (-109069262828 : ℤ) SegmentCellsBounded1.cover11
    have hp12 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded1.part12 (-109069262828 : ℤ) (-108762888494 : ℤ) SegmentCellsBounded1.cover12
    have hp13 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded1.part13 (-108762888494 : ℤ) (-108456514160 : ℤ) SegmentCellsBounded1.cover13
    have hp14 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded1.part14 (-108456514160 : ℤ) (-108150139826 : ℤ) SegmentCellsBounded1.cover14
    have hp15 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded1.part15 (-108150139826 : ℤ) (-107843765492 : ℤ) SegmentCellsBounded1.cover15
    simp only [SegmentCellsBounded1.cells,List.map_append,List.append_assoc]
    exact (intervalCovers_append hp0 (intervalCovers_append hp1 (intervalCovers_append hp2 (intervalCovers_append hp3 (intervalCovers_append hp4 (intervalCovers_append hp5 (intervalCovers_append hp6 (intervalCovers_append hp7 (intervalCovers_append hp8 (intervalCovers_append hp9 (intervalCovers_append hp10 (intervalCovers_append hp11 (intervalCovers_append hp12 (intervalCovers_append hp13 (intervalCovers_append hp14 hp15 (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num))
  have h2 : IntervalCovers (SegmentCellsBounded2.cells.map QuarterContour.axisInterval) ((SegmentCellsBounded2.lower : ℚ)/2^40) ((SegmentCellsBounded2.upper : ℚ)/2^40) := by
    have hp0 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded2.part0 (-107843765492 : ℤ) (-107537391159 : ℤ) SegmentCellsBounded2.cover0
    have hp1 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded2.part1 (-107537391159 : ℤ) (-107231016825 : ℤ) SegmentCellsBounded2.cover1
    have hp2 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded2.part2 (-107231016825 : ℤ) (-106924642491 : ℤ) SegmentCellsBounded2.cover2
    have hp3 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded2.part3 (-106924642491 : ℤ) (-106618268157 : ℤ) SegmentCellsBounded2.cover3
    have hp4 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded2.part4 (-106618268157 : ℤ) (-106311893823 : ℤ) SegmentCellsBounded2.cover4
    have hp5 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded2.part5 (-106311893823 : ℤ) (-106005519490 : ℤ) SegmentCellsBounded2.cover5
    have hp6 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded2.part6 (-106005519490 : ℤ) (-105699145156 : ℤ) SegmentCellsBounded2.cover6
    have hp7 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded2.part7 (-105699145156 : ℤ) (-105392770822 : ℤ) SegmentCellsBounded2.cover7
    have hp8 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded2.part8 (-105392770822 : ℤ) (-105086396488 : ℤ) SegmentCellsBounded2.cover8
    have hp9 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded2.part9 (-105086396488 : ℤ) (-104780022155 : ℤ) SegmentCellsBounded2.cover9
    have hp10 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded2.part10 (-104780022155 : ℤ) (-104473647821 : ℤ) SegmentCellsBounded2.cover10
    have hp11 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded2.part11 (-104473647821 : ℤ) (-104167273487 : ℤ) SegmentCellsBounded2.cover11
    have hp12 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded2.part12 (-104167273487 : ℤ) (-103860899153 : ℤ) SegmentCellsBounded2.cover12
    have hp13 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded2.part13 (-103860899153 : ℤ) (-103554524819 : ℤ) SegmentCellsBounded2.cover13
    have hp14 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded2.part14 (-103554524819 : ℤ) (-103248150486 : ℤ) SegmentCellsBounded2.cover14
    have hp15 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded2.part15 (-103248150486 : ℤ) (-102941776152 : ℤ) SegmentCellsBounded2.cover15
    simp only [SegmentCellsBounded2.cells,List.map_append,List.append_assoc]
    exact (intervalCovers_append hp0 (intervalCovers_append hp1 (intervalCovers_append hp2 (intervalCovers_append hp3 (intervalCovers_append hp4 (intervalCovers_append hp5 (intervalCovers_append hp6 (intervalCovers_append hp7 (intervalCovers_append hp8 (intervalCovers_append hp9 (intervalCovers_append hp10 (intervalCovers_append hp11 (intervalCovers_append hp12 (intervalCovers_append hp13 (intervalCovers_append hp14 hp15 (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num))
  have h3 : IntervalCovers (SegmentCellsBounded3.cells.map QuarterContour.axisInterval) ((SegmentCellsBounded3.lower : ℚ)/2^40) ((SegmentCellsBounded3.upper : ℚ)/2^40) := by
    have hp0 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded3.part0 (-102941776152 : ℤ) (-102635401818 : ℤ) SegmentCellsBounded3.cover0
    have hp1 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded3.part1 (-102635401818 : ℤ) (-102329027484 : ℤ) SegmentCellsBounded3.cover1
    have hp2 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded3.part2 (-102329027484 : ℤ) (-102022653151 : ℤ) SegmentCellsBounded3.cover2
    have hp3 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded3.part3 (-102022653151 : ℤ) (-101716278817 : ℤ) SegmentCellsBounded3.cover3
    have hp4 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded3.part4 (-101716278817 : ℤ) (-101409904483 : ℤ) SegmentCellsBounded3.cover4
    have hp5 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded3.part5 (-101409904483 : ℤ) (-101103530149 : ℤ) SegmentCellsBounded3.cover5
    have hp6 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded3.part6 (-101103530149 : ℤ) (-100797155815 : ℤ) SegmentCellsBounded3.cover6
    have hp7 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded3.part7 (-100797155815 : ℤ) (-100490781482 : ℤ) SegmentCellsBounded3.cover7
    have hp8 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded3.part8 (-100490781482 : ℤ) (-100184407148 : ℤ) SegmentCellsBounded3.cover8
    have hp9 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded3.part9 (-100184407148 : ℤ) (-99878032814 : ℤ) SegmentCellsBounded3.cover9
    have hp10 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded3.part10 (-99878032814 : ℤ) (-99571658480 : ℤ) SegmentCellsBounded3.cover10
    have hp11 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded3.part11 (-99571658480 : ℤ) (-99265284146 : ℤ) SegmentCellsBounded3.cover11
    have hp12 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded3.part12 (-99265284146 : ℤ) (-98958909813 : ℤ) SegmentCellsBounded3.cover12
    have hp13 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded3.part13 (-98958909813 : ℤ) (-98652535479 : ℤ) SegmentCellsBounded3.cover13
    have hp14 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded3.part14 (-98652535479 : ℤ) (-98346161145 : ℤ) SegmentCellsBounded3.cover14
    have hp15 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded3.part15 (-98346161145 : ℤ) (-98039786811 : ℤ) SegmentCellsBounded3.cover15
    simp only [SegmentCellsBounded3.cells,List.map_append,List.append_assoc]
    exact (intervalCovers_append hp0 (intervalCovers_append hp1 (intervalCovers_append hp2 (intervalCovers_append hp3 (intervalCovers_append hp4 (intervalCovers_append hp5 (intervalCovers_append hp6 (intervalCovers_append hp7 (intervalCovers_append hp8 (intervalCovers_append hp9 (intervalCovers_append hp10 (intervalCovers_append hp11 (intervalCovers_append hp12 (intervalCovers_append hp13 (intervalCovers_append hp14 hp15 (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num))
  have h4 : IntervalCovers (SegmentCellsBounded4.cells.map QuarterContour.axisInterval) ((SegmentCellsBounded4.lower : ℚ)/2^40) ((SegmentCellsBounded4.upper : ℚ)/2^40) := by
    have hp0 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded4.part0 (-98039786811 : ℤ) (-97733412478 : ℤ) SegmentCellsBounded4.cover0
    have hp1 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded4.part1 (-97733412478 : ℤ) (-97427038144 : ℤ) SegmentCellsBounded4.cover1
    have hp2 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded4.part2 (-97427038144 : ℤ) (-97120663810 : ℤ) SegmentCellsBounded4.cover2
    have hp3 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded4.part3 (-97120663810 : ℤ) (-96814289476 : ℤ) SegmentCellsBounded4.cover3
    have hp4 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded4.part4 (-96814289476 : ℤ) (-96507915142 : ℤ) SegmentCellsBounded4.cover4
    have hp5 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded4.part5 (-96507915142 : ℤ) (-96201540809 : ℤ) SegmentCellsBounded4.cover5
    have hp6 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded4.part6 (-96201540809 : ℤ) (-95895166475 : ℤ) SegmentCellsBounded4.cover6
    have hp7 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded4.part7 (-95895166475 : ℤ) (-95588792141 : ℤ) SegmentCellsBounded4.cover7
    have hp8 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded4.part8 (-95588792141 : ℤ) (-95282417807 : ℤ) SegmentCellsBounded4.cover8
    have hp9 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded4.part9 (-95282417807 : ℤ) (-94976043473 : ℤ) SegmentCellsBounded4.cover9
    have hp10 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded4.part10 (-94976043473 : ℤ) (-94669669140 : ℤ) SegmentCellsBounded4.cover10
    have hp11 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded4.part11 (-94669669140 : ℤ) (-94363294806 : ℤ) SegmentCellsBounded4.cover11
    have hp12 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded4.part12 (-94363294806 : ℤ) (-94056920472 : ℤ) SegmentCellsBounded4.cover12
    have hp13 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded4.part13 (-94056920472 : ℤ) (-93750546138 : ℤ) SegmentCellsBounded4.cover13
    have hp14 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded4.part14 (-93750546138 : ℤ) (-93444171805 : ℤ) SegmentCellsBounded4.cover14
    have hp15 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded4.part15 (-93444171805 : ℤ) (-93137797471 : ℤ) SegmentCellsBounded4.cover15
    simp only [SegmentCellsBounded4.cells,List.map_append,List.append_assoc]
    exact (intervalCovers_append hp0 (intervalCovers_append hp1 (intervalCovers_append hp2 (intervalCovers_append hp3 (intervalCovers_append hp4 (intervalCovers_append hp5 (intervalCovers_append hp6 (intervalCovers_append hp7 (intervalCovers_append hp8 (intervalCovers_append hp9 (intervalCovers_append hp10 (intervalCovers_append hp11 (intervalCovers_append hp12 (intervalCovers_append hp13 (intervalCovers_append hp14 hp15 (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num))
  have h5 : IntervalCovers (SegmentCellsBounded5.cells.map QuarterContour.axisInterval) ((SegmentCellsBounded5.lower : ℚ)/2^40) ((SegmentCellsBounded5.upper : ℚ)/2^40) := by
    have hp0 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded5.part0 (-93137797471 : ℤ) (-92831423137 : ℤ) SegmentCellsBounded5.cover0
    have hp1 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded5.part1 (-92831423137 : ℤ) (-92525048803 : ℤ) SegmentCellsBounded5.cover1
    have hp2 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded5.part2 (-92525048803 : ℤ) (-92218674469 : ℤ) SegmentCellsBounded5.cover2
    have hp3 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded5.part3 (-92218674469 : ℤ) (-91912300136 : ℤ) SegmentCellsBounded5.cover3
    have hp4 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded5.part4 (-91912300136 : ℤ) (-91605925802 : ℤ) SegmentCellsBounded5.cover4
    have hp5 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded5.part5 (-91605925802 : ℤ) (-91299551468 : ℤ) SegmentCellsBounded5.cover5
    have hp6 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded5.part6 (-91299551468 : ℤ) (-90993177134 : ℤ) SegmentCellsBounded5.cover6
    have hp7 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded5.part7 (-90993177134 : ℤ) (-90686802801 : ℤ) SegmentCellsBounded5.cover7
    have hp8 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded5.part8 (-90686802801 : ℤ) (-90380428467 : ℤ) SegmentCellsBounded5.cover8
    have hp9 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded5.part9 (-90380428467 : ℤ) (-90074054133 : ℤ) SegmentCellsBounded5.cover9
    have hp10 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded5.part10 (-90074054133 : ℤ) (-89767679799 : ℤ) SegmentCellsBounded5.cover10
    have hp11 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded5.part11 (-89767679799 : ℤ) (-89461305465 : ℤ) SegmentCellsBounded5.cover11
    have hp12 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded5.part12 (-89461305465 : ℤ) (-89154931132 : ℤ) SegmentCellsBounded5.cover12
    have hp13 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded5.part13 (-89154931132 : ℤ) (-88848556798 : ℤ) SegmentCellsBounded5.cover13
    have hp14 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded5.part14 (-88848556798 : ℤ) (-88542182464 : ℤ) SegmentCellsBounded5.cover14
    have hp15 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded5.part15 (-88542182464 : ℤ) (-88235808130 : ℤ) SegmentCellsBounded5.cover15
    simp only [SegmentCellsBounded5.cells,List.map_append,List.append_assoc]
    exact (intervalCovers_append hp0 (intervalCovers_append hp1 (intervalCovers_append hp2 (intervalCovers_append hp3 (intervalCovers_append hp4 (intervalCovers_append hp5 (intervalCovers_append hp6 (intervalCovers_append hp7 (intervalCovers_append hp8 (intervalCovers_append hp9 (intervalCovers_append hp10 (intervalCovers_append hp11 (intervalCovers_append hp12 (intervalCovers_append hp13 (intervalCovers_append hp14 hp15 (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num))
  have h6 : IntervalCovers (SegmentCellsBounded6.cells.map QuarterContour.axisInterval) ((SegmentCellsBounded6.lower : ℚ)/2^40) ((SegmentCellsBounded6.upper : ℚ)/2^40) := by
    have hp0 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded6.part0 (-88235808130 : ℤ) (-87929433796 : ℤ) SegmentCellsBounded6.cover0
    have hp1 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded6.part1 (-87929433796 : ℤ) (-87623059463 : ℤ) SegmentCellsBounded6.cover1
    have hp2 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded6.part2 (-87623059463 : ℤ) (-87316685129 : ℤ) SegmentCellsBounded6.cover2
    have hp3 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded6.part3 (-87316685129 : ℤ) (-87010310795 : ℤ) SegmentCellsBounded6.cover3
    have hp4 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded6.part4 (-87010310795 : ℤ) (-86703936461 : ℤ) SegmentCellsBounded6.cover4
    have hp5 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded6.part5 (-86703936461 : ℤ) (-86397562128 : ℤ) SegmentCellsBounded6.cover5
    have hp6 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded6.part6 (-86397562128 : ℤ) (-86091187794 : ℤ) SegmentCellsBounded6.cover6
    have hp7 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded6.part7 (-86091187794 : ℤ) (-85784813460 : ℤ) SegmentCellsBounded6.cover7
    have hp8 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded6.part8 (-85784813460 : ℤ) (-85478439126 : ℤ) SegmentCellsBounded6.cover8
    have hp9 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded6.part9 (-85478439126 : ℤ) (-85172064792 : ℤ) SegmentCellsBounded6.cover9
    have hp10 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded6.part10 (-85172064792 : ℤ) (-84865690459 : ℤ) SegmentCellsBounded6.cover10
    have hp11 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded6.part11 (-84865690459 : ℤ) (-84559316125 : ℤ) SegmentCellsBounded6.cover11
    have hp12 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded6.part12 (-84559316125 : ℤ) (-84252941791 : ℤ) SegmentCellsBounded6.cover12
    have hp13 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded6.part13 (-84252941791 : ℤ) (-83946567457 : ℤ) SegmentCellsBounded6.cover13
    have hp14 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded6.part14 (-83946567457 : ℤ) (-83640193123 : ℤ) SegmentCellsBounded6.cover14
    have hp15 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded6.part15 (-83640193123 : ℤ) (-83333818790 : ℤ) SegmentCellsBounded6.cover15
    simp only [SegmentCellsBounded6.cells,List.map_append,List.append_assoc]
    exact (intervalCovers_append hp0 (intervalCovers_append hp1 (intervalCovers_append hp2 (intervalCovers_append hp3 (intervalCovers_append hp4 (intervalCovers_append hp5 (intervalCovers_append hp6 (intervalCovers_append hp7 (intervalCovers_append hp8 (intervalCovers_append hp9 (intervalCovers_append hp10 (intervalCovers_append hp11 (intervalCovers_append hp12 (intervalCovers_append hp13 (intervalCovers_append hp14 hp15 (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num))
  have h7 : IntervalCovers (SegmentCellsBounded7.cells.map QuarterContour.axisInterval) ((SegmentCellsBounded7.lower : ℚ)/2^40) ((SegmentCellsBounded7.upper : ℚ)/2^40) := by
    have hp0 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded7.part0 (-83333818790 : ℤ) (-83027444456 : ℤ) SegmentCellsBounded7.cover0
    have hp1 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded7.part1 (-83027444456 : ℤ) (-82721070122 : ℤ) SegmentCellsBounded7.cover1
    have hp2 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded7.part2 (-82721070122 : ℤ) (-82414695788 : ℤ) SegmentCellsBounded7.cover2
    have hp3 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded7.part3 (-82414695788 : ℤ) (-82108321455 : ℤ) SegmentCellsBounded7.cover3
    have hp4 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded7.part4 (-82108321455 : ℤ) (-81801947121 : ℤ) SegmentCellsBounded7.cover4
    have hp5 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded7.part5 (-81801947121 : ℤ) (-81495572787 : ℤ) SegmentCellsBounded7.cover5
    have hp6 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded7.part6 (-81495572787 : ℤ) (-81189198453 : ℤ) SegmentCellsBounded7.cover6
    have hp7 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded7.part7 (-81189198453 : ℤ) (-80882824119 : ℤ) SegmentCellsBounded7.cover7
    have hp8 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded7.part8 (-80882824119 : ℤ) (-80576449786 : ℤ) SegmentCellsBounded7.cover8
    have hp9 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded7.part9 (-80576449786 : ℤ) (-80270075452 : ℤ) SegmentCellsBounded7.cover9
    have hp10 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded7.part10 (-80270075452 : ℤ) (-79963701118 : ℤ) SegmentCellsBounded7.cover10
    have hp11 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded7.part11 (-79963701118 : ℤ) (-79657326784 : ℤ) SegmentCellsBounded7.cover11
    have hp12 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded7.part12 (-79657326784 : ℤ) (-79350952451 : ℤ) SegmentCellsBounded7.cover12
    have hp13 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded7.part13 (-79350952451 : ℤ) (-79044578117 : ℤ) SegmentCellsBounded7.cover13
    have hp14 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded7.part14 (-79044578117 : ℤ) (-78738203783 : ℤ) SegmentCellsBounded7.cover14
    have hp15 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded7.part15 (-78738203783 : ℤ) (-78431829449 : ℤ) SegmentCellsBounded7.cover15
    simp only [SegmentCellsBounded7.cells,List.map_append,List.append_assoc]
    exact (intervalCovers_append hp0 (intervalCovers_append hp1 (intervalCovers_append hp2 (intervalCovers_append hp3 (intervalCovers_append hp4 (intervalCovers_append hp5 (intervalCovers_append hp6 (intervalCovers_append hp7 (intervalCovers_append hp8 (intervalCovers_append hp9 (intervalCovers_append hp10 (intervalCovers_append hp11 (intervalCovers_append hp12 (intervalCovers_append hp13 (intervalCovers_append hp14 hp15 (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num))
  have h8 : IntervalCovers (SegmentCellsBounded8.cells.map QuarterContour.axisInterval) ((SegmentCellsBounded8.lower : ℚ)/2^40) ((SegmentCellsBounded8.upper : ℚ)/2^40) := by
    have hp0 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded8.part0 (-78431829449 : ℤ) (-78125455115 : ℤ) SegmentCellsBounded8.cover0
    have hp1 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded8.part1 (-78125455115 : ℤ) (-77819080782 : ℤ) SegmentCellsBounded8.cover1
    have hp2 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded8.part2 (-77819080782 : ℤ) (-77512706448 : ℤ) SegmentCellsBounded8.cover2
    have hp3 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded8.part3 (-77512706448 : ℤ) (-77206332114 : ℤ) SegmentCellsBounded8.cover3
    have hp4 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded8.part4 (-77206332114 : ℤ) (-76899957780 : ℤ) SegmentCellsBounded8.cover4
    have hp5 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded8.part5 (-76899957780 : ℤ) (-76593583446 : ℤ) SegmentCellsBounded8.cover5
    have hp6 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded8.part6 (-76593583446 : ℤ) (-76287209113 : ℤ) SegmentCellsBounded8.cover6
    have hp7 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded8.part7 (-76287209113 : ℤ) (-75980834779 : ℤ) SegmentCellsBounded8.cover7
    have hp8 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded8.part8 (-75980834779 : ℤ) (-75674460445 : ℤ) SegmentCellsBounded8.cover8
    have hp9 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded8.part9 (-75674460445 : ℤ) (-75368086111 : ℤ) SegmentCellsBounded8.cover9
    have hp10 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded8.part10 (-75368086111 : ℤ) (-75061711778 : ℤ) SegmentCellsBounded8.cover10
    have hp11 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded8.part11 (-75061711778 : ℤ) (-74755337444 : ℤ) SegmentCellsBounded8.cover11
    have hp12 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded8.part12 (-74755337444 : ℤ) (-74448963110 : ℤ) SegmentCellsBounded8.cover12
    have hp13 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded8.part13 (-74448963110 : ℤ) (-74142588776 : ℤ) SegmentCellsBounded8.cover13
    have hp14 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded8.part14 (-74142588776 : ℤ) (-73836214442 : ℤ) SegmentCellsBounded8.cover14
    have hp15 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded8.part15 (-73836214442 : ℤ) (-73529840109 : ℤ) SegmentCellsBounded8.cover15
    simp only [SegmentCellsBounded8.cells,List.map_append,List.append_assoc]
    exact (intervalCovers_append hp0 (intervalCovers_append hp1 (intervalCovers_append hp2 (intervalCovers_append hp3 (intervalCovers_append hp4 (intervalCovers_append hp5 (intervalCovers_append hp6 (intervalCovers_append hp7 (intervalCovers_append hp8 (intervalCovers_append hp9 (intervalCovers_append hp10 (intervalCovers_append hp11 (intervalCovers_append hp12 (intervalCovers_append hp13 (intervalCovers_append hp14 hp15 (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num))
  have h9 : IntervalCovers (SegmentCellsBounded9.cells.map QuarterContour.axisInterval) ((SegmentCellsBounded9.lower : ℚ)/2^40) ((SegmentCellsBounded9.upper : ℚ)/2^40) := by
    have hp0 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded9.part0 (-73529840109 : ℤ) (-73223465775 : ℤ) SegmentCellsBounded9.cover0
    have hp1 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded9.part1 (-73223465775 : ℤ) (-72917091441 : ℤ) SegmentCellsBounded9.cover1
    have hp2 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded9.part2 (-72917091441 : ℤ) (-72610717107 : ℤ) SegmentCellsBounded9.cover2
    have hp3 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded9.part3 (-72610717107 : ℤ) (-72304342773 : ℤ) SegmentCellsBounded9.cover3
    have hp4 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded9.part4 (-72304342773 : ℤ) (-71997968440 : ℤ) SegmentCellsBounded9.cover4
    have hp5 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded9.part5 (-71997968440 : ℤ) (-71691594106 : ℤ) SegmentCellsBounded9.cover5
    have hp6 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded9.part6 (-71691594106 : ℤ) (-71385219772 : ℤ) SegmentCellsBounded9.cover6
    have hp7 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded9.part7 (-71385219772 : ℤ) (-71078845438 : ℤ) SegmentCellsBounded9.cover7
    have hp8 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded9.part8 (-71078845438 : ℤ) (-70772471105 : ℤ) SegmentCellsBounded9.cover8
    have hp9 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded9.part9 (-70772471105 : ℤ) (-70466096771 : ℤ) SegmentCellsBounded9.cover9
    have hp10 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded9.part10 (-70466096771 : ℤ) (-70159722437 : ℤ) SegmentCellsBounded9.cover10
    have hp11 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded9.part11 (-70159722437 : ℤ) (-69853348103 : ℤ) SegmentCellsBounded9.cover11
    have hp12 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded9.part12 (-69853348103 : ℤ) (-69546973769 : ℤ) SegmentCellsBounded9.cover12
    have hp13 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded9.part13 (-69546973769 : ℤ) (-69240599436 : ℤ) SegmentCellsBounded9.cover13
    have hp14 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded9.part14 (-69240599436 : ℤ) (-68934225102 : ℤ) SegmentCellsBounded9.cover14
    have hp15 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded9.part15 (-68934225102 : ℤ) (-68627850768 : ℤ) SegmentCellsBounded9.cover15
    simp only [SegmentCellsBounded9.cells,List.map_append,List.append_assoc]
    exact (intervalCovers_append hp0 (intervalCovers_append hp1 (intervalCovers_append hp2 (intervalCovers_append hp3 (intervalCovers_append hp4 (intervalCovers_append hp5 (intervalCovers_append hp6 (intervalCovers_append hp7 (intervalCovers_append hp8 (intervalCovers_append hp9 (intervalCovers_append hp10 (intervalCovers_append hp11 (intervalCovers_append hp12 (intervalCovers_append hp13 (intervalCovers_append hp14 hp15 (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num))
  have h10 : IntervalCovers (SegmentCellsBounded10.cells.map QuarterContour.axisInterval) ((SegmentCellsBounded10.lower : ℚ)/2^40) ((SegmentCellsBounded10.upper : ℚ)/2^40) := by
    have hp0 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded10.part0 (-68627850768 : ℤ) (-68321476434 : ℤ) SegmentCellsBounded10.cover0
    have hp1 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded10.part1 (-68321476434 : ℤ) (-68015102101 : ℤ) SegmentCellsBounded10.cover1
    have hp2 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded10.part2 (-68015102101 : ℤ) (-67708727767 : ℤ) SegmentCellsBounded10.cover2
    have hp3 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded10.part3 (-67708727767 : ℤ) (-67402353433 : ℤ) SegmentCellsBounded10.cover3
    have hp4 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded10.part4 (-67402353433 : ℤ) (-67095979099 : ℤ) SegmentCellsBounded10.cover4
    have hp5 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded10.part5 (-67095979099 : ℤ) (-66789604765 : ℤ) SegmentCellsBounded10.cover5
    have hp6 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded10.part6 (-66789604765 : ℤ) (-66483230432 : ℤ) SegmentCellsBounded10.cover6
    have hp7 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded10.part7 (-66483230432 : ℤ) (-66176856098 : ℤ) SegmentCellsBounded10.cover7
    have hp8 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded10.part8 (-66176856098 : ℤ) (-65870481764 : ℤ) SegmentCellsBounded10.cover8
    have hp9 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded10.part9 (-65870481764 : ℤ) (-65564107430 : ℤ) SegmentCellsBounded10.cover9
    have hp10 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded10.part10 (-65564107430 : ℤ) (-65257733096 : ℤ) SegmentCellsBounded10.cover10
    have hp11 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded10.part11 (-65257733096 : ℤ) (-64951358763 : ℤ) SegmentCellsBounded10.cover11
    have hp12 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded10.part12 (-64951358763 : ℤ) (-64644984429 : ℤ) SegmentCellsBounded10.cover12
    have hp13 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded10.part13 (-64644984429 : ℤ) (-64338610095 : ℤ) SegmentCellsBounded10.cover13
    have hp14 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded10.part14 (-64338610095 : ℤ) (-64032235761 : ℤ) SegmentCellsBounded10.cover14
    have hp15 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded10.part15 (-64032235761 : ℤ) (-63725861428 : ℤ) SegmentCellsBounded10.cover15
    simp only [SegmentCellsBounded10.cells,List.map_append,List.append_assoc]
    exact (intervalCovers_append hp0 (intervalCovers_append hp1 (intervalCovers_append hp2 (intervalCovers_append hp3 (intervalCovers_append hp4 (intervalCovers_append hp5 (intervalCovers_append hp6 (intervalCovers_append hp7 (intervalCovers_append hp8 (intervalCovers_append hp9 (intervalCovers_append hp10 (intervalCovers_append hp11 (intervalCovers_append hp12 (intervalCovers_append hp13 (intervalCovers_append hp14 hp15 (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num))
  have h11 : IntervalCovers (SegmentCellsBounded11.cells.map QuarterContour.axisInterval) ((SegmentCellsBounded11.lower : ℚ)/2^40) ((SegmentCellsBounded11.upper : ℚ)/2^40) := by
    have hp0 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded11.part0 (-63725861428 : ℤ) (-63419487094 : ℤ) SegmentCellsBounded11.cover0
    have hp1 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded11.part1 (-63419487094 : ℤ) (-63113112760 : ℤ) SegmentCellsBounded11.cover1
    have hp2 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded11.part2 (-63113112760 : ℤ) (-62806738426 : ℤ) SegmentCellsBounded11.cover2
    have hp3 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded11.part3 (-62806738426 : ℤ) (-62500364092 : ℤ) SegmentCellsBounded11.cover3
    have hp4 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded11.part4 (-62500364092 : ℤ) (-62193989759 : ℤ) SegmentCellsBounded11.cover4
    have hp5 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded11.part5 (-62193989759 : ℤ) (-61887615425 : ℤ) SegmentCellsBounded11.cover5
    have hp6 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded11.part6 (-61887615425 : ℤ) (-61581241091 : ℤ) SegmentCellsBounded11.cover6
    have hp7 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded11.part7 (-61581241091 : ℤ) (-61274866757 : ℤ) SegmentCellsBounded11.cover7
    have hp8 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded11.part8 (-61274866757 : ℤ) (-60968492423 : ℤ) SegmentCellsBounded11.cover8
    have hp9 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded11.part9 (-60968492423 : ℤ) (-60662118090 : ℤ) SegmentCellsBounded11.cover9
    have hp10 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded11.part10 (-60662118090 : ℤ) (-60355743756 : ℤ) SegmentCellsBounded11.cover10
    have hp11 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded11.part11 (-60355743756 : ℤ) (-60049369422 : ℤ) SegmentCellsBounded11.cover11
    have hp12 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded11.part12 (-60049369422 : ℤ) (-59742995088 : ℤ) SegmentCellsBounded11.cover12
    have hp13 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded11.part13 (-59742995088 : ℤ) (-59436620755 : ℤ) SegmentCellsBounded11.cover13
    have hp14 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded11.part14 (-59436620755 : ℤ) (-59130246421 : ℤ) SegmentCellsBounded11.cover14
    have hp15 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded11.part15 (-59130246421 : ℤ) (-58823872087 : ℤ) SegmentCellsBounded11.cover15
    simp only [SegmentCellsBounded11.cells,List.map_append,List.append_assoc]
    exact (intervalCovers_append hp0 (intervalCovers_append hp1 (intervalCovers_append hp2 (intervalCovers_append hp3 (intervalCovers_append hp4 (intervalCovers_append hp5 (intervalCovers_append hp6 (intervalCovers_append hp7 (intervalCovers_append hp8 (intervalCovers_append hp9 (intervalCovers_append hp10 (intervalCovers_append hp11 (intervalCovers_append hp12 (intervalCovers_append hp13 (intervalCovers_append hp14 hp15 (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num))
  have h12 : IntervalCovers (SegmentCellsBounded12.cells.map QuarterContour.axisInterval) ((SegmentCellsBounded12.lower : ℚ)/2^40) ((SegmentCellsBounded12.upper : ℚ)/2^40) := by
    have hp0 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded12.part0 (-58823872087 : ℤ) (-58517497753 : ℤ) SegmentCellsBounded12.cover0
    have hp1 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded12.part1 (-58517497753 : ℤ) (-58211123419 : ℤ) SegmentCellsBounded12.cover1
    have hp2 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded12.part2 (-58211123419 : ℤ) (-57904749086 : ℤ) SegmentCellsBounded12.cover2
    have hp3 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded12.part3 (-57904749086 : ℤ) (-57598374752 : ℤ) SegmentCellsBounded12.cover3
    have hp4 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded12.part4 (-57598374752 : ℤ) (-57292000418 : ℤ) SegmentCellsBounded12.cover4
    have hp5 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded12.part5 (-57292000418 : ℤ) (-56985626084 : ℤ) SegmentCellsBounded12.cover5
    have hp6 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded12.part6 (-56985626084 : ℤ) (-56679251751 : ℤ) SegmentCellsBounded12.cover6
    have hp7 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded12.part7 (-56679251751 : ℤ) (-56372877417 : ℤ) SegmentCellsBounded12.cover7
    have hp8 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded12.part8 (-56372877417 : ℤ) (-56066503083 : ℤ) SegmentCellsBounded12.cover8
    have hp9 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded12.part9 (-56066503083 : ℤ) (-55760128749 : ℤ) SegmentCellsBounded12.cover9
    have hp10 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded12.part10 (-55760128749 : ℤ) (-55453754415 : ℤ) SegmentCellsBounded12.cover10
    have hp11 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded12.part11 (-55453754415 : ℤ) (-55147380082 : ℤ) SegmentCellsBounded12.cover11
    have hp12 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded12.part12 (-55147380082 : ℤ) (-54841005748 : ℤ) SegmentCellsBounded12.cover12
    have hp13 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded12.part13 (-54841005748 : ℤ) (-54534631414 : ℤ) SegmentCellsBounded12.cover13
    have hp14 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded12.part14 (-54534631414 : ℤ) (-54228257080 : ℤ) SegmentCellsBounded12.cover14
    have hp15 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded12.part15 (-54228257080 : ℤ) (-53921882746 : ℤ) SegmentCellsBounded12.cover15
    simp only [SegmentCellsBounded12.cells,List.map_append,List.append_assoc]
    exact (intervalCovers_append hp0 (intervalCovers_append hp1 (intervalCovers_append hp2 (intervalCovers_append hp3 (intervalCovers_append hp4 (intervalCovers_append hp5 (intervalCovers_append hp6 (intervalCovers_append hp7 (intervalCovers_append hp8 (intervalCovers_append hp9 (intervalCovers_append hp10 (intervalCovers_append hp11 (intervalCovers_append hp12 (intervalCovers_append hp13 (intervalCovers_append hp14 hp15 (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num))
  have h13 : IntervalCovers (SegmentCellsBounded13.cells.map QuarterContour.axisInterval) ((SegmentCellsBounded13.lower : ℚ)/2^40) ((SegmentCellsBounded13.upper : ℚ)/2^40) := by
    have hp0 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded13.part0 (-53921882746 : ℤ) (-53615508413 : ℤ) SegmentCellsBounded13.cover0
    have hp1 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded13.part1 (-53615508413 : ℤ) (-53309134079 : ℤ) SegmentCellsBounded13.cover1
    have hp2 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded13.part2 (-53309134079 : ℤ) (-53002759745 : ℤ) SegmentCellsBounded13.cover2
    have hp3 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded13.part3 (-53002759745 : ℤ) (-52696385411 : ℤ) SegmentCellsBounded13.cover3
    have hp4 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded13.part4 (-52696385411 : ℤ) (-52390011078 : ℤ) SegmentCellsBounded13.cover4
    have hp5 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded13.part5 (-52390011078 : ℤ) (-52083636744 : ℤ) SegmentCellsBounded13.cover5
    have hp6 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded13.part6 (-52083636744 : ℤ) (-51777262410 : ℤ) SegmentCellsBounded13.cover6
    have hp7 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded13.part7 (-51777262410 : ℤ) (-51470888076 : ℤ) SegmentCellsBounded13.cover7
    have hp8 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded13.part8 (-51470888076 : ℤ) (-51164513742 : ℤ) SegmentCellsBounded13.cover8
    have hp9 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded13.part9 (-51164513742 : ℤ) (-50858139409 : ℤ) SegmentCellsBounded13.cover9
    have hp10 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded13.part10 (-50858139409 : ℤ) (-50551765075 : ℤ) SegmentCellsBounded13.cover10
    have hp11 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded13.part11 (-50551765075 : ℤ) (-50245390741 : ℤ) SegmentCellsBounded13.cover11
    have hp12 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded13.part12 (-50245390741 : ℤ) (-49939016407 : ℤ) SegmentCellsBounded13.cover12
    have hp13 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded13.part13 (-49939016407 : ℤ) (-49632642073 : ℤ) SegmentCellsBounded13.cover13
    have hp14 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded13.part14 (-49632642073 : ℤ) (-49326267740 : ℤ) SegmentCellsBounded13.cover14
    have hp15 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded13.part15 (-49326267740 : ℤ) (-49019893406 : ℤ) SegmentCellsBounded13.cover15
    simp only [SegmentCellsBounded13.cells,List.map_append,List.append_assoc]
    exact (intervalCovers_append hp0 (intervalCovers_append hp1 (intervalCovers_append hp2 (intervalCovers_append hp3 (intervalCovers_append hp4 (intervalCovers_append hp5 (intervalCovers_append hp6 (intervalCovers_append hp7 (intervalCovers_append hp8 (intervalCovers_append hp9 (intervalCovers_append hp10 (intervalCovers_append hp11 (intervalCovers_append hp12 (intervalCovers_append hp13 (intervalCovers_append hp14 hp15 (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num))
  have h14 : IntervalCovers (SegmentCellsBounded14.cells.map QuarterContour.axisInterval) ((SegmentCellsBounded14.lower : ℚ)/2^40) ((SegmentCellsBounded14.upper : ℚ)/2^40) := by
    have hp0 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded14.part0 (-49019893406 : ℤ) (-48713519072 : ℤ) SegmentCellsBounded14.cover0
    have hp1 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded14.part1 (-48713519072 : ℤ) (-48407144738 : ℤ) SegmentCellsBounded14.cover1
    have hp2 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded14.part2 (-48407144738 : ℤ) (-48100770405 : ℤ) SegmentCellsBounded14.cover2
    have hp3 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded14.part3 (-48100770405 : ℤ) (-47794396071 : ℤ) SegmentCellsBounded14.cover3
    have hp4 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded14.part4 (-47794396071 : ℤ) (-47488021737 : ℤ) SegmentCellsBounded14.cover4
    have hp5 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded14.part5 (-47488021737 : ℤ) (-47181647403 : ℤ) SegmentCellsBounded14.cover5
    have hp6 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded14.part6 (-47181647403 : ℤ) (-46875273069 : ℤ) SegmentCellsBounded14.cover6
    have hp7 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded14.part7 (-46875273069 : ℤ) (-46568898736 : ℤ) SegmentCellsBounded14.cover7
    have hp8 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded14.part8 (-46568898736 : ℤ) (-46262524402 : ℤ) SegmentCellsBounded14.cover8
    have hp9 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded14.part9 (-46262524402 : ℤ) (-45956150068 : ℤ) SegmentCellsBounded14.cover9
    have hp10 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded14.part10 (-45956150068 : ℤ) (-45649775734 : ℤ) SegmentCellsBounded14.cover10
    have hp11 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded14.part11 (-45649775734 : ℤ) (-45343401401 : ℤ) SegmentCellsBounded14.cover11
    have hp12 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded14.part12 (-45343401401 : ℤ) (-45037027067 : ℤ) SegmentCellsBounded14.cover12
    have hp13 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded14.part13 (-45037027067 : ℤ) (-44730652733 : ℤ) SegmentCellsBounded14.cover13
    have hp14 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded14.part14 (-44730652733 : ℤ) (-44424278399 : ℤ) SegmentCellsBounded14.cover14
    have hp15 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded14.part15 (-44424278399 : ℤ) (-44117904065 : ℤ) SegmentCellsBounded14.cover15
    simp only [SegmentCellsBounded14.cells,List.map_append,List.append_assoc]
    exact (intervalCovers_append hp0 (intervalCovers_append hp1 (intervalCovers_append hp2 (intervalCovers_append hp3 (intervalCovers_append hp4 (intervalCovers_append hp5 (intervalCovers_append hp6 (intervalCovers_append hp7 (intervalCovers_append hp8 (intervalCovers_append hp9 (intervalCovers_append hp10 (intervalCovers_append hp11 (intervalCovers_append hp12 (intervalCovers_append hp13 (intervalCovers_append hp14 hp15 (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num))
  have h15 : IntervalCovers (SegmentCellsBounded15.cells.map QuarterContour.axisInterval) ((SegmentCellsBounded15.lower : ℚ)/2^40) ((SegmentCellsBounded15.upper : ℚ)/2^40) := by
    have hp0 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded15.part0 (-44117904065 : ℤ) (-43811529732 : ℤ) SegmentCellsBounded15.cover0
    have hp1 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded15.part1 (-43811529732 : ℤ) (-43505155398 : ℤ) SegmentCellsBounded15.cover1
    have hp2 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded15.part2 (-43505155398 : ℤ) (-43198781064 : ℤ) SegmentCellsBounded15.cover2
    have hp3 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded15.part3 (-43198781064 : ℤ) (-42892406730 : ℤ) SegmentCellsBounded15.cover3
    have hp4 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded15.part4 (-42892406730 : ℤ) (-42586032396 : ℤ) SegmentCellsBounded15.cover4
    have hp5 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded15.part5 (-42586032396 : ℤ) (-42279658063 : ℤ) SegmentCellsBounded15.cover5
    have hp6 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded15.part6 (-42279658063 : ℤ) (-41973283729 : ℤ) SegmentCellsBounded15.cover6
    have hp7 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded15.part7 (-41973283729 : ℤ) (-41666909395 : ℤ) SegmentCellsBounded15.cover7
    have hp8 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded15.part8 (-41666909395 : ℤ) (-41360535061 : ℤ) SegmentCellsBounded15.cover8
    have hp9 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded15.part9 (-41360535061 : ℤ) (-41054160728 : ℤ) SegmentCellsBounded15.cover9
    have hp10 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded15.part10 (-41054160728 : ℤ) (-40747786394 : ℤ) SegmentCellsBounded15.cover10
    have hp11 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded15.part11 (-40747786394 : ℤ) (-40441412060 : ℤ) SegmentCellsBounded15.cover11
    have hp12 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded15.part12 (-40441412060 : ℤ) (-40135037726 : ℤ) SegmentCellsBounded15.cover12
    have hp13 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded15.part13 (-40135037726 : ℤ) (-39828663392 : ℤ) SegmentCellsBounded15.cover13
    have hp14 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded15.part14 (-39828663392 : ℤ) (-39522289059 : ℤ) SegmentCellsBounded15.cover14
    have hp15 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded15.part15 (-39522289059 : ℤ) (-39215914725 : ℤ) SegmentCellsBounded15.cover15
    simp only [SegmentCellsBounded15.cells,List.map_append,List.append_assoc]
    exact (intervalCovers_append hp0 (intervalCovers_append hp1 (intervalCovers_append hp2 (intervalCovers_append hp3 (intervalCovers_append hp4 (intervalCovers_append hp5 (intervalCovers_append hp6 (intervalCovers_append hp7 (intervalCovers_append hp8 (intervalCovers_append hp9 (intervalCovers_append hp10 (intervalCovers_append hp11 (intervalCovers_append hp12 (intervalCovers_append hp13 (intervalCovers_append hp14 hp15 (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num))
  have h16 : IntervalCovers (SegmentCellsBounded16.cells.map QuarterContour.axisInterval) ((SegmentCellsBounded16.lower : ℚ)/2^40) ((SegmentCellsBounded16.upper : ℚ)/2^40) := by
    have hp0 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded16.part0 (-39215914725 : ℤ) (-38909540391 : ℤ) SegmentCellsBounded16.cover0
    have hp1 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded16.part1 (-38909540391 : ℤ) (-38603166057 : ℤ) SegmentCellsBounded16.cover1
    have hp2 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded16.part2 (-38603166057 : ℤ) (-38296791723 : ℤ) SegmentCellsBounded16.cover2
    have hp3 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded16.part3 (-38296791723 : ℤ) (-37990417390 : ℤ) SegmentCellsBounded16.cover3
    have hp4 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded16.part4 (-37990417390 : ℤ) (-37684043056 : ℤ) SegmentCellsBounded16.cover4
    have hp5 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded16.part5 (-37684043056 : ℤ) (-37377668722 : ℤ) SegmentCellsBounded16.cover5
    have hp6 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded16.part6 (-37377668722 : ℤ) (-37071294388 : ℤ) SegmentCellsBounded16.cover6
    have hp7 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded16.part7 (-37071294388 : ℤ) (-36764920055 : ℤ) SegmentCellsBounded16.cover7
    have hp8 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded16.part8 (-36764920055 : ℤ) (-36458545721 : ℤ) SegmentCellsBounded16.cover8
    have hp9 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded16.part9 (-36458545721 : ℤ) (-36152171387 : ℤ) SegmentCellsBounded16.cover9
    have hp10 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded16.part10 (-36152171387 : ℤ) (-35845797053 : ℤ) SegmentCellsBounded16.cover10
    have hp11 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded16.part11 (-35845797053 : ℤ) (-35539422719 : ℤ) SegmentCellsBounded16.cover11
    have hp12 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded16.part12 (-35539422719 : ℤ) (-35233048386 : ℤ) SegmentCellsBounded16.cover12
    have hp13 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded16.part13 (-35233048386 : ℤ) (-34926674052 : ℤ) SegmentCellsBounded16.cover13
    have hp14 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded16.part14 (-34926674052 : ℤ) (-34620299718 : ℤ) SegmentCellsBounded16.cover14
    have hp15 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded16.part15 (-34620299718 : ℤ) (-34313925384 : ℤ) SegmentCellsBounded16.cover15
    simp only [SegmentCellsBounded16.cells,List.map_append,List.append_assoc]
    exact (intervalCovers_append hp0 (intervalCovers_append hp1 (intervalCovers_append hp2 (intervalCovers_append hp3 (intervalCovers_append hp4 (intervalCovers_append hp5 (intervalCovers_append hp6 (intervalCovers_append hp7 (intervalCovers_append hp8 (intervalCovers_append hp9 (intervalCovers_append hp10 (intervalCovers_append hp11 (intervalCovers_append hp12 (intervalCovers_append hp13 (intervalCovers_append hp14 hp15 (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num))
  have h17 : IntervalCovers (SegmentCellsBounded17.cells.map QuarterContour.axisInterval) ((SegmentCellsBounded17.lower : ℚ)/2^40) ((SegmentCellsBounded17.upper : ℚ)/2^40) := by
    have hp0 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded17.part0 (-34313925384 : ℤ) (-34007551051 : ℤ) SegmentCellsBounded17.cover0
    have hp1 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded17.part1 (-34007551051 : ℤ) (-33701176717 : ℤ) SegmentCellsBounded17.cover1
    have hp2 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded17.part2 (-33701176717 : ℤ) (-33394802383 : ℤ) SegmentCellsBounded17.cover2
    have hp3 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded17.part3 (-33394802383 : ℤ) (-33088428049 : ℤ) SegmentCellsBounded17.cover3
    have hp4 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded17.part4 (-33088428049 : ℤ) (-32782053715 : ℤ) SegmentCellsBounded17.cover4
    have hp5 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded17.part5 (-32782053715 : ℤ) (-32475679382 : ℤ) SegmentCellsBounded17.cover5
    have hp6 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded17.part6 (-32475679382 : ℤ) (-32169305048 : ℤ) SegmentCellsBounded17.cover6
    have hp7 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded17.part7 (-32169305048 : ℤ) (-31862930714 : ℤ) SegmentCellsBounded17.cover7
    have hp8 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded17.part8 (-31862930714 : ℤ) (-31556556380 : ℤ) SegmentCellsBounded17.cover8
    have hp9 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded17.part9 (-31556556380 : ℤ) (-31250182046 : ℤ) SegmentCellsBounded17.cover9
    have hp10 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded17.part10 (-31250182046 : ℤ) (-30943807713 : ℤ) SegmentCellsBounded17.cover10
    have hp11 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded17.part11 (-30943807713 : ℤ) (-30637433379 : ℤ) SegmentCellsBounded17.cover11
    have hp12 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded17.part12 (-30637433379 : ℤ) (-30331059045 : ℤ) SegmentCellsBounded17.cover12
    have hp13 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded17.part13 (-30331059045 : ℤ) (-30024684711 : ℤ) SegmentCellsBounded17.cover13
    have hp14 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded17.part14 (-30024684711 : ℤ) (-29718310378 : ℤ) SegmentCellsBounded17.cover14
    have hp15 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded17.part15 (-29718310378 : ℤ) (-29411936044 : ℤ) SegmentCellsBounded17.cover15
    simp only [SegmentCellsBounded17.cells,List.map_append,List.append_assoc]
    exact (intervalCovers_append hp0 (intervalCovers_append hp1 (intervalCovers_append hp2 (intervalCovers_append hp3 (intervalCovers_append hp4 (intervalCovers_append hp5 (intervalCovers_append hp6 (intervalCovers_append hp7 (intervalCovers_append hp8 (intervalCovers_append hp9 (intervalCovers_append hp10 (intervalCovers_append hp11 (intervalCovers_append hp12 (intervalCovers_append hp13 (intervalCovers_append hp14 hp15 (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num))
  have h18 : IntervalCovers (SegmentCellsBounded18.cells.map QuarterContour.axisInterval) ((SegmentCellsBounded18.lower : ℚ)/2^40) ((SegmentCellsBounded18.upper : ℚ)/2^40) := by
    have hp0 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded18.part0 (-29411936044 : ℤ) (-29105561710 : ℤ) SegmentCellsBounded18.cover0
    have hp1 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded18.part1 (-29105561710 : ℤ) (-28799187376 : ℤ) SegmentCellsBounded18.cover1
    have hp2 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded18.part2 (-28799187376 : ℤ) (-28492813042 : ℤ) SegmentCellsBounded18.cover2
    have hp3 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded18.part3 (-28492813042 : ℤ) (-28186438709 : ℤ) SegmentCellsBounded18.cover3
    have hp4 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded18.part4 (-28186438709 : ℤ) (-27880064375 : ℤ) SegmentCellsBounded18.cover4
    have hp5 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded18.part5 (-27880064375 : ℤ) (-27573690041 : ℤ) SegmentCellsBounded18.cover5
    have hp6 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded18.part6 (-27573690041 : ℤ) (-27267315707 : ℤ) SegmentCellsBounded18.cover6
    have hp7 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded18.part7 (-27267315707 : ℤ) (-26960941373 : ℤ) SegmentCellsBounded18.cover7
    have hp8 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded18.part8 (-26960941373 : ℤ) (-26654567040 : ℤ) SegmentCellsBounded18.cover8
    have hp9 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded18.part9 (-26654567040 : ℤ) (-26348192706 : ℤ) SegmentCellsBounded18.cover9
    have hp10 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded18.part10 (-26348192706 : ℤ) (-26041818372 : ℤ) SegmentCellsBounded18.cover10
    have hp11 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded18.part11 (-26041818372 : ℤ) (-25735444038 : ℤ) SegmentCellsBounded18.cover11
    have hp12 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded18.part12 (-25735444038 : ℤ) (-25429069705 : ℤ) SegmentCellsBounded18.cover12
    have hp13 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded18.part13 (-25429069705 : ℤ) (-25122695371 : ℤ) SegmentCellsBounded18.cover13
    have hp14 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded18.part14 (-25122695371 : ℤ) (-24816321037 : ℤ) SegmentCellsBounded18.cover14
    have hp15 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded18.part15 (-24816321037 : ℤ) (-24509946703 : ℤ) SegmentCellsBounded18.cover15
    simp only [SegmentCellsBounded18.cells,List.map_append,List.append_assoc]
    exact (intervalCovers_append hp0 (intervalCovers_append hp1 (intervalCovers_append hp2 (intervalCovers_append hp3 (intervalCovers_append hp4 (intervalCovers_append hp5 (intervalCovers_append hp6 (intervalCovers_append hp7 (intervalCovers_append hp8 (intervalCovers_append hp9 (intervalCovers_append hp10 (intervalCovers_append hp11 (intervalCovers_append hp12 (intervalCovers_append hp13 (intervalCovers_append hp14 hp15 (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num))
  have h19 : IntervalCovers (SegmentCellsBounded19.cells.map QuarterContour.axisInterval) ((SegmentCellsBounded19.lower : ℚ)/2^40) ((SegmentCellsBounded19.upper : ℚ)/2^40) := by
    have hp0 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded19.part0 (-24509946703 : ℤ) (-24203572369 : ℤ) SegmentCellsBounded19.cover0
    have hp1 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded19.part1 (-24203572369 : ℤ) (-23897198036 : ℤ) SegmentCellsBounded19.cover1
    have hp2 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded19.part2 (-23897198036 : ℤ) (-23590823702 : ℤ) SegmentCellsBounded19.cover2
    have hp3 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded19.part3 (-23590823702 : ℤ) (-23284449368 : ℤ) SegmentCellsBounded19.cover3
    have hp4 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded19.part4 (-23284449368 : ℤ) (-22978075034 : ℤ) SegmentCellsBounded19.cover4
    have hp5 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded19.part5 (-22978075034 : ℤ) (-22671700701 : ℤ) SegmentCellsBounded19.cover5
    have hp6 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded19.part6 (-22671700701 : ℤ) (-22365326367 : ℤ) SegmentCellsBounded19.cover6
    have hp7 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded19.part7 (-22365326367 : ℤ) (-22058952033 : ℤ) SegmentCellsBounded19.cover7
    have hp8 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded19.part8 (-22058952033 : ℤ) (-21752577699 : ℤ) SegmentCellsBounded19.cover8
    have hp9 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded19.part9 (-21752577699 : ℤ) (-21446203365 : ℤ) SegmentCellsBounded19.cover9
    have hp10 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded19.part10 (-21446203365 : ℤ) (-21139829032 : ℤ) SegmentCellsBounded19.cover10
    have hp11 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded19.part11 (-21139829032 : ℤ) (-20833454698 : ℤ) SegmentCellsBounded19.cover11
    have hp12 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded19.part12 (-20833454698 : ℤ) (-20527080364 : ℤ) SegmentCellsBounded19.cover12
    have hp13 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded19.part13 (-20527080364 : ℤ) (-20220706030 : ℤ) SegmentCellsBounded19.cover13
    have hp14 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded19.part14 (-20220706030 : ℤ) (-19914331696 : ℤ) SegmentCellsBounded19.cover14
    have hp15 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded19.part15 (-19914331696 : ℤ) (-19607957363 : ℤ) SegmentCellsBounded19.cover15
    simp only [SegmentCellsBounded19.cells,List.map_append,List.append_assoc]
    exact (intervalCovers_append hp0 (intervalCovers_append hp1 (intervalCovers_append hp2 (intervalCovers_append hp3 (intervalCovers_append hp4 (intervalCovers_append hp5 (intervalCovers_append hp6 (intervalCovers_append hp7 (intervalCovers_append hp8 (intervalCovers_append hp9 (intervalCovers_append hp10 (intervalCovers_append hp11 (intervalCovers_append hp12 (intervalCovers_append hp13 (intervalCovers_append hp14 hp15 (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num))
  have h20 : IntervalCovers (SegmentCellsBounded20.cells.map QuarterContour.axisInterval) ((SegmentCellsBounded20.lower : ℚ)/2^40) ((SegmentCellsBounded20.upper : ℚ)/2^40) := by
    have hp0 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded20.part0 (-19607957363 : ℤ) (-19301583029 : ℤ) SegmentCellsBounded20.cover0
    have hp1 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded20.part1 (-19301583029 : ℤ) (-18995208695 : ℤ) SegmentCellsBounded20.cover1
    have hp2 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded20.part2 (-18995208695 : ℤ) (-18688834361 : ℤ) SegmentCellsBounded20.cover2
    have hp3 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded20.part3 (-18688834361 : ℤ) (-18382460028 : ℤ) SegmentCellsBounded20.cover3
    have hp4 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded20.part4 (-18382460028 : ℤ) (-18076085694 : ℤ) SegmentCellsBounded20.cover4
    have hp5 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded20.part5 (-18076085694 : ℤ) (-17769711360 : ℤ) SegmentCellsBounded20.cover5
    have hp6 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded20.part6 (-17769711360 : ℤ) (-17463337026 : ℤ) SegmentCellsBounded20.cover6
    have hp7 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded20.part7 (-17463337026 : ℤ) (-17156962692 : ℤ) SegmentCellsBounded20.cover7
    have hp8 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded20.part8 (-17156962692 : ℤ) (-16850588359 : ℤ) SegmentCellsBounded20.cover8
    have hp9 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded20.part9 (-16850588359 : ℤ) (-16544214025 : ℤ) SegmentCellsBounded20.cover9
    have hp10 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded20.part10 (-16544214025 : ℤ) (-16237839691 : ℤ) SegmentCellsBounded20.cover10
    have hp11 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded20.part11 (-16237839691 : ℤ) (-15931465357 : ℤ) SegmentCellsBounded20.cover11
    have hp12 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded20.part12 (-15931465357 : ℤ) (-15625091023 : ℤ) SegmentCellsBounded20.cover12
    have hp13 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded20.part13 (-15625091023 : ℤ) (-15318716690 : ℤ) SegmentCellsBounded20.cover13
    have hp14 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded20.part14 (-15318716690 : ℤ) (-15012342356 : ℤ) SegmentCellsBounded20.cover14
    have hp15 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded20.part15 (-15012342356 : ℤ) (-14705968022 : ℤ) SegmentCellsBounded20.cover15
    simp only [SegmentCellsBounded20.cells,List.map_append,List.append_assoc]
    exact (intervalCovers_append hp0 (intervalCovers_append hp1 (intervalCovers_append hp2 (intervalCovers_append hp3 (intervalCovers_append hp4 (intervalCovers_append hp5 (intervalCovers_append hp6 (intervalCovers_append hp7 (intervalCovers_append hp8 (intervalCovers_append hp9 (intervalCovers_append hp10 (intervalCovers_append hp11 (intervalCovers_append hp12 (intervalCovers_append hp13 (intervalCovers_append hp14 hp15 (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num))
  have h21 : IntervalCovers (SegmentCellsBounded21.cells.map QuarterContour.axisInterval) ((SegmentCellsBounded21.lower : ℚ)/2^40) ((SegmentCellsBounded21.upper : ℚ)/2^40) := by
    have hp0 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded21.part0 (-14705968022 : ℤ) (-14399593688 : ℤ) SegmentCellsBounded21.cover0
    have hp1 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded21.part1 (-14399593688 : ℤ) (-14093219355 : ℤ) SegmentCellsBounded21.cover1
    have hp2 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded21.part2 (-14093219355 : ℤ) (-13786845021 : ℤ) SegmentCellsBounded21.cover2
    have hp3 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded21.part3 (-13786845021 : ℤ) (-13480470687 : ℤ) SegmentCellsBounded21.cover3
    have hp4 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded21.part4 (-13480470687 : ℤ) (-13174096353 : ℤ) SegmentCellsBounded21.cover4
    have hp5 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded21.part5 (-13174096353 : ℤ) (-12867722019 : ℤ) SegmentCellsBounded21.cover5
    have hp6 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded21.part6 (-12867722019 : ℤ) (-12561347686 : ℤ) SegmentCellsBounded21.cover6
    have hp7 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded21.part7 (-12561347686 : ℤ) (-12254973352 : ℤ) SegmentCellsBounded21.cover7
    have hp8 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded21.part8 (-12254973352 : ℤ) (-11948599018 : ℤ) SegmentCellsBounded21.cover8
    have hp9 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded21.part9 (-11948599018 : ℤ) (-11642224684 : ℤ) SegmentCellsBounded21.cover9
    have hp10 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded21.part10 (-11642224684 : ℤ) (-11335850351 : ℤ) SegmentCellsBounded21.cover10
    have hp11 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded21.part11 (-11335850351 : ℤ) (-11029476017 : ℤ) SegmentCellsBounded21.cover11
    have hp12 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded21.part12 (-11029476017 : ℤ) (-10723101683 : ℤ) SegmentCellsBounded21.cover12
    have hp13 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded21.part13 (-10723101683 : ℤ) (-10416727349 : ℤ) SegmentCellsBounded21.cover13
    have hp14 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded21.part14 (-10416727349 : ℤ) (-10110353015 : ℤ) SegmentCellsBounded21.cover14
    have hp15 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded21.part15 (-10110353015 : ℤ) (-9803978682 : ℤ) SegmentCellsBounded21.cover15
    simp only [SegmentCellsBounded21.cells,List.map_append,List.append_assoc]
    exact (intervalCovers_append hp0 (intervalCovers_append hp1 (intervalCovers_append hp2 (intervalCovers_append hp3 (intervalCovers_append hp4 (intervalCovers_append hp5 (intervalCovers_append hp6 (intervalCovers_append hp7 (intervalCovers_append hp8 (intervalCovers_append hp9 (intervalCovers_append hp10 (intervalCovers_append hp11 (intervalCovers_append hp12 (intervalCovers_append hp13 (intervalCovers_append hp14 hp15 (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num))
  have h22 : IntervalCovers (SegmentCellsBounded22.cells.map QuarterContour.axisInterval) ((SegmentCellsBounded22.lower : ℚ)/2^40) ((SegmentCellsBounded22.upper : ℚ)/2^40) := by
    have hp0 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded22.part0 (-9803978682 : ℤ) (-9497604348 : ℤ) SegmentCellsBounded22.cover0
    have hp1 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded22.part1 (-9497604348 : ℤ) (-9191230014 : ℤ) SegmentCellsBounded22.cover1
    have hp2 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded22.part2 (-9191230014 : ℤ) (-8884855680 : ℤ) SegmentCellsBounded22.cover2
    have hp3 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded22.part3 (-8884855680 : ℤ) (-8578481346 : ℤ) SegmentCellsBounded22.cover3
    have hp4 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded22.part4 (-8578481346 : ℤ) (-8272107013 : ℤ) SegmentCellsBounded22.cover4
    have hp5 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded22.part5 (-8272107013 : ℤ) (-7965732679 : ℤ) SegmentCellsBounded22.cover5
    have hp6 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded22.part6 (-7965732679 : ℤ) (-7659358345 : ℤ) SegmentCellsBounded22.cover6
    have hp7 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded22.part7 (-7659358345 : ℤ) (-7352984011 : ℤ) SegmentCellsBounded22.cover7
    have hp8 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded22.part8 (-7352984011 : ℤ) (-7046609678 : ℤ) SegmentCellsBounded22.cover8
    have hp9 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded22.part9 (-7046609678 : ℤ) (-6740235344 : ℤ) SegmentCellsBounded22.cover9
    have hp10 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded22.part10 (-6740235344 : ℤ) (-6433861010 : ℤ) SegmentCellsBounded22.cover10
    have hp11 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded22.part11 (-6433861010 : ℤ) (-6127486676 : ℤ) SegmentCellsBounded22.cover11
    have hp12 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded22.part12 (-6127486676 : ℤ) (-5821112342 : ℤ) SegmentCellsBounded22.cover12
    have hp13 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded22.part13 (-5821112342 : ℤ) (-5514738009 : ℤ) SegmentCellsBounded22.cover13
    have hp14 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded22.part14 (-5514738009 : ℤ) (-5208363675 : ℤ) SegmentCellsBounded22.cover14
    have hp15 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded22.part15 (-5208363675 : ℤ) (-4901989341 : ℤ) SegmentCellsBounded22.cover15
    simp only [SegmentCellsBounded22.cells,List.map_append,List.append_assoc]
    exact (intervalCovers_append hp0 (intervalCovers_append hp1 (intervalCovers_append hp2 (intervalCovers_append hp3 (intervalCovers_append hp4 (intervalCovers_append hp5 (intervalCovers_append hp6 (intervalCovers_append hp7 (intervalCovers_append hp8 (intervalCovers_append hp9 (intervalCovers_append hp10 (intervalCovers_append hp11 (intervalCovers_append hp12 (intervalCovers_append hp13 (intervalCovers_append hp14 hp15 (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num))
  have h23 : IntervalCovers (SegmentCellsBounded23.cells.map QuarterContour.axisInterval) ((SegmentCellsBounded23.lower : ℚ)/2^40) ((SegmentCellsBounded23.upper : ℚ)/2^40) := by
    have hp0 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded23.part0 (-4901989341 : ℤ) (-4595615007 : ℤ) SegmentCellsBounded23.cover0
    have hp1 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded23.part1 (-4595615007 : ℤ) (-4289240673 : ℤ) SegmentCellsBounded23.cover1
    have hp2 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded23.part2 (-4289240673 : ℤ) (-3982866340 : ℤ) SegmentCellsBounded23.cover2
    have hp3 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded23.part3 (-3982866340 : ℤ) (-3676492006 : ℤ) SegmentCellsBounded23.cover3
    have hp4 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded23.part4 (-3676492006 : ℤ) (-3370117672 : ℤ) SegmentCellsBounded23.cover4
    have hp5 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded23.part5 (-3370117672 : ℤ) (-3063743338 : ℤ) SegmentCellsBounded23.cover5
    have hp6 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded23.part6 (-3063743338 : ℤ) (-2757369005 : ℤ) SegmentCellsBounded23.cover6
    have hp7 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded23.part7 (-2757369005 : ℤ) (-2450994671 : ℤ) SegmentCellsBounded23.cover7
    have hp8 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded23.part8 (-2450994671 : ℤ) (-2144620337 : ℤ) SegmentCellsBounded23.cover8
    have hp9 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded23.part9 (-2144620337 : ℤ) (-1838246003 : ℤ) SegmentCellsBounded23.cover9
    have hp10 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded23.part10 (-1838246003 : ℤ) (-1531871669 : ℤ) SegmentCellsBounded23.cover10
    have hp11 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded23.part11 (-1531871669 : ℤ) (-1225497336 : ℤ) SegmentCellsBounded23.cover11
    have hp12 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded23.part12 (-1225497336 : ℤ) (-919123002 : ℤ) SegmentCellsBounded23.cover12
    have hp13 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded23.part13 (-919123002 : ℤ) (-612748668 : ℤ) SegmentCellsBounded23.cover13
    have hp14 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded23.part14 (-612748668 : ℤ) (-306374334 : ℤ) SegmentCellsBounded23.cover14
    have hp15 := SegmentLedgerBridge.intervalCovers SegmentCellsBounded23.part15 (-306374334 : ℤ) (0 : ℤ) SegmentCellsBounded23.cover15
    simp only [SegmentCellsBounded23.cells,List.map_append,List.append_assoc]
    exact (intervalCovers_append hp0 (intervalCovers_append hp1 (intervalCovers_append hp2 (intervalCovers_append hp3 (intervalCovers_append hp4 (intervalCovers_append hp5 (intervalCovers_append hp6 (intervalCovers_append hp7 (intervalCovers_append hp8 (intervalCovers_append hp9 (intervalCovers_append hp10 (intervalCovers_append hp11 (intervalCovers_append hp12 (intervalCovers_append hp13 (intervalCovers_append hp14 hp15 (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num))
  simp only [cells,List.map_append,List.append_assoc]
  exact intervalCovers_restrict (intervalCovers_append h0 (intervalCovers_append h1 (intervalCovers_append h2 (intervalCovers_append h3 (intervalCovers_append h4 (intervalCovers_append h5 (intervalCovers_append h6 (intervalCovers_append h7 (intervalCovers_append h8 (intervalCovers_append h9 (intervalCovers_append h10 (intervalCovers_append h11 (intervalCovers_append h12 (intervalCovers_append h13 (intervalCovers_append h14 (intervalCovers_append h15 (intervalCovers_append h16 (intervalCovers_append h17 (intervalCovers_append h18 (intervalCovers_append h19 (intervalCovers_append h20 (intervalCovers_append h21 (intervalCovers_append h22 h23 (by norm_num [SegmentCellsBounded22.upper,SegmentCellsBounded23.lower])) (by norm_num [SegmentCellsBounded21.upper,SegmentCellsBounded22.lower])) (by norm_num [SegmentCellsBounded20.upper,SegmentCellsBounded21.lower])) (by norm_num [SegmentCellsBounded19.upper,SegmentCellsBounded20.lower])) (by norm_num [SegmentCellsBounded18.upper,SegmentCellsBounded19.lower])) (by norm_num [SegmentCellsBounded17.upper,SegmentCellsBounded18.lower])) (by norm_num [SegmentCellsBounded16.upper,SegmentCellsBounded17.lower])) (by norm_num [SegmentCellsBounded15.upper,SegmentCellsBounded16.lower])) (by norm_num [SegmentCellsBounded14.upper,SegmentCellsBounded15.lower])) (by norm_num [SegmentCellsBounded13.upper,SegmentCellsBounded14.lower])) (by norm_num [SegmentCellsBounded12.upper,SegmentCellsBounded13.lower])) (by norm_num [SegmentCellsBounded11.upper,SegmentCellsBounded12.lower])) (by norm_num [SegmentCellsBounded10.upper,SegmentCellsBounded11.lower])) (by norm_num [SegmentCellsBounded9.upper,SegmentCellsBounded10.lower])) (by norm_num [SegmentCellsBounded8.upper,SegmentCellsBounded9.lower])) (by norm_num [SegmentCellsBounded7.upper,SegmentCellsBounded8.lower])) (by norm_num [SegmentCellsBounded6.upper,SegmentCellsBounded7.lower])) (by norm_num [SegmentCellsBounded5.upper,SegmentCellsBounded6.lower])) (by norm_num [SegmentCellsBounded4.upper,SegmentCellsBounded5.lower])) (by norm_num [SegmentCellsBounded3.upper,SegmentCellsBounded4.lower])) (by norm_num [SegmentCellsBounded2.upper,SegmentCellsBounded3.lower])) (by norm_num [SegmentCellsBounded1.upper,SegmentCellsBounded2.lower])) (by norm_num [SegmentCellsBounded0.upper,SegmentCellsBounded1.lower])) (by norm_num [SegmentCellsBounded0.lower]) (by norm_num [SegmentCellsBounded23.upper])
theorem cells_length : cells.length = 24576 := by
  simp only [cells,List.length_append,SegmentCellsBounded0.cells_length,SegmentCellsBounded1.cells_length,SegmentCellsBounded2.cells_length,SegmentCellsBounded3.cells_length,SegmentCellsBounded4.cells_length,SegmentCellsBounded5.cells_length,SegmentCellsBounded6.cells_length,SegmentCellsBounded7.cells_length,SegmentCellsBounded8.cells_length,SegmentCellsBounded9.cells_length,SegmentCellsBounded10.cells_length,SegmentCellsBounded11.cells_length,SegmentCellsBounded12.cells_length,SegmentCellsBounded13.cells_length,SegmentCellsBounded14.cells_length,SegmentCellsBounded15.cells_length,SegmentCellsBounded16.cells_length,SegmentCellsBounded17.cells_length,SegmentCellsBounded18.cells_length,SegmentCellsBounded19.cells_length,SegmentCellsBounded20.cells_length,SegmentCellsBounded21.cells_length,SegmentCellsBounded22.cells_length,SegmentCellsBounded23.cells_length]
end CatalanCore.Cert.QuarterContour.SegmentFinite
#print axioms CatalanCore.Cert.QuarterContour.SegmentFinite.shape
#print axioms CatalanCore.Cert.QuarterContour.SegmentFinite.sval_checked
#print axioms CatalanCore.Cert.QuarterContour.SegmentFinite.scost
#print axioms CatalanCore.Cert.QuarterContour.SegmentFinite.cover
