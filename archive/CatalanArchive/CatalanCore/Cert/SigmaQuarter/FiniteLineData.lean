module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Line0
public import CatalanCore.Cert.SigmaQuarter.Line1
public import CatalanCore.Cert.SigmaQuarter.Line2
public import CatalanCore.Cert.SigmaQuarter.Line3
public import CatalanCore.Cert.SigmaQuarter.Line4
public import CatalanCore.Cert.SigmaQuarter.Line5
public import CatalanCore.Cert.SigmaQuarter.Line6
public import CatalanCore.Cert.SigmaQuarter.Line7
public import CatalanCore.Cert.SigmaQuarter.Line8
public import CatalanCore.Cert.SigmaQuarter.Line9
public import CatalanCore.Cert.SigmaQuarter.Line10
public import CatalanCore.Cert.SigmaQuarter.Line11
public import CatalanCore.Cert.SigmaQuarter.Line12
public import CatalanCore.Cert.SigmaQuarter.Line13
public import CatalanCore.Cert.SigmaQuarter.Line14
public import CatalanCore.Cert.SigmaQuarter.Line15
public import CatalanCore.Cert.SigmaQuarter.Line16
public import CatalanCore.Cert.SigmaQuarter.Line17
public import CatalanCore.Cert.SigmaQuarter.Line18
public import CatalanCore.Cert.SigmaQuarter.Line19
public import CatalanCore.Cert.SigmaQuarter.Line20
public import CatalanCore.Cert.SigmaQuarter.Line21
public import CatalanCore.Cert.SigmaQuarter.Line22
public import CatalanCore.Cert.SigmaQuarter.Line23
public import CatalanCore.Cert.SigmaQuarter.Line24
public import CatalanCore.Cert.SigmaQuarter.Line25
public import CatalanCore.Cert.SigmaQuarter.Line26
public import CatalanCore.Cert.SigmaQuarter.Line27
public import CatalanCore.Cert.SigmaQuarter.Line28
public import CatalanCore.Cert.SigmaQuarter.Line29
public import CatalanCore.Cert.SigmaQuarter.Line30
public import CatalanCore.Cert.SigmaQuarter.Line31
public import CatalanCore.Cert.SigmaQuarter.Line32
public import CatalanCore.Cert.SigmaQuarter.Line33
public import CatalanCore.Cert.SigmaQuarter.Line34
public import CatalanCore.Cert.SigmaQuarter.Line35
public import CatalanCore.Cert.SigmaQuarter.Line36
public import CatalanCore.Cert.SigmaQuarter.Line37
public import CatalanCore.Cert.SigmaQuarter.Line38
public import CatalanCore.Cert.SigmaQuarter.Line39
public import CatalanCore.Cert.SigmaQuarter.Line40
public import CatalanCore.Cert.SigmaQuarter.Line41
public import CatalanCore.Cert.SigmaQuarter.Line42
public import CatalanCore.Cert.SigmaQuarter.Line43
public import CatalanCore.Cert.SigmaQuarter.Line44
public import CatalanCore.Cert.SigmaQuarter.Line45
public import CatalanCore.Cert.SigmaQuarter.Line46
public import CatalanCore.Cert.SigmaQuarter.Line47
public import CatalanCore.Cert.SigmaQuarter.Line48
public import CatalanCore.Cert.SigmaQuarter.Line49
public import CatalanCore.Cert.SigmaQuarter.Line50
public import CatalanCore.Cert.SigmaQuarter.Line51
public import CatalanCore.Cert.SigmaQuarter.Line52
public import CatalanCore.Cert.SigmaQuarter.Line53
public import CatalanCore.Cert.SigmaQuarter.Line54
public import CatalanCore.Cert.SigmaQuarter.Line55
public import CatalanCore.Cert.SigmaQuarter.Line56
public import CatalanCore.Cert.SigmaQuarter.Line57
public import CatalanCore.Cert.SigmaQuarter.Line58
public import CatalanCore.Cert.SigmaQuarter.Line59
public import CatalanCore.Cert.SigmaQuarter.Line60
public import CatalanCore.Cert.SigmaQuarter.Line61
public import CatalanCore.Cert.SigmaQuarter.Line62
public import CatalanCore.Cert.SigmaQuarter.Line63
public import CatalanCore.Cert.SigmaQuarter.Line64

public import CatalanCore.Cert.SigmaQuarter.GeometryLine00
public import CatalanCore.Cert.SigmaQuarter.GeometryLine01
public import CatalanCore.Cert.SigmaQuarter.GeometryLine02
public import CatalanCore.Cert.SigmaQuarter.GeometryLine03
public import CatalanCore.Cert.SigmaQuarter.GeometryLine04
public import CatalanCore.Cert.SigmaQuarter.GeometryLine05
public import CatalanCore.Cert.SigmaQuarter.GeometryLine06
public import CatalanCore.Cert.SigmaQuarter.GeometryLine07
public import CatalanCore.Cert.SigmaQuarter.GeometryLine08

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def lines : List Macro := Line0Data ++ (Line1Data ++ (Line2Data ++ (Line3Data ++ (Line4Data ++ (Line5Data ++ (Line6Data ++ (Line7Data ++ (Line8Data ++ (Line9Data ++ (Line10Data ++ (Line11Data ++ (Line12Data ++ (Line13Data ++ (Line14Data ++ (Line15Data ++ (Line16Data ++ (Line17Data ++ (Line18Data ++ (Line19Data ++ (Line20Data ++ (Line21Data ++ (Line22Data ++ (Line23Data ++ (Line24Data ++ (Line25Data ++ (Line26Data ++ (Line27Data ++ (Line28Data ++ (Line29Data ++ (Line30Data ++ (Line31Data ++ (Line32Data ++ (Line33Data ++ (Line34Data ++ (Line35Data ++ (Line36Data ++ (Line37Data ++ (Line38Data ++ (Line39Data ++ (Line40Data ++ (Line41Data ++ (Line42Data ++ (Line43Data ++ (Line44Data ++ (Line45Data ++ (Line46Data ++ (Line47Data ++ (Line48Data ++ (Line49Data ++ (Line50Data ++ (Line51Data ++ (Line52Data ++ (Line53Data ++ (Line54Data ++ (Line55Data ++ (Line56Data ++ (Line57Data ++ (Line58Data ++ (Line59Data ++ (Line60Data ++ (Line61Data ++ (Line62Data ++ (Line63Data ++ (Line64Data))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem lines_far : ∀ m ∈ lines, farOK pts m :=
  List.forall_mem_append.mpr ⟨Line0_farAll, List.forall_mem_append.mpr ⟨Line1_farAll, List.forall_mem_append.mpr ⟨Line2_farAll, List.forall_mem_append.mpr ⟨Line3_farAll, List.forall_mem_append.mpr ⟨Line4_farAll, List.forall_mem_append.mpr ⟨Line5_farAll, List.forall_mem_append.mpr ⟨Line6_farAll, List.forall_mem_append.mpr ⟨Line7_farAll, List.forall_mem_append.mpr ⟨Line8_farAll, List.forall_mem_append.mpr ⟨Line9_farAll, List.forall_mem_append.mpr ⟨Line10_farAll, List.forall_mem_append.mpr ⟨Line11_farAll, List.forall_mem_append.mpr ⟨Line12_farAll, List.forall_mem_append.mpr ⟨Line13_farAll, List.forall_mem_append.mpr ⟨Line14_farAll, List.forall_mem_append.mpr ⟨Line15_farAll, List.forall_mem_append.mpr ⟨Line16_farAll, List.forall_mem_append.mpr ⟨Line17_farAll, List.forall_mem_append.mpr ⟨Line18_farAll, List.forall_mem_append.mpr ⟨Line19_farAll, List.forall_mem_append.mpr ⟨Line20_farAll, List.forall_mem_append.mpr ⟨Line21_farAll, List.forall_mem_append.mpr ⟨Line22_farAll, List.forall_mem_append.mpr ⟨Line23_farAll, List.forall_mem_append.mpr ⟨Line24_farAll, List.forall_mem_append.mpr ⟨Line25_farAll, List.forall_mem_append.mpr ⟨Line26_farAll, List.forall_mem_append.mpr ⟨Line27_farAll, List.forall_mem_append.mpr ⟨Line28_farAll, List.forall_mem_append.mpr ⟨Line29_farAll, List.forall_mem_append.mpr ⟨Line30_farAll, List.forall_mem_append.mpr ⟨Line31_farAll, List.forall_mem_append.mpr ⟨Line32_farAll, List.forall_mem_append.mpr ⟨Line33_farAll, List.forall_mem_append.mpr ⟨Line34_farAll, List.forall_mem_append.mpr ⟨Line35_farAll, List.forall_mem_append.mpr ⟨Line36_farAll, List.forall_mem_append.mpr ⟨Line37_farAll, List.forall_mem_append.mpr ⟨Line38_farAll, List.forall_mem_append.mpr ⟨Line39_farAll, List.forall_mem_append.mpr ⟨Line40_farAll, List.forall_mem_append.mpr ⟨Line41_farAll, List.forall_mem_append.mpr ⟨Line42_farAll, List.forall_mem_append.mpr ⟨Line43_farAll, List.forall_mem_append.mpr ⟨Line44_farAll, List.forall_mem_append.mpr ⟨Line45_farAll, List.forall_mem_append.mpr ⟨Line46_farAll, List.forall_mem_append.mpr ⟨Line47_farAll, List.forall_mem_append.mpr ⟨Line48_farAll, List.forall_mem_append.mpr ⟨Line49_farAll, List.forall_mem_append.mpr ⟨Line50_farAll, List.forall_mem_append.mpr ⟨Line51_farAll, List.forall_mem_append.mpr ⟨Line52_farAll, List.forall_mem_append.mpr ⟨Line53_farAll, List.forall_mem_append.mpr ⟨Line54_farAll, List.forall_mem_append.mpr ⟨Line55_farAll, List.forall_mem_append.mpr ⟨Line56_farAll, List.forall_mem_append.mpr ⟨Line57_farAll, List.forall_mem_append.mpr ⟨Line58_farAll, List.forall_mem_append.mpr ⟨Line59_farAll, List.forall_mem_append.mpr ⟨Line60_farAll, List.forall_mem_append.mpr ⟨Line61_farAll, List.forall_mem_append.mpr ⟨Line62_farAll, List.forall_mem_append.mpr ⟨Line63_farAll, Line64_farAll⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem lines_ok : ∀ m ∈ lines, axisOK pts m = true :=
  List.forall_mem_append.mpr ⟨Line0_okAll, List.forall_mem_append.mpr ⟨Line1_okAll, List.forall_mem_append.mpr ⟨Line2_okAll, List.forall_mem_append.mpr ⟨Line3_okAll, List.forall_mem_append.mpr ⟨Line4_okAll, List.forall_mem_append.mpr ⟨Line5_okAll, List.forall_mem_append.mpr ⟨Line6_okAll, List.forall_mem_append.mpr ⟨Line7_okAll, List.forall_mem_append.mpr ⟨Line8_okAll, List.forall_mem_append.mpr ⟨Line9_okAll, List.forall_mem_append.mpr ⟨Line10_okAll, List.forall_mem_append.mpr ⟨Line11_okAll, List.forall_mem_append.mpr ⟨Line12_okAll, List.forall_mem_append.mpr ⟨Line13_okAll, List.forall_mem_append.mpr ⟨Line14_okAll, List.forall_mem_append.mpr ⟨Line15_okAll, List.forall_mem_append.mpr ⟨Line16_okAll, List.forall_mem_append.mpr ⟨Line17_okAll, List.forall_mem_append.mpr ⟨Line18_okAll, List.forall_mem_append.mpr ⟨Line19_okAll, List.forall_mem_append.mpr ⟨Line20_okAll, List.forall_mem_append.mpr ⟨Line21_okAll, List.forall_mem_append.mpr ⟨Line22_okAll, List.forall_mem_append.mpr ⟨Line23_okAll, List.forall_mem_append.mpr ⟨Line24_okAll, List.forall_mem_append.mpr ⟨Line25_okAll, List.forall_mem_append.mpr ⟨Line26_okAll, List.forall_mem_append.mpr ⟨Line27_okAll, List.forall_mem_append.mpr ⟨Line28_okAll, List.forall_mem_append.mpr ⟨Line29_okAll, List.forall_mem_append.mpr ⟨Line30_okAll, List.forall_mem_append.mpr ⟨Line31_okAll, List.forall_mem_append.mpr ⟨Line32_okAll, List.forall_mem_append.mpr ⟨Line33_okAll, List.forall_mem_append.mpr ⟨Line34_okAll, List.forall_mem_append.mpr ⟨Line35_okAll, List.forall_mem_append.mpr ⟨Line36_okAll, List.forall_mem_append.mpr ⟨Line37_okAll, List.forall_mem_append.mpr ⟨Line38_okAll, List.forall_mem_append.mpr ⟨Line39_okAll, List.forall_mem_append.mpr ⟨Line40_okAll, List.forall_mem_append.mpr ⟨Line41_okAll, List.forall_mem_append.mpr ⟨Line42_okAll, List.forall_mem_append.mpr ⟨Line43_okAll, List.forall_mem_append.mpr ⟨Line44_okAll, List.forall_mem_append.mpr ⟨Line45_okAll, List.forall_mem_append.mpr ⟨Line46_okAll, List.forall_mem_append.mpr ⟨Line47_okAll, List.forall_mem_append.mpr ⟨Line48_okAll, List.forall_mem_append.mpr ⟨Line49_okAll, List.forall_mem_append.mpr ⟨Line50_okAll, List.forall_mem_append.mpr ⟨Line51_okAll, List.forall_mem_append.mpr ⟨Line52_okAll, List.forall_mem_append.mpr ⟨Line53_okAll, List.forall_mem_append.mpr ⟨Line54_okAll, List.forall_mem_append.mpr ⟨Line55_okAll, List.forall_mem_append.mpr ⟨Line56_okAll, List.forall_mem_append.mpr ⟨Line57_okAll, List.forall_mem_append.mpr ⟨Line58_okAll, List.forall_mem_append.mpr ⟨Line59_okAll, List.forall_mem_append.mpr ⟨Line60_okAll, List.forall_mem_append.mpr ⟨Line61_okAll, List.forall_mem_append.mpr ⟨Line62_okAll, List.forall_mem_append.mpr ⟨Line63_okAll, Line64_okAll⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem lines_chunks : lines = lineGeo0 ++ (lineGeo1 ++ (lineGeo2 ++ (lineGeo3 ++ (lineGeo4 ++ (lineGeo5 ++ (lineGeo6 ++ (lineGeo7 ++ (lineGeo8)))))))) := by
  simp only [lines, lineGeo0, lineGeo1, lineGeo2, lineGeo3, lineGeo4, lineGeo5, lineGeo6, lineGeo7, lineGeo8, List.append_assoc]
end CatalanCore.Cert.SigmaQuarter
