module
public import CatalanCore.Cert.QuarterContour.EnergySumBlock0
public import CatalanCore.Cert.QuarterContour.EnergySumBlock1
public import CatalanCore.Cert.QuarterContour.EnergySumBlock2
public import CatalanCore.Cert.QuarterContour.EnergySumBlock3
public import CatalanCore.Cert.QuarterContour.EnergySumBlock4
public import CatalanCore.Cert.QuarterContour.EnergySumBlock5
public import CatalanCore.Cert.QuarterContour.EnergySumBlock6
public import CatalanCore.Cert.QuarterContour.EnergySumBlock7
public import CatalanCore.Cert.QuarterContour.EnergySumBlock8
public import CatalanCore.Cert.QuarterContour.EnergySumBlock9
public import CatalanCore.Cert.QuarterContour.EnergySumBlock10
public import CatalanCore.Cert.QuarterContour.EnergySumBlock11
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.EnergyExact
open CatalanCore.Cert.QuarterContour.EnergyIndexed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
def ITOT : ℤ := -1224464941202965752359140662845471452672
def Iupper : ℚ := 2391533088287042485076446607120061431/1329227995784915872903807060280344576
theorem index_partition : List.range SigmaQuarterContour.pts.length =
    [EnergySumBlock0.indices,EnergySumBlock1.indices,EnergySumBlock2.indices,EnergySumBlock3.indices,EnergySumBlock4.indices,EnergySumBlock5.indices,EnergySumBlock6.indices,EnergySumBlock7.indices,EnergySumBlock8.indices,EnergySumBlock9.indices,EnergySumBlock10.indices,EnergySumBlock11.indices].flatten := by decide +kernel
theorem energyTotal_checked : energyTotal SigmaQuarterContour.pts SigmaQuarterContour.pts = ITOT := by
  rw [energyTotal_indexed,index_partition,indexSum_flatten]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,EnergySumBlock0.checked,EnergySumBlock1.checked,EnergySumBlock2.checked,EnergySumBlock3.checked,EnergySumBlock4.checked,EnergySumBlock5.checked,EnergySumBlock6.checked,EnergySumBlock7.checked,EnergySumBlock8.checked,EnergySumBlock9.checked,EnergySumBlock10.checked,EnergySumBlock11.checked]
  decide +kernel
theorem energy_le_Iupper : CatalanLambda.Decay.Irho (1/2048 : ℝ)
    (QuarterContour.positions SigmaQuarterContour.pts) (QuarterContour.masses SigmaQuarterContour.pts) ≤ (Iupper : ℝ) := by
  calc
    _ ≤ -(ITOT : ℝ)/2^129 := by simpa only [energyTotal_checked] using QuarterContour.energy_le SigmaQuarterContour.pts
    _ = (Iupper : ℝ) := by norm_num [ITOT,Iupper]
theorem energy_le_rounded : CatalanLambda.Decay.Irho (1/2048 : ℝ)
    (QuarterContour.positions SigmaQuarterContour.pts) (QuarterContour.masses SigmaQuarterContour.pts) ≤
      (179918953/100000000 : ℝ) := by
  exact energy_le_Iupper.trans (by norm_num [Iupper])
end CatalanCore.Cert.QuarterContour.EnergyExact
#print axioms CatalanCore.Cert.QuarterContour.EnergyExact.energyTotal_checked
#print axioms CatalanCore.Cert.QuarterContour.EnergyExact.energy_le_Iupper
#print axioms CatalanCore.Cert.QuarterContour.EnergyExact.energy_le_rounded
