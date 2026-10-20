module

public import CatalanCore.Cert.SigmaQuarter.EnergyChunk00
public import CatalanCore.Cert.SigmaQuarter.EnergyChunk01
public import CatalanCore.Cert.SigmaQuarter.EnergyChunk02
public import CatalanCore.Cert.SigmaQuarter.EnergyChunk03
public import CatalanCore.Cert.SigmaQuarter.EnergyChunk04
public import CatalanCore.Cert.SigmaQuarter.EnergyChunk05
public import CatalanCore.Cert.SigmaQuarter.EnergyChunk06
public import CatalanCore.Cert.SigmaQuarter.EnergyChunk07
public import CatalanCore.Cert.SigmaQuarter.EnergyChunk08
public import CatalanCore.Cert.SigmaQuarter.EnergyChunk09
public import CatalanCore.Cert.SigmaQuarter.EnergyChunk10
public import CatalanCore.Cert.SigmaQuarter.EnergyChunk11
public import CatalanCore.Cert.SigmaQuarter.EnergyChunk12
public import CatalanCore.Cert.SigmaQuarter.EnergyChunk13
public import CatalanCore.Cert.SigmaQuarter.EnergyChunk14
public import CatalanCore.Cert.SigmaQuarter.EnergyChunk15
public import CatalanCore.Cert.SigmaQuarter.EnergyChunk16
public import CatalanCore.Cert.SigmaQuarter.EnergyChunk17
public import CatalanCore.Cert.SigmaQuarter.EnergyChunk18
public import CatalanCore.Cert.SigmaQuarter.EnergyChunk19
public import CatalanCore.Cert.SigmaQuarter.EnergyChunk20
public import CatalanCore.Cert.SigmaQuarter.EnergyChunk21
public import CatalanCore.Cert.SigmaQuarter.EnergyChunk22
public import CatalanCore.Cert.SigmaQuarter.EnergyChunk23
public import CatalanCore.Cert.SigmaQuarter.EnergyChunk24
public import CatalanCore.Cert.SigmaQuarter.EnergyChunk25
public import CatalanCore.Cert.SigmaQuarter.EnergyChunk26
public import CatalanCore.Cert.SigmaQuarter.EnergyChunk27
public import CatalanCore.Cert.SigmaQuarter.EnergyChunk28
public import CatalanCore.Cert.SigmaQuarter.EnergyChunk29
public import CatalanCore.Cert.SigmaQuarter.EnergyChunk30
public import CatalanCore.Cert.SigmaQuarter.EnergyChunk31
public import CatalanCore.Cert.SigmaQuarter.EnergyChunk32
public import CatalanCore.Cert.SigmaQuarter.EnergyChunk33
public import CatalanCore.Cert.SigmaQuarter.EnergyChunk34
public import CatalanCore.Cert.SigmaQuarter.EnergyChunk35
public import CatalanCore.Cert.SigmaQuarter.EnergyChunk36
public import CatalanCore.Cert.SigmaQuarter.EnergyChunk37
public import CatalanCore.Cert.SigmaQuarter.EnergyChunk38
public import CatalanCore.Cert.SigmaQuarter.EnergyChunk39
public import CatalanCore.Cert.SigmaQuarter.EnergyChunk40
public import CatalanCore.Cert.SigmaQuarter.EnergyChunk41
public import CatalanCore.Cert.SigmaQuarter.EnergyChunk42
public import CatalanCore.Cert.SigmaQuarter.EnergyChunk43
public import CatalanCore.Cert.SigmaQuarter.EnergyChunk44
public import CatalanCore.Cert.SigmaQuarter.EnergyChunk45
public import CatalanCore.Cert.SigmaQuarter.EnergyChunk46
public import CatalanCore.Cert.SigmaQuarter.EnergyChunk47
public import CatalanCore.Cert.SigmaQuarter.EnergyChunk48
public import CatalanCore.Cert.SigmaQuarter.EnergyChunk49
public import CatalanCore.Cert.SigmaQuarter.EnergyChunk50
public import CatalanCore.Cert.SigmaQuarter.EnergyChunk51
public import CatalanCore.Cert.SigmaQuarter.EnergyChunk52
public import CatalanCore.Cert.SigmaQuarter.EnergyChunk53
public import CatalanCore.Cert.SigmaQuarter.EnergyChunk54
public import CatalanCore.Cert.SigmaQuarter.EnergyChunk55
public import CatalanCore.Cert.SigmaQuarter.EnergyChunk56
public import CatalanCore.Cert.SigmaQuarter.EnergyChunk57
public import CatalanCore.Cert.SigmaQuarter.EnergyChunk58
public import CatalanCore.Cert.SigmaQuarter.EnergyChunk59

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem energy_chunks : pts = energyChunk 0 ++ energyChunk 1 ++ energyChunk 2 ++ energyChunk 3 ++ energyChunk 4 ++ energyChunk 5 ++ energyChunk 6 ++ energyChunk 7 ++ energyChunk 8 ++ energyChunk 9 ++ energyChunk 10 ++ energyChunk 11 ++ energyChunk 12 ++ energyChunk 13 ++ energyChunk 14 ++ energyChunk 15 ++ energyChunk 16 ++ energyChunk 17 ++ energyChunk 18 ++ energyChunk 19 ++ energyChunk 20 ++ energyChunk 21 ++ energyChunk 22 ++ energyChunk 23 ++ energyChunk 24 ++ energyChunk 25 ++ energyChunk 26 ++ energyChunk 27 ++ energyChunk 28 ++ energyChunk 29 ++ energyChunk 30 ++ energyChunk 31 ++ energyChunk 32 ++ energyChunk 33 ++ energyChunk 34 ++ energyChunk 35 ++ energyChunk 36 ++ energyChunk 37 ++ energyChunk 38 ++ energyChunk 39 ++ energyChunk 40 ++ energyChunk 41 ++ energyChunk 42 ++ energyChunk 43 ++ energyChunk 44 ++ energyChunk 45 ++ energyChunk 46 ++ energyChunk 47 ++ energyChunk 48 ++ energyChunk 49 ++ energyChunk 50 ++ energyChunk 51 ++ energyChunk 52 ++ energyChunk 53 ++ energyChunk 54 ++ energyChunk 55 ++ energyChunk 56 ++ energyChunk 57 ++ energyChunk 58 ++ energyChunk 59 := by decide +kernel

theorem energyTot_val : energyTot pts = (-1250837350937396876287209246288743738534 : ℤ) := by
  conv_lhs => rw [energy_chunks]
  simp only [energyTot_append]
  rw [energyChunk_0, energyChunk_1, energyChunk_2, energyChunk_3, energyChunk_4, energyChunk_5, energyChunk_6, energyChunk_7, energyChunk_8, energyChunk_9, energyChunk_10, energyChunk_11, energyChunk_12, energyChunk_13, energyChunk_14, energyChunk_15, energyChunk_16, energyChunk_17, energyChunk_18, energyChunk_19, energyChunk_20, energyChunk_21, energyChunk_22, energyChunk_23, energyChunk_24, energyChunk_25, energyChunk_26, energyChunk_27, energyChunk_28, energyChunk_29, energyChunk_30, energyChunk_31, energyChunk_32, energyChunk_33, energyChunk_34, energyChunk_35, energyChunk_36, energyChunk_37, energyChunk_38, energyChunk_39, energyChunk_40, energyChunk_41, energyChunk_42, energyChunk_43, energyChunk_44, energyChunk_45, energyChunk_46, energyChunk_47, energyChunk_48, energyChunk_49, energyChunk_50, energyChunk_51, energyChunk_52, energyChunk_53, energyChunk_54, energyChunk_55, energyChunk_56, energyChunk_57, energyChunk_58, energyChunk_59]
  norm_num

end CatalanCore.Cert.SigmaQuarter
