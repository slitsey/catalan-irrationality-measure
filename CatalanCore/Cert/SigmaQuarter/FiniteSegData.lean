module
public import CatalanCore.Cert.SigmaQuarter.GlueCore
public import CatalanCore.Cert.SigmaQuarter.Seg0
public import CatalanCore.Cert.SigmaQuarter.Seg1
public import CatalanCore.Cert.SigmaQuarter.Seg2
public import CatalanCore.Cert.SigmaQuarter.Seg3
public import CatalanCore.Cert.SigmaQuarter.Seg4
public import CatalanCore.Cert.SigmaQuarter.Seg5
public import CatalanCore.Cert.SigmaQuarter.Seg6
public import CatalanCore.Cert.SigmaQuarter.Seg7
public import CatalanCore.Cert.SigmaQuarter.Seg8
public import CatalanCore.Cert.SigmaQuarter.Seg9
public import CatalanCore.Cert.SigmaQuarter.Seg10
public import CatalanCore.Cert.SigmaQuarter.Seg11
public import CatalanCore.Cert.SigmaQuarter.Seg12
public import CatalanCore.Cert.SigmaQuarter.Seg13
public import CatalanCore.Cert.SigmaQuarter.Seg14
public import CatalanCore.Cert.SigmaQuarter.Seg15
public import CatalanCore.Cert.SigmaQuarter.Seg16
public import CatalanCore.Cert.SigmaQuarter.Seg17
public import CatalanCore.Cert.SigmaQuarter.Seg18
public import CatalanCore.Cert.SigmaQuarter.Seg19
public import CatalanCore.Cert.SigmaQuarter.Seg20
public import CatalanCore.Cert.SigmaQuarter.Seg21
public import CatalanCore.Cert.SigmaQuarter.Seg22
public import CatalanCore.Cert.SigmaQuarter.Seg23
public import CatalanCore.Cert.SigmaQuarter.Seg24
public import CatalanCore.Cert.SigmaQuarter.Seg25
public import CatalanCore.Cert.SigmaQuarter.Seg26
public import CatalanCore.Cert.SigmaQuarter.Seg27
public import CatalanCore.Cert.SigmaQuarter.Seg28
public import CatalanCore.Cert.SigmaQuarter.Seg29
public import CatalanCore.Cert.SigmaQuarter.Seg30
public import CatalanCore.Cert.SigmaQuarter.Seg31
public import CatalanCore.Cert.SigmaQuarter.Seg32
public import CatalanCore.Cert.SigmaQuarter.Seg33
public import CatalanCore.Cert.SigmaQuarter.Seg34
public import CatalanCore.Cert.SigmaQuarter.Seg35
public import CatalanCore.Cert.SigmaQuarter.Seg36
public import CatalanCore.Cert.SigmaQuarter.Seg37
public import CatalanCore.Cert.SigmaQuarter.Seg38
public import CatalanCore.Cert.SigmaQuarter.Seg39
public import CatalanCore.Cert.SigmaQuarter.Seg40
public import CatalanCore.Cert.SigmaQuarter.Seg41
public import CatalanCore.Cert.SigmaQuarter.Seg42
public import CatalanCore.Cert.SigmaQuarter.Seg43
public import CatalanCore.Cert.SigmaQuarter.Seg44
public import CatalanCore.Cert.SigmaQuarter.Seg45
public import CatalanCore.Cert.SigmaQuarter.Seg46
public import CatalanCore.Cert.SigmaQuarter.Seg47
public import CatalanCore.Cert.SigmaQuarter.Seg48
public import CatalanCore.Cert.SigmaQuarter.Seg49
public import CatalanCore.Cert.SigmaQuarter.Seg50
public import CatalanCore.Cert.SigmaQuarter.Seg51
public import CatalanCore.Cert.SigmaQuarter.Seg52
public import CatalanCore.Cert.SigmaQuarter.Seg53
public import CatalanCore.Cert.SigmaQuarter.Seg54
public import CatalanCore.Cert.SigmaQuarter.Seg55
public import CatalanCore.Cert.SigmaQuarter.Seg56
public import CatalanCore.Cert.SigmaQuarter.Seg57
public import CatalanCore.Cert.SigmaQuarter.Seg58
public import CatalanCore.Cert.SigmaQuarter.Seg59
public import CatalanCore.Cert.SigmaQuarter.Seg60
public import CatalanCore.Cert.SigmaQuarter.Seg61
public import CatalanCore.Cert.SigmaQuarter.Seg62
public import CatalanCore.Cert.SigmaQuarter.Seg63
public import CatalanCore.Cert.SigmaQuarter.Seg64

public import CatalanCore.Cert.SigmaQuarter.GeometrySeg00
public import CatalanCore.Cert.SigmaQuarter.GeometrySeg01
public import CatalanCore.Cert.SigmaQuarter.GeometrySeg02
public import CatalanCore.Cert.SigmaQuarter.GeometrySeg03
public import CatalanCore.Cert.SigmaQuarter.GeometrySeg04
public import CatalanCore.Cert.SigmaQuarter.GeometrySeg05
public import CatalanCore.Cert.SigmaQuarter.GeometrySeg06
public import CatalanCore.Cert.SigmaQuarter.GeometrySeg07
public import CatalanCore.Cert.SigmaQuarter.GeometrySeg08

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def segs : List Macro := Seg0Data ++ Seg1Data ++ Seg2Data ++ Seg3Data ++ Seg4Data ++ Seg5Data ++ Seg6Data ++ Seg7Data ++ Seg8Data ++ Seg9Data ++ Seg10Data ++ Seg11Data ++ Seg12Data ++ Seg13Data ++ Seg14Data ++ Seg15Data ++ Seg16Data ++ Seg17Data ++ Seg18Data ++ Seg19Data ++ Seg20Data ++ Seg21Data ++ Seg22Data ++ Seg23Data ++ Seg24Data ++ Seg25Data ++ Seg26Data ++ Seg27Data ++ Seg28Data ++ Seg29Data ++ Seg30Data ++ Seg31Data ++ Seg32Data ++ Seg33Data ++ Seg34Data ++ Seg35Data ++ Seg36Data ++ Seg37Data ++ Seg38Data ++ Seg39Data ++ Seg40Data ++ Seg41Data ++ Seg42Data ++ Seg43Data ++ Seg44Data ++ Seg45Data ++ Seg46Data ++ Seg47Data ++ Seg48Data ++ Seg49Data ++ Seg50Data ++ Seg51Data ++ Seg52Data ++ Seg53Data ++ Seg54Data ++ Seg55Data ++ Seg56Data ++ Seg57Data ++ Seg58Data ++ Seg59Data ++ Seg60Data ++ Seg61Data ++ Seg62Data ++ Seg63Data ++ Seg64Data
theorem segs_far : ∀ m ∈ segs, farOK pts m := by
  intro m hm
  simp only [segs, List.mem_append, or_assoc] at hm
  rcases hm with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39 | h40 | h41 | h42 | h43 | h44 | h45 | h46 | h47 | h48 | h49 | h50 | h51 | h52 | h53 | h54 | h55 | h56 | h57 | h58 | h59 | h60 | h61 | h62 | h63 | h64
  exacts [Seg0_farAll m h0,Seg1_farAll m h1,Seg2_farAll m h2,Seg3_farAll m h3,Seg4_farAll m h4,Seg5_farAll m h5,Seg6_farAll m h6,Seg7_farAll m h7,Seg8_farAll m h8,Seg9_farAll m h9,Seg10_farAll m h10,Seg11_farAll m h11,Seg12_farAll m h12,Seg13_farAll m h13,Seg14_farAll m h14,Seg15_farAll m h15,Seg16_farAll m h16,Seg17_farAll m h17,Seg18_farAll m h18,Seg19_farAll m h19,Seg20_farAll m h20,Seg21_farAll m h21,Seg22_farAll m h22,Seg23_farAll m h23,Seg24_farAll m h24,Seg25_farAll m h25,Seg26_farAll m h26,Seg27_farAll m h27,Seg28_farAll m h28,Seg29_farAll m h29,Seg30_farAll m h30,Seg31_farAll m h31,Seg32_farAll m h32,Seg33_farAll m h33,Seg34_farAll m h34,Seg35_farAll m h35,Seg36_farAll m h36,Seg37_farAll m h37,Seg38_farAll m h38,Seg39_farAll m h39,Seg40_farAll m h40,Seg41_farAll m h41,Seg42_farAll m h42,Seg43_farAll m h43,Seg44_farAll m h44,Seg45_farAll m h45,Seg46_farAll m h46,Seg47_farAll m h47,Seg48_farAll m h48,Seg49_farAll m h49,Seg50_farAll m h50,Seg51_farAll m h51,Seg52_farAll m h52,Seg53_farAll m h53,Seg54_farAll m h54,Seg55_farAll m h55,Seg56_farAll m h56,Seg57_farAll m h57,Seg58_farAll m h58,Seg59_farAll m h59,Seg60_farAll m h60,Seg61_farAll m h61,Seg62_farAll m h62,Seg63_farAll m h63,Seg64_farAll m h64]
theorem segs_ok : ∀ m ∈ segs, axisOK pts m = true := by
  intro m hm
  simp only [segs, List.mem_append, or_assoc] at hm
  rcases hm with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39 | h40 | h41 | h42 | h43 | h44 | h45 | h46 | h47 | h48 | h49 | h50 | h51 | h52 | h53 | h54 | h55 | h56 | h57 | h58 | h59 | h60 | h61 | h62 | h63 | h64
  exacts [Seg0_okAll m h0,Seg1_okAll m h1,Seg2_okAll m h2,Seg3_okAll m h3,Seg4_okAll m h4,Seg5_okAll m h5,Seg6_okAll m h6,Seg7_okAll m h7,Seg8_okAll m h8,Seg9_okAll m h9,Seg10_okAll m h10,Seg11_okAll m h11,Seg12_okAll m h12,Seg13_okAll m h13,Seg14_okAll m h14,Seg15_okAll m h15,Seg16_okAll m h16,Seg17_okAll m h17,Seg18_okAll m h18,Seg19_okAll m h19,Seg20_okAll m h20,Seg21_okAll m h21,Seg22_okAll m h22,Seg23_okAll m h23,Seg24_okAll m h24,Seg25_okAll m h25,Seg26_okAll m h26,Seg27_okAll m h27,Seg28_okAll m h28,Seg29_okAll m h29,Seg30_okAll m h30,Seg31_okAll m h31,Seg32_okAll m h32,Seg33_okAll m h33,Seg34_okAll m h34,Seg35_okAll m h35,Seg36_okAll m h36,Seg37_okAll m h37,Seg38_okAll m h38,Seg39_okAll m h39,Seg40_okAll m h40,Seg41_okAll m h41,Seg42_okAll m h42,Seg43_okAll m h43,Seg44_okAll m h44,Seg45_okAll m h45,Seg46_okAll m h46,Seg47_okAll m h47,Seg48_okAll m h48,Seg49_okAll m h49,Seg50_okAll m h50,Seg51_okAll m h51,Seg52_okAll m h52,Seg53_okAll m h53,Seg54_okAll m h54,Seg55_okAll m h55,Seg56_okAll m h56,Seg57_okAll m h57,Seg58_okAll m h58,Seg59_okAll m h59,Seg60_okAll m h60,Seg61_okAll m h61,Seg62_okAll m h62,Seg63_okAll m h63,Seg64_okAll m h64]
theorem segs_chunks : segs = segGeo0 ++ segGeo1 ++ segGeo2 ++ segGeo3 ++ segGeo4 ++ segGeo5 ++ segGeo6 ++ segGeo7 ++ segGeo8 := by
  simp only [segs, segGeo0, segGeo1, segGeo2, segGeo3, segGeo4, segGeo5, segGeo6, segGeo7, segGeo8, List.append_assoc]
end CatalanCore.Cert.SigmaQuarter
