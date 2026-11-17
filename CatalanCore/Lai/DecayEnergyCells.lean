module

public import CatalanCore.Lai.DecayEnergyCheck
public import CatalanCore.Lai.DecayData.Cells00
public import CatalanCore.Lai.DecayData.Cells01

@[expose] public section

/-!
# `CatalanCore.Lai.DecayEnergyCells`: the 26 energy cells (T-energy)

The 26 A cells `cA00 ... cA25` of the cover (`Lai.DecayData.Cells00/01`, each already checked by
`cA<i>_ok : okA cA<i> = true`) with their angle cell `[n0, n1]/128`, remainder `Er` and cell bound `Cb`
(`eC<i>`), and per cell one kernel check `okE eC<i> = true`.
-/

open CatalanCore.Lai.DecayCheck CatalanCore.Lai.DecayEnergyCheck CatalanCore.Lai.DecayData

namespace CatalanCore.Lai.DecayEnergyCells

noncomputable section


def eC0 : ECell := ⟨cA00, 0, 8, (10337016627765 / 549755813888 : ℚ), (-9603026225 / 274877906944 : ℚ)⟩
theorem eC0_okA : okA eC0.d = true := cA00_ok

theorem eC0_okE : okE eC0 = true := by
  -- kcost: 0.51 s measured 17 Nov
  decide +kernel

def eC1 : ECell := ⟨cA01, 8, 16, (677749655429 / 34359738368 : ℚ), (-6476282145 / 137438953472 : ℚ)⟩
theorem eC1_okA : okA eC1.d = true := cA01_ok

theorem eC1_okE : okE eC1 = true := by
  -- kcost: 0.51 s measured 17 Nov
  decide +kernel

def eC2 : ECell := ⟨cA02, 16, 24, (5658655924283 / 274877906944 : ℚ), (-52674543417 / 549755813888 : ℚ)⟩
theorem eC2_okA : okA eC2.d = true := cA02_ok

theorem eC2_okE : okE eC2 = true := by
  -- kcost: 0.52 s measured 17 Nov
  decide +kernel

def eC3 : ECell := ⟨cA03, 24, 32, (2946740664543 / 137438953472 : ℚ), (-205731033543 / 1099511627776 : ℚ)⟩
theorem eC3_okA : okA eC3.d = true := cA03_ok

theorem eC3_okE : okE eC3 = true := by
  -- kcost: 0.53 s measured 17 Nov
  decide +kernel

def eC4 : ECell := ⟨cA04, 32, 40, (24646371317001 / 1099511627776 : ℚ), (-162116229365 / 549755813888 : ℚ)⟩
theorem eC4_okA : okA eC4.d = true := cA04_ok

theorem eC4_okE : okE eC4 = true := by
  -- kcost: 0.50 s measured 17 Nov
  decide +kernel

def eC5 : ECell := ⟨cA05, 40, 48, (26115311097505 / 1099511627776 : ℚ), (-107144020471 / 274877906944 : ℚ)⟩
theorem eC5_okA : okA eC5.d = true := cA05_ok

theorem eC5_okE : okE eC5 = true := by
  -- kcost: 0.50 s measured 17 Nov
  decide +kernel

def eC6 : ECell := ⟨cA06, 48, 56, (1795210011113 / 68719476736 : ℚ), (-501852868529 / 1099511627776 : ℚ)⟩
theorem eC6_okA : okA eC6.d = true := cA06_ok

theorem eC6_okE : okE eC6 = true := by
  -- kcost: 0.49 s measured 17 Nov
  decide +kernel

def eC7 : ECell := ⟨cA07, 56, 64, (533463723855 / 17179869184 : ℚ), (-530986806663 / 1099511627776 : ℚ)⟩
theorem eC7_okA : okA eC7.d = true := cA07_ok

theorem eC7_okE : okE eC7 = true := by
  -- kcost: 0.49 s measured 17 Nov
  decide +kernel

def eC8 : ECell := ⟨cA08, 64, 72, (47655767903191 / 1099511627776 : ℚ), (-503306812301 / 1099511627776 : ℚ)⟩
theorem eC8_okA : okA eC8.d = true := cA08_ok

theorem eC8_okE : okE eC8 = true := by
  -- kcost: 0.50 s measured 17 Nov
  decide +kernel

def eC9 : ECell := ⟨cA09, 72, 80, (88944745206809 / 1099511627776 : ℚ), (-208933574321 / 549755813888 : ℚ)⟩
theorem eC9_okA : okA eC9.d = true := cA09_ok

theorem eC9_okE : okE eC9 = true := by
  -- kcost: 0.53 s measured 17 Nov
  decide +kernel

def eC10 : ECell := ⟨cA10, 80, 88, (253543192500469 / 1099511627776 : ℚ), (-288155787925 / 1099511627776 : ℚ)⟩
theorem eC10_okA : okA eC10.d = true := cA10_ok

theorem eC10_okE : okE eC10 = true := by
  -- kcost: 0.52 s measured 17 Nov
  decide +kernel

def eC11 : ECell := ⟨cA11, 88, 92, (350900538605095 / 1099511627776 : ℚ), (-44255463015 / 549755813888 : ℚ)⟩
theorem eC11_okA : okA eC11.d = true := cA11_ok

theorem eC11_okE : okE eC11 = true := by
  -- kcost: 0.60 s measured 17 Nov
  decide +kernel

def eC12 : ECell := ⟨cA12, 92, 96, (770860606534963 / 1099511627776 : ℚ), (-26225688255 / 549755813888 : ℚ)⟩
theorem eC12_okA : okA eC12.d = true := cA12_ok

theorem eC12_okE : okE eC12 = true := by
  -- kcost: 0.49 s measured 17 Nov
  decide +kernel

def eC13 : ECell := ⟨cA13, 96, 100, (967479547873581 / 549755813888 : ℚ), (-20789108109 / 1099511627776 : ℚ)⟩
theorem eC13_okA : okA eC13.d = true := cA13_ok

theorem eC13_okE : okE eC13 = true := by
  -- kcost: 0.49 s measured 17 Nov
  decide +kernel

def eC14 : ECell := ⟨cA14, 100, 104, (2809373813532483 / 549755813888 : ℚ), (1923739243 / 549755813888 : ℚ)⟩
theorem eC14_okA : okA eC14.d = true := cA14_ok

theorem eC14_okE : okE eC14 = true := by
  -- kcost: 0.49 s measured 17 Nov
  decide +kernel

def eC15 : ECell := ⟨cA15, 104, 108, (19244449731210231 / 1099511627776 : ℚ), (9953163709 / 549755813888 : ℚ)⟩
theorem eC15_okA : okA eC15.d = true := cA15_ok

theorem eC15_okE : okE eC15 = true := by
  -- kcost: 0.49 s measured 17 Nov
  decide +kernel

def eC16 : ECell := ⟨cA16, 108, 110, (21450340164845345 / 1099511627776 : ℚ), (25705227 / 2147483648 : ℚ)⟩
theorem eC16_okA : okA eC16.d = true := cA16_ok

theorem eC16_okE : okE eC16 = true := by
  -- kcost: 0.49 s measured 17 Nov
  decide +kernel

def eC17 : ECell := ⟨cA17, 110, 112, (10014733765112771 / 274877906944 : ℚ), (14010788329 / 1099511627776 : ℚ)⟩
theorem eC17_okA : okA eC17.d = true := cA17_ok

theorem eC17_okE : okE eC17 = true := by
  -- kcost: 0.51 s measured 17 Nov
  decide +kernel

def eC18 : ECell := ⟨cA18, 112, 114, (38159505407552519 / 549755813888 : ℚ), (14046294627 / 1099511627776 : ℚ)⟩
theorem eC18_okA : okA eC18.d = true := cA18_ok

theorem eC18_okE : okE eC18 = true := by
  -- kcost: 0.51 s measured 17 Nov
  decide +kernel

def eC19 : ECell := ⟨cA19, 114, 116, (73459770485541019 / 549755813888 : ℚ), (13449675959 / 1099511627776 : ℚ)⟩
theorem eC19_okA : okA eC19.d = true := cA19_ok

theorem eC19_okE : okE eC19 = true := by
  -- kcost: 0.53 s measured 17 Nov
  decide +kernel

def eC20 : ECell := ⟨cA20, 116, 118, (140787239538431645 / 549755813888 : ℚ), (6212009911 / 549755813888 : ℚ)⟩
theorem eC20_okA : okA eC20.d = true := cA20_ok

theorem eC20_okE : okE eC20 = true := by
  -- kcost: 0.53 s measured 17 Nov
  decide +kernel

def eC21 : ECell := ⟨cA21, 118, 120, (525769539063145337 / 1099511627776 : ℚ), (5589788847 / 549755813888 : ℚ)⟩
theorem eC21_okA : okA eC21.d = true := cA21_ok

theorem eC21_okE : okE eC21 = true := by
  -- kcost: 0.49 s measured 17 Nov
  decide +kernel

def eC22 : ECell := ⟨cA22, 120, 122, (232243632988059597 / 274877906944 : ℚ), (2479710193 / 274877906944 : ℚ)⟩
theorem eC22_okA : okA eC22.d = true := cA22_ok

theorem eC22_okE : okE eC22 = true := by
  -- kcost: 0.67 s measured 17 Nov
  decide +kernel

def eC23 : ECell := ⟨cA23, 122, 124, (1498370497087556725 / 1099511627776 : ℚ), (8819946771 / 1099511627776 : ℚ)⟩
theorem eC23_okA : okA eC23.d = true := cA23_ok

theorem eC23_okE : okE eC23 = true := by
  -- kcost: 0.52 s measured 17 Nov
  decide +kernel

def eC24 : ECell := ⟨cA24, 124, 126, (66325108151308245 / 34359738368 : ℚ), (8019427179 / 1099511627776 : ℚ)⟩
theorem eC24_okA : okA eC24.d = true := cA24_ok

theorem eC24_okE : okE eC24 = true := by
  -- kcost: 0.52 s measured 17 Nov
  decide +kernel

def eC25 : ECell := ⟨cA25, 126, 128, (2551745822279693607 / 1099511627776 : ℚ), (7601283007 / 1099511627776 : ℚ)⟩
theorem eC25_okA : okA eC25.d = true := cA25_ok

theorem eC25_okE : okE eC25 = true := by
  -- kcost: 0.54 s measured 17 Nov
  decide +kernel


end

end CatalanCore.Lai.DecayEnergyCells
