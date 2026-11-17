module

public import CatalanCore.Lai.DecayCert
public import CatalanCore.Lai.DecayData.Cover
public import CatalanCore.Lai.DecayEnergyData
public import CatalanCore.Lai.DecayAtoms

@[expose] public section

/-!
# `CatalanCore.Lai.DecayFinal`: the closed Lai decay data and the unconditional decay theorems

`laiDecayData` assembles the SOS positivity (`DecayGlue.laiC_data`), the 40-cell cover
(`DecayData.laiCover_all`), the atoms (`DecayAtoms`) and the energy (`DecayEnergyData`).
-/

namespace CatalanCore.Lai.DecayFinal

open CatalanCore.Lai.DecayCert CatalanCore.Uniform

/-- **The closed decay data of Lai's design** (`c = laiC`, `N = 8`, `wA = 146127/500000`,
`wB = 459681/10^6`, `a0 = A0q`, `AA = AAq`). -/
theorem laiDecayData : LaiDecayData DecayGlue.laiC 8 (146127 / 500000) (459681 / 1000000)
    (DecayAtoms.A0q : ℝ) (DecayAtoms.AAq : ℝ) where
  hpos := DecayGlue.laiC_data.1
  hc0 := DecayGlue.laiC_data.2
  hcov := DecayData.laiCover_all
  ha0 := DecayAtoms.lai_ha0_closed
  hA := DecayAtoms.lai_hA_closed
  hρ := DecayAtoms.lai_hρ_closed
  henergy := DecayEnergyData.laiEnergyOK_closed

/-- Plane decay, no hypotheses. -/
theorem lai_plane_decay_final (a b : ℤ) (hb : b ≠ 0) :
    HasScaledDecay (laiPlaneFam a b) id (3344010000 / 10 ^ 8) (4294856306 / 10 ^ 8) :=
  lai_plane_decay laiDecayData a b hb

/-- Ratio decay, no hypotheses. -/
theorem lai_ratio_decay_final :
    HasScaledDecay laiRatioFam id (3344010000 / 10 ^ 8) (4294856306 / 10 ^ 8) :=
  lai_ratio_decay laiDecayData

#print axioms laiDecayData
#print axioms lai_plane_decay_final
#print axioms lai_ratio_decay_final

end CatalanCore.Lai.DecayFinal
