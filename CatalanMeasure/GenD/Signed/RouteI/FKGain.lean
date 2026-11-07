module
public import CatalanMeasure.GenD.Signed.RouteI.Literals
public import CatalanMeasure.GenD.Uniform.Bank535.Ledger10.Merge13

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 0

namespace CatalanMeasure.GenD.Signed.RouteI
open CatalanMeasure.GenD D58
noncomputable section

open Uniform.Bank540.Ledger
open CatalanMeasure.GenD.Uniform.Bank535.Ledger10

/-! C74: fallback content producer, WaveE. The data-free terminal does not import this module. -/
theorem eta_lt_of_gain_shift (eta g G : ℝ)
    (h : eta ≤ g + G + 798775 / 100000) :
    eta < 58^2 * (K590.target + G / 58^2 - Real.log 2/2) - gDg g := by
  obtain ⟨hl, hh⟩ := D58.log2_bounds
  unfold gDg
  norm_num [K590.target, D58.lo, D58.hi] at hl hh ⊢
  linarith

/-- Seven existing C-prime windows sharpen the exported rounded content bound. -/
theorem gain13_ge_sharp : (789379626089/36054018000 : ℝ) ≤ gain13 := by
  have h := gain12_ge
  unfold gain13 cpGain
  simp only [cpWins,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,cw_area]
  norm_num
  linarith only [h]

theorem content_fk_gain : content296-1/1000 ≤ gain13 := by
  have h := gain13_ge_sharp
  norm_num [content296] at *
  linarith only [h]

theorem hgain296 :
    eta296 < 58^2 * (T296 - Real.log 2/2) - gDg gain13 := by
  change eta296 < 58^2 * (K590.target + shift296 / 58^2 - Real.log 2/2) - gDg gain13
  apply eta_lt_of_gain_shift
  have hg := content_fk_gain
  dsimp only [eta296]
  linarith only [hg]

end
end CatalanMeasure.GenD.Signed.RouteI
#print axioms CatalanMeasure.GenD.Signed.RouteI.eta_lt_of_gain_shift
#print axioms CatalanMeasure.GenD.Signed.RouteI.gain13_ge_sharp
#print axioms CatalanMeasure.GenD.Signed.RouteI.content_fk_gain
#print axioms CatalanMeasure.GenD.Signed.RouteI.hgain296
