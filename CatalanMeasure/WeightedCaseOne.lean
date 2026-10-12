module

public import CatalanMeasure.Cert.ModColumn

@[expose] public section

namespace CatalanMeasure.WeightedCaseOne

open CatalanMeasure.Cert OAI.InternalCatalan

def AY : List ℚ := [(7 / 48 : ℚ),
  (-88752761 / 37500000 : ℚ),
  (75989479 / 7500000 : ℚ),
  (202935297 / 12500000 : ℚ),
  (-814655649 / 12500000 : ℚ),
  (-217677447 / 6250000 : ℚ),
  (879826751 / 6250000 : ℚ),
  (10764211 / 312500 : ℚ),
  (-101923001 / 781250 : ℚ),
  (-9819141 / 781250 : ℚ),
  (16992389 / 390625 : ℚ)]
def QY : List ℚ := [(0 : ℚ),
  (1 : ℚ),
  (0 : ℚ),
  (-1 : ℚ)]
def MY : ℚ := -7586255 / 10000000
def planY : List Piece := [((0 : ℚ), (1 / 4 : ℚ), false), ((1 / 4 : ℚ), (1 / 2 : ℚ), false), ((1 / 2 : ℚ), (9600673 / 10000000 : ℚ), false), ((9600673 / 10000000 : ℚ), (384027 / 400000 : ℚ), true), ((384027 / 400000 : ℚ), (1 : ℚ), false)]

set_option maxRecDepth 1000000 in
theorem hAQ : fracSum (modColFracs barrierV1Finite []) = (AY, QY) := by decide +kernel

set_option maxRecDepth 1000000 in
theorem hchain : colCheck [] AY planY = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem hgaps : planY.all (gapOK AY) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem hbrackets : planY.all (modColBracketOK barrierV1Finite [] AY QY MY) = true := by decide +kernel

theorem column_bound : ∀ s ∈ Set.Ioo (0 : ℝ) 1,
    realEnergyColumnTrialField barrierV1 s + Real.log (1 + s) ≤ -7586255 / 10000000 := by
  have h := modColCheck_spec hAQ hchain hgaps hbrackets
  simpa [modColField, trialSeq, barrierV1, MY] using h

end CatalanMeasure.WeightedCaseOne
