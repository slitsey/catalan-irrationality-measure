module
public import CatalanArchive.CatalanMeasure.Parametric.GapContentTransfer
public import CatalanArchive.CatalanMeasure.Parametric.FlexibleSecondEnergy
public import CatalanMeasure.Parametric.GapBudgets
public import CatalanMeasure.Parametric.StrongNearField
public import CatalanArchive.CatalanMeasure.Cert.MarkedResidual
public import CatalanArchive.CatalanMeasure.Parametric.StrongFirstFields
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial Filter Real OAI.InternalCatalan
open scoped Topology
noncomputable section

def gapAtomDomain (x : ℝ) : Prop := (physicalAtomGap:ℝ)≤|x|

theorem gap_nodes_nonzero (N : ℕ) (i : Fin (18*N)) : twentyGapNodes N i≠0 := by
  have hi := (gap_nodes_bounds
    (show (0:ℝ) < interpolationGap by norm_num [interpolationGap])
    (show (interpolationGap:ℝ)<1 by norm_num [interpolationGap]) N i).2
  change (interpolationGap:ℝ)< |twentyGapNodes N i| at hi
  intro hz
  rw [hz,abs_zero] at hi
  norm_num [interpolationGap] at hi

def GapWeightBounds : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ (k : ℕ) (a : Fin (18*N)),
    |(rowCommonFactor twenty N).eval (twentyGapNodes N a)| *
      |restrictedWeight twenty N k (twentyGapNodes N) a|≤
        108000*N*Real.exp (gapWeightCost*N)

theorem gap_atom_point_of_bounds
    (F : FirstTrialBoundsAt strongTarget strongFirstCost)
    (D : SecondTrialBoundsOn strongTarget gapResidualCap (-(3/4:ℝ)) gapSecondCost gapAtomDomain)
    (hw : GapWeightBounds) : WeightedAtomPointOn twentyGapNodes gapAtomDomain strongTarget gapRadiusCost := by
  rw [← gap_final_payments.2.1]
  exact weighted_atom_point_on F twentyGapNodes gapAtomDomain D gap_final_payments.1 le_rfl hw

theorem measure_878_of_gap_bounds
    (F : FirstTrialBoundsAt strongTarget strongFirstCost)
    (D : SecondTrialBoundsOn strongTarget gapResidualCap (-(3/4:ℝ)) gapSecondCost gapAtomDomain)
    (hw : GapWeightBounds) :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
      (b:ℝ)^(-(878:ℝ))< |catalan-(a:ℝ)/b| := by
  obtain ⟨c,hc,hdiv,hcop,hgrowth⟩ :=
    secondaryTent_content_of_canonical_rank secondaryTent_canonical_rank
  have h := measure_of_content_on twentyGapNodes gapAtomDomain
    (fun N => (twenty_gap_nodes_properties N).1)
    (fun N i => ((twenty_gap_nodes_properties N).2 i).1) gap_nodes_nonzero
    (fun N i => ((twenty_gap_nodes_properties N).2 i).2) strongTarget c hc hdiv hcop
    (χ := 507/2000) (ρ := gapRadiusCost) (η := 375279/200000)
    (κ := 4390000/519037) (δ := 1/10000000)
    hgrowth (gap_atom_point_of_bounds F D hw) strong_eta_lt
    (by norm_num) (by norm_num [gapRadiusCost]) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num [gapRadiusCost]

theorem measure_2632_of_gap_bounds
    (F : FirstTrialBoundsAt strongTarget strongFirstCost)
    (D : SecondTrialBoundsOn strongTarget gapResidualCap (-(3/4:ℝ)) gapSecondCost gapAtomDomain)
    (hw : GapWeightBounds) :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
      (b:ℝ)^(-(2632:ℝ))< |catalan-(a:ℝ)/b| := by
  obtain ⟨c,hc,hdiv,_hcop,hgrowth⟩ :=
    secondaryTent_content_of_canonical_rank secondaryTent_canonical_rank
  obtain ⟨P₀,hnz,hsmall⟩ := content_hypotheses_on twentyGapNodes gapAtomDomain
    (fun N => (twenty_gap_nodes_properties N).1)
    (fun N i => ((twenty_gap_nodes_properties N).2 i).1) gap_nodes_nonzero
    (fun N i => ((twenty_gap_nodes_properties N).2 i).2) strongTarget c hc hdiv
    (χ := 507/2000) (ρ := gapRadiusCost) (η := 375279/200000)
    hgrowth (gap_atom_point_of_bounds F D hw) strong_eta_lt
  have hnz' : ∀ p, P₀≤p → p.Prime → ∀ (a : ℤ) (b : ℕ),
      0<b → ¬p∣b → aeval ((a:ℝ)/b) (twentyContentIntPoly c p)≠0 := by
    intro p hp hprime a b hb hpb
    exact hnz p hp hprime a b hb
      (fun h => hpb (dvd_trans (show p∣p^2 from ⟨p,by ring⟩) h))
  have hdeg : ∀ p, (twentyContentIntPoly c p).natDegree≤18*p := by
    intro p
    exact (coefficientContentQuotient_natDegree (twentyMeasureIntPoly p)
      (hc p) (hdiv p)).le.trans (twentyMeasureIntPoly_natDegree_le p)
  have hh := CatalanMeasure.irrationality_measure_of_polynomials catalan 18
    (η := 375279/200000+507/2000) (ρ := gapRadiusCost) (by norm_num)
    (by norm_num [gapRadiusCost]) (twentyContentIntPoly c) P₀ hdeg hnz' hsmall
  simp only [Nat.cast_ofNat] at hh
  filter_upwards [hh,eventually_ge_atTop (2:ℕ)] with b hb hb2 a
  have hb1 : (1:ℝ)≤b := by exact_mod_cast (show 1≤b by omega)
  exact lt_of_le_of_lt (Real.rpow_le_rpow_of_exponent_le hb1 (by norm_num [gapRadiusCost])) (hb a)

end
end CatalanMeasure.Parametric
