module
public import CatalanCore.Li2.DecayCert.Bent.EnergyRows
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay
noncomputable section

def bentEnergyLowAt (z : ℚ) (b : BentInput) (c : BentCert) (i : ℕ) : ℚ :=
  (c.energyCells[i]?.map (bentEnergyLow z b c)).getD 0

theorem bentEnergyLowAt_get (z : ℚ) (b : BentInput) (c : BentCert) (i : Fin c.energyCells.length) :
    bentEnergyLowAt z b c i.val=bentEnergyLow z b c c.energyCells[i] := by
  simp only [bentEnergyLowAt,List.getElem?_eq_getElem i.isLt,Option.map_some,Option.getD_some,Fin.getElem_fin]

theorem bentEnergyRows_sum (z : ℚ) (b : BentInput) (c : BentCert)
    (hd : datumCheck b.data c.density=true) (hc : energyCoverCheck b c.energyCells=true)
    (vs : List SE) (hm : c.energyCells.mapM (bentEnergyRow z b c)=some vs) :
    (vs.map ScalarExpr.value).sum=
      ∑ j : Fin (baseSegments b).length,(if j.val < b.upper.length then (2:ℝ) else 1)*
        ∑ i : Fin c.energyCells.length,if (c.energyCells[i]).segment=j.val then
          (bentEnergyLowAt z b c i.val:ℝ)*((baseSegments b)[j]).parameterMeasure.real
            (Icc ((c.energyCells[i]).left.x:ℝ) ((c.energyCells[i]).right.x:ℝ)) else 0 := by
  rw [option_mapM_sum_values c.energyCells (bentEnergyRow z b c) (bentEnergyValue z b c) vs
    (fun e he => bentEnergyRow_value z b c hd hc e he) hm]
  rw [← fin_sum_list_map c.energyCells (bentEnergyValue z b c)]
  let label : Fin c.energyCells.length → ℕ := fun i => (c.energyCells[i]).segment
  have hlabel (i : Fin c.energyCells.length) : label i < (baseSegments b).length :=
    (energyCoverCheck_piece b c.energyCells hc c.energyCells[i] (List.getElem_mem _)).1
  let weight : Fin (baseSegments b).length → ℝ := fun j => if j.val < b.upper.length then 2 else 1
  let f : Fin (baseSegments b).length → Fin c.energyCells.length → ℝ := fun j i =>
    (bentEnergyLowAt z b c i.val:ℝ)*((baseSegments b)[j]).parameterMeasure.real
      (Icc ((c.energyCells[i]).left.x:ℝ) ((c.energyCells[i]).right.x:ℝ))
  calc
    _ = ∑ i : Fin c.energyCells.length,weight ⟨label i,hlabel i⟩*f ⟨label i,hlabel i⟩ i := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [bentEnergyValue,weight,f,label,bentEnergyLowAt_get,Fin.getElem_fin]
      have hseg : (c.energyCells[i.val]).segment < (baseSegments b).length := by
        simpa only [label,Fin.getElem_fin] using hlabel i
      rw [List.getElem?_eq_getElem hseg]
      simp only [Option.map_some,Option.getD_some]
      ring
    _ = _ := labelled_sum_reindex label hlabel weight f

theorem bentEnergyExpr_upper (z : ℚ) (hn : z < 0) (b : BentInput) (c : BentCert)
    (hd : datumCheck b.data c.density=true) (hp : placementCheck b=true)
    (hc : energyCoverCheck b c.energyCells=true) (e : SE) (he : bentEnergyExpr z b c=some e) :
    I b.data.dual.σ ≤ e.value := by
  have hform : bentEnergyExpr z b c=(do
    let VI ← bentVExpr z b c
    let lows ← c.energyCells.mapM (bentEnergyRow z b c)
    pure (seScale (1/2) (seSub VI (seSum lows)))) := rfl
  rw [hform] at he
  cases hv : bentVExpr z b c with
  | none => simp [hv] at he
  | some VI =>
    rw [hv] at he
    cases hm : c.energyCells.mapM (bentEnergyRow z b c) with
    | none => simp [hm] at he
    | some lows =>
      rw [hm] at he
      change some (seScale (1/2) (seSub VI (seSum lows)))=some e at he
      rw [← Option.some.inj he,seScale_value,seSub_value,seSum_value,bentVExpr_value z hn b c hd hp VI hv]
      have hl (i : Fin c.energyCells.length) (j : Fin (baseSegments b).length)
          (hlabel : (c.energyCells[i]).segment=j.val) :
          ∀ᵐ x : ℝ ∂((baseSegments b)[j]).parameterMeasure.restrict
            (Icc ((c.energyCells[i]).left.x:ℝ) ((c.energyCells[i]).right.x:ℝ)),
          (bentEnergyLowAt z b c i.val:ℝ) ≤ W (z:ℝ) b.data.dual.σ
            (cqReal ((baseSegments b)[j]).mid+cqReal ((baseSegments b)[j]).half*(x:ℂ)) := by
        rw [bentEnergyLowAt_get]
        exact bentEnergyRows_lower z (ne_of_lt hn) b c hd hp hc lows hm i j hlabel
      have hb := energy_up_bent_labelled z b c.density hd hp c.energyCells hc (bentEnergyLowAt z b c) hl
        (datum_V_integrable (z:ℝ) b.data.dual) (datum_U_integrable b.data.dual)
      rw [← bentEnergyRows_sum z b c hd hc lows hm] at hb
      convert hb using 1 <;> push_cast <;> ring
#print axioms bentEnergyRows_sum
#print axioms bentEnergyExpr_upper
end
end CatalanCore.Li2.DecayCert
