module
public import CatalanCore.Li2.DecayCert.Bent.EnergyPrelude
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay CatalanCore.Zeta5.Potential
noncomputable section

def bentEnergyRow (z : ℚ) (b : BentInput) (c : BentCert) (e : EnergyPiece) : Option SE := do
  let s ← (baseSegments b)[e.segment]?
  let lo ← energyLower z b c.contour c.atoms e
  pure (seScale ((if e.segment < b.upper.length then 2 else 1)*lo)
    (arcMassExpr e.terms s e.left e.right))

def bentEnergyLow (z : ℚ) (b : BentInput) (c : BentCert) (e : EnergyPiece) : ℚ :=
  (energyLower z b c.contour c.atoms e).getD 0

def bentEnergyValue (z : ℚ) (b : BentInput) (c : BentCert) (e : EnergyPiece) : ℝ :=
  ((baseSegments b)[e.segment]?.map (fun s => (if e.segment < b.upper.length then (2:ℝ) else 1)*
    (bentEnergyLow z b c e:ℝ)*s.parameterMeasure.real (Icc (e.left.x:ℝ) (e.right.x:ℝ)))).getD 0

theorem bentEnergyRow_lower (z : ℚ) (b : BentInput) (c : BentCert) (e : EnergyPiece)
    (v : SE) (hv : bentEnergyRow z b c e=some v) :
    energyLower z b c.contour c.atoms e=some (bentEnergyLow z b c e) := by
  unfold bentEnergyRow at hv
  cases hs : (baseSegments b)[e.segment]? with
  | none => simp [hs] at hv
  | some s =>
    rw [hs] at hv
    cases hl : energyLower z b c.contour c.atoms e with
    | none => simp [hl] at hv
    | some L => simp only [bentEnergyLow,hl,Option.getD_some]

theorem bentEnergyRow_value (z : ℚ) (b : BentInput) (c : BentCert)
    (hd : datumCheck b.data c.density=true) (hc : energyCoverCheck b c.energyCells=true)
    (e : EnergyPiece) (he : e ∈ c.energyCells) (v : SE) (hv : bentEnergyRow z b c e=some v) :
    v.value=bentEnergyValue z b c e := by
  have hp := energyCoverCheck_piece b c.energyCells hc e he
  let s := (baseSegments b)[e.segment]
  have hs : (baseSegments b)[e.segment]?=some s := List.getElem?_eq_getElem hp.1
  have hL := bentEnergyRow_lower z b c e v hv
  unfold bentEnergyRow at hv
  rw [hs,hL] at hv
  change some (seScale ((if e.segment < b.upper.length then 2 else 1)*bentEnergyLow z b c e)
    (arcMassExpr e.terms s e.left e.right))=some v at hv
  rw [← Option.some.inj hv,seScale_value]
  have hpos := baseSegments_positive b c.density hd s (List.getElem_mem _)
  have hhalf : cqReal s.half ≠ 0 := by
    rcases (sourceDataCheck_parts b.data.segments b.data.radius c.density hd).2 s
      (baseSegments_mem_data b s (List.getElem_mem _)) with ⟨t,ht,hbern⟩
    exact half_ne_of_cqSq_ne s.half ht.1
  rw [arcMassExpr_parameter e.terms s e.left e.right hhalf hpos hp.2.1 hp.2.2.1 hp.2.2.2.le]
  simp only [bentEnergyValue,hs,Option.map_some,Option.getD_some,Rat.cast_mul]
  split_ifs <;> norm_num

theorem bentEnergyRows_lower (z : ℚ) (hz : z ≠ 0) (b : BentInput) (c : BentCert)
    (hd : datumCheck b.data c.density=true) (hp : placementCheck b=true)
    (hc : energyCoverCheck b c.energyCells=true) (vs : List SE)
    (hm : c.energyCells.mapM (bentEnergyRow z b c)=some vs)
    (i : Fin c.energyCells.length) (j : Fin (baseSegments b).length)
    (hlabel : (c.energyCells[i]).segment=j.val) :
    ∀ᵐ x : ℝ ∂((baseSegments b)[j]).parameterMeasure.restrict
      (Icc ((c.energyCells[i]).left.x:ℝ) ((c.energyCells[i]).right.x:ℝ)),
      (bentEnergyLow z b c c.energyCells[i]:ℝ) ≤ W (z:ℝ) b.data.dual.σ
        (cqReal ((baseSegments b)[j]).mid+cqReal ((baseSegments b)[j]).half*(x:ℂ)) := by
  have hei : c.energyCells[i] ∈ c.energyCells := List.getElem_mem _
  have hpiece := energyCoverCheck_piece b c.energyCells hc c.energyCells[i] hei
  rcases option_mapM_input c.energyCells (bentEnergyRow z b c) vs hm c.energyCells[i] hei with ⟨v,hv⟩
  have hL := bentEnergyRow_lower z b c c.energyCells[i] v hv
  have hl := energyLower_sound z hz b c.density hd hp c.contour c.atoms c.energyCells[i] hpiece.1 _ hL
  have hidx : (baseSegments b)[(c.energyCells[i]).segment]'hpiece.1=(baseSegments b)[j] := by
    have hfin : (⟨(c.energyCells[i]).segment,hpiece.1⟩:Fin (baseSegments b).length)=j := Fin.ext hlabel
    exact congrArg (fun k : Fin (baseSegments b).length => (baseSegments b)[k]) hfin
  change ∀ᵐ x : ℝ ∂((baseSegments b)[(c.energyCells[i]).segment]).parameterMeasure.restrict
      (Icc ((c.energyCells[i]).left.x:ℝ) ((c.energyCells[i]).right.x:ℝ)),_ at hl
  rw [hidx] at hl
  exact hl
#print axioms bentEnergyRow_lower
#print axioms bentEnergyRow_value
#print axioms bentEnergyRows_lower
end
end CatalanCore.Li2.DecayCert
