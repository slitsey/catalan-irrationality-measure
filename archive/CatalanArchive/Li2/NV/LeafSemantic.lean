module
public import CatalanCore.Li2.DecayCert.Lattice.Gates.Own
public import CatalanCore.Li2.DecayCert.Lattice.Gates.Lists
public import CatalanCore.Li2.DecayCert.Covers.Geometry
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 800000
open Polynomial MeasureTheory Set
open scoped BigOperators
open CatalanCore.Li2.DecayCert CatalanCore.Li2.DecayCert.LatticeGate
namespace CatalanCore.Li2.DecayCert.NVLeafSemantic
noncomputable section



def leafGap (co : List ℚ) (E a b va vb : ℚ) : List ℚ :=
  qListSub [va-(vb-va)/(b-a)*a-E,(vb-va)/(b-a)] co

def leafGapTree (co : List ℚ) (E a b va vb : ℚ) : BernsteinTree :=
  .leaf (co.length-1) ((List.range co.length).map
    (bernCoeffFast (leafGap co E a b va vb) a b (co.length-1)))

def leafGapCheck (co : List ℚ) (E a b va vb : ℚ) : Bool :=
  bernListCheck (leafGap co E a b va vb) a b (leafGapTree co E a b va vb)

theorem qListPoly_eval_real (co : List ℚ) (u : ℝ) :
    ((qListPoly co).map (Rat.castHom ℝ)).eval u =
      evalModel (co.map (fun q : ℚ => (q:ℝ))) u := by
  simp only [qListPoly,Polynomial.map_sum,Polynomial.map_mul,Polynomial.map_C,
    Polynomial.map_pow,Polynomial.map_X,Polynomial.eval_finsetSum,
    Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,
    evalModel_map_rat]
  simp

theorem leafGap_sound (co : List ℚ) (E a b va vb : ℚ)
    (hc : leafGapCheck co E a b va vb=true) (u : ℝ)
    (hu : u∈Icc (a:ℝ) (b:ℝ)) :
    evalModel (co.map (fun q : ℚ => (q:ℝ))) u+(E:ℝ) ≤
      (va:ℝ)+((vb:ℝ)-va)/((b:ℝ)-a)*(u-a) := by
  have hh : bernCheck (qListPoly (leafGap co E a b va vb)) a b
      (leafGapTree co E a b va vb)=true := by
    rwa [← bernListCheck_eq]
  have hp := bernCheck_sound _ _ _ _ hh u hu
  have hlin (x y : ℚ) :
      ((qListPoly [x,y]).map (Rat.castHom ℝ)).eval u = (x:ℝ)+(y:ℝ)*u := by
    simp [qListPoly,coeffQ,Finset.sum_range_succ]
  simp only [leafGap,qListPoly_sub,Polynomial.map_sub,Polynomial.eval_sub,
    hlin,qListPoly_eval_real] at hp
  push_cast at hp
  linarith only [hp]

theorem leafGap_model (f : ℝ→ℝ) (co : List ℚ) (E a b va vb lo hi : ℚ)
    (hm : ModelsOn f (co.map (fun q : ℚ => (q:ℝ))) lo hi E)
    (hc : leafGapCheck co E a b va vb=true)
    (ha : lo≤a) (hb : b≤hi) :
    ∀u∈Icc (a:ℝ) (b:ℝ), f u ≤
      (va:ℝ)+((vb:ℝ)-va)/((b:ℝ)-a)*(u-a) := by
  intro u hu
  have haR : (lo:ℝ)≤(a:ℝ) := by exact_mod_cast ha
  have hbR : (b:ℝ)≤(hi:ℝ) := by exact_mod_cast hb
  have he := (abs_le.mp (hm.2.2 u ⟨haR.trans hu.1,hu.2.trans hbR⟩)).2
  have hp := leafGap_sound co E a b va vb hc u hu
  linarith only [he,hp]
#print axioms leafGap_model

end
end CatalanCore.Li2.DecayCert.NVLeafSemantic
