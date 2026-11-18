module
public import CatalanCore.Li2.DecayCert.Compile.Basic
public import CatalanCore.Uniform.Decay.Tools.BernsteinList
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 600000
open Polynomial Set
open scoped BigOperators
open CatalanCore.Uniform.Decay.Tools
namespace CatalanCore.Li2.DecayCert.LatticeGate

theorem scalarSum_value (xs : List SE) : (seSum xs).value=(xs.map ScalarExpr.value).sum := by
  have hh : ∀xs : List SE,∀b : SE,(xs.foldl seAdd b).value=b.value+(xs.map ScalarExpr.value).sum := by
    intro xs
    induction xs with
    | nil => intro b; simp
    | cons a xs ih =>
      intro b
      simp only [List.foldl_cons,List.map_cons,List.sum_cons]
      rw [ih,seAdd_value]
      ring
  simpa only [seSum,seRat_value,Rat.cast_zero,zero_add] using hh xs (seRat 0)

def affineCoeffSE (a : List SE) (n : ℕ) (u v : ℚ) (j : ℕ) : SE :=
  seScale (v^j) (seSum ((List.range (n+1-j)).map (fun l : ℕ =>
    seScale ((chooseFast (j+l) j:ℚ)*u^l) (seGet a (j+l)))))

theorem affineCoeffSE_value (a : List SE) (n : ℕ) (u v : ℚ) (j : ℕ) :
    (affineCoeffSE a n u v j).value=
      affCoeffs (fun i=>(seGet a i).value) n (u:ℝ) (v:ℝ) j := by
  unfold affineCoeffSE affCoeffs
  rw [seScale_value,scalarSum_value,List.map_map,list_sum_map_range,Finset.sum_Ico_eq_sum_range]
  simp only [Function.comp_def,seScale_value,chooseFast_eq,Nat.add_sub_cancel_left]
  push_cast
  rfl

def affineSE (a : List SE) (u v : ℚ) : List SE :=
  (List.range a.length).map (affineCoeffSE a (a.length-1) u v)

theorem evalModel_affineSE (a : List SE) (u v : ℚ) (t : ℝ) :
    evalModel ((affineSE a u v).map ScalarExpr.value) t=
      evalModel (a.map ScalarExpr.value) ((u:ℝ)+(v:ℝ)*t) := by
  by_cases ha : a=[]
  · subst a
    simp [affineSE,evalModel]
  · have hn : a.length-1+1=a.length := by cases a <;>simp_all
    simp only [affineSE,List.map_map]
    rw [evalModel_range,evalModel_map_scalar]
    simp only [Function.comp_def,affineCoeffSE_value]
    simpa only [peval,hn] using
      peval_affCoeffs (fun i=>(seGet a i).value) (a.length-1) (u:ℝ) (v:ℝ) t

def affineCompiled (m : CompiledModel) (u v : ℚ) : CompiledModel :=
  ⟨affineSE m.coeff u v,m.error⟩

def affineDomainCheck (u v R : ℚ) : Bool := decide (|u|+|v|≤R)

theorem affineCompiled_sound (m : CompiledModel) (u v R : ℚ) (f : ℝ→ℝ)
    (hm : Models f (m.coeff.map ScalarExpr.value) (R:ℝ) m.error.value)
    (hc : affineDomainCheck u v R=true) :
    ModelsOn (fun t=>f ((u:ℝ)+(v:ℝ)*t))
      ((affineCompiled m u v).coeff.map ScalarExpr.value) (-1) 1
      (affineCompiled m u v).error.value := by
  have hdom : |(u:ℝ)|+|(v:ℝ)|≤(R:ℝ) := by
    have h : |u|+|v|≤R := of_decide_eq_true hc
    exact_mod_cast h
  refine ⟨by norm_num,hm.2.1,?_⟩
  intro t ht
  have hmul : |(v:ℝ)*t|≤|(v:ℝ)| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (abs_le.mpr ht)
  have hpoint : |(u:ℝ)+(v:ℝ)*t|≤(R:ℝ) :=
    (abs_add_le _ _).trans (by linarith)
  change |f ((u:ℝ)+(v:ℝ)*t)-evalModel ((affineSE m.coeff u v).map ScalarExpr.value) t|≤m.error.value
  rw [evalModel_affineSE]
  exact hm.2.2 _ hpoint

#print axioms evalModel_affineSE
#print axioms affineCompiled_sound
end CatalanCore.Li2.DecayCert.LatticeGate
