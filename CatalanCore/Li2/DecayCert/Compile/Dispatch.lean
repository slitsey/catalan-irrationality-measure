module
public import CatalanCore.Li2.DecayCert.Compile.DiscModel
public import CatalanCore.Li2.DecayCert.Compile.Elementary
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay CatalanCore.Tools.Joukowski
noncomputable section

theorem cq_eq_zero_of_sq (a : CQ) (ha : cqSq a=0) : a=(0,0) := by
  have h := ha
  dsimp only [cqSq] at h
  apply Prod.ext <;> dsimp only <;> nlinarith [sq_nonneg a.1,sq_nonneg a.2]

theorem compileModel_sound (lo hi : ℚ) (e : CellExpr) (w : ModelWitness)
    (m : CompiledModel) (hdom : lo ≤ hi) (hpos : PositiveSources e)
    (hc : compileModel lo hi e w=some m) :
    ModelsOn e.value (m.coeff.map ScalarExpr.value) lo hi m.error.value := by
  induction w generalizing e m with
  | simple =>
    cases e <;> simp only [compileModel] at hc
    all_goals try contradiction
    all_goals cases Option.some.inj hc
    · simpa only [CellExpr.value,List.map_cons,List.map_nil,seRat_value,Rat.cast_zero] using
        ModelsOn.constant _ lo hi (by exact_mod_cast hdom)
    · simpa [CellExpr.value,seRat_value,Rat.cast_zero,Rat.cast_one] using
        ModelsOn.linear 0 1 lo hi (by exact_mod_cast hdom)
    · simpa only [CellExpr.value,List.map_cons,List.map_nil,seRat_value,Rat.cast_zero] using
        ModelsOn.linear _ _ lo hi (by exact_mod_cast hdom)
  | order J =>
    cases e <;> simp only [compileModel] at hc
    all_goals try contradiction
    cases Option.some.inj hc
    exact polynomial_compile_model _ lo hi J hdom
  | regular w =>
    cases e with
    | fre a b => exact regularCompile_fre_sound a b lo hi w m hdom hc
    | xlog a b => exact regularCompile_xlog_sound a b lo hi w m hc
    | logAffine a b => exact regularCompile_log_sound a b lo hi w m hdom hc
    | invPow a b k => exact regularCompile_inv_sound a b k lo hi w m hdom hc
    | ulog =>
      simp only [compileModel] at hc
      split_ifs at hc with hg
      obtain ⟨rfl,hhi⟩ := hg
      cases Option.some.inj hc
      simpa only [CellExpr.value,Rat.cast_zero] using ulogCompile_sound hi hhi w.terms
    | _ => simp [compileModel,regularCompile] at hc
  | segOwn J n =>
    cases e <;> simp only [compileModel] at hc
    all_goals try contradiction
    exact ownCompile_sound _ _ _ lo hi J n m hpos hc
  | segDisc w =>
    cases e <;> simp only [compileModel] at hc
    all_goals try contradiction
    exact (segDiscCompile_model _ _ _ (max |lo| |hi|) w m hpos hc).onIcc lo hi
      (by exact_mod_cast hdom) (fun u hu => by simpa only [Rat.cast_max,Rat.cast_abs] using abs_le_rat_radius lo hi u hu)
  | add wa wb iha ihb =>
    cases e <;> simp only [compileModel] at hc
    all_goals try contradiction
    rename_i a b
    cases hma : compileModel lo hi a wa with
    | none => simp [hma] at hc
    | some ma =>
      cases hmb : compileModel lo hi b wb with
      | none => simp [hma,hmb] at hc
      | some mb =>
        simp only [hma,hmb,Option.bind_some,Option.pure_def] at hc
        cases Option.some.inj hc
        exact (iha a ma hpos.1 hma).add_scalar (ihb b mb hpos.2 hmb)
  | scale wa iha =>
    cases e <;> simp only [compileModel] at hc
    all_goals try contradiction
    rename_i c a
    cases hma : compileModel lo hi a wa with
    | none => simp [hma] at hc
    | some ma =>
      simp only [hma,Option.bind_some,Option.pure_def] at hc
      cases Option.some.inj hc
      simpa only [CellExpr.value,seScale_value,Rat.cast_abs] using (iha a ma hpos hma).scale_scalar c
  | seeds terms =>
    cases e <;> simp only [compileModel] at hc
    all_goals try contradiction
    · rename_i a b
      split_ifs at hc with hsingle hseed
      · obtain ⟨ha,rfl,rfl⟩ := hsingle
        have haz := cq_eq_zero_of_sq a ha
        subst a
        cases Option.some.inj hc
        refine ⟨le_rfl,by simp [seRat_value],?_⟩
        intro u hu
        have hu0 : u=0 := by simpa only [Rat.cast_zero] using le_antisymm hu.2 hu.1
        subst u
        simp [CellExpr.value,cqReal,evalModel,seRat_value]
      · obtain ⟨ha,hb,rfl,hhi⟩ := hseed
        have haz := cq_eq_zero_of_sq a ha
        subst a
        cases Option.some.inj hc
        simpa only [seScale_value,Rat.cast_abs,Rat.cast_zero] using fre_seed_model b (cqReal_ne_of_cqSq_ne b hb) hi hhi terms
    · rename_i a b
      split_ifs at hc with hg
      obtain ⟨rfl,hb,rfl,hhi⟩ := hg
      cases Option.some.inj hc
      simpa only [seScale_value,Rat.cast_zero] using xlog_seed_model b hi hb hhi terms
#print axioms cq_eq_zero_of_sq
#print axioms compileModel_sound
end
end CatalanCore.Li2.DecayCert
