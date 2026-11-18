module
public import CatalanCore.Li2.DecayCert.Covers.Clipped
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
noncomputable section

theorem option_mapM_member {α β : Type*} (xs : List α) (f : α → Option β) :
    ∀ ys : List β,xs.mapM f=some ys → ∀ y ∈ ys,∃ x ∈ xs,f x=some y := by
  induction xs with
  | nil => intro ys hm; have he : ([]:List β)=ys := Option.some.inj hm; subst ys; simp
  | cons a xs ih =>
    intro ys hm y hy
    cases ha : f a with
    | none => simp [ha] at hm
    | some b =>
      cases ht : xs.mapM f with
      | none => simp [ha,ht] at hm
      | some bs =>
        simp only [List.mapM_cons,ha,ht,Option.bind_some,Option.pure_def] at hm
        cases Option.some.inj hm
        rcases List.mem_cons.mp hy with rfl | hy
        · exact ⟨a,List.mem_cons_self,ha⟩
        · rcases ih bs ht y hy with ⟨x,hx,hxy⟩
          exact ⟨x,List.mem_cons_of_mem a hx,hxy⟩

theorem clippedParentLower_pointwise (f : ℝ → ℝ) (lo hi L : ℚ) (rows : List (QInterval×ℚ))
    (hparents : ∀ r ∈ rows,∀ x ∈ Icc (r.1.left:ℝ) (r.1.right:ℝ),(r.2:ℝ) ≤ f x)
    (hc : clippedParentLower lo hi rows=some L) :
    ∀ x ∈ Icc (lo:ℝ) (hi:ℝ),(L:ℝ) ≤ f x := by
  let clipped := (rows.map (fun r => ((⟨max lo r.1.left,min hi r.1.right⟩:QInterval),r.2))).filter (fun r => r.1.left < r.1.right)
  have hc' : (match clipped with
    | [] => none
    | r::rs => if chainCheck lo hi ((r::rs).map Prod.fst) then some (rs.foldl (fun v r => min v r.2) r.2) else none)=some L := hc
  cases hcl : clipped with
  | nil => simp [hcl] at hc'
  | cons r rs =>
    rw [hcl] at hc'
    dsimp only at hc'
    split_ifs at hc' with hchain
    have hmin : rs.foldl (fun v r => min v r.2) r.2=L := Option.some.inj hc'
    have hcover := (chainCheck_sound lo hi ((r::rs).map Prod.fst) hchain).2.2.2
    have hhead := hchain
    simp only [List.map_cons,chainCheck,Bool.and_eq_true,decide_eq_true_eq] at hhead
    intro x hx
    have hxsome : ∃ v ∈ r::rs,x ∈ Icc (v.1.left:ℝ) (v.1.right:ℝ) := by
      by_cases he : x=(lo:ℝ)
      · refine ⟨r,List.mem_cons_self,?_⟩
        have hleft : (r.1.left:ℝ)=(lo:ℝ) := by exact_mod_cast hhead.1.1
        have hright : (r.1.left:ℝ)<(r.1.right:ℝ) := by exact_mod_cast hhead.1.2.1
        constructor <;> linarith
      · have hxo : x ∈ Ioc (lo:ℝ) (hi:ℝ) := ⟨lt_of_le_of_ne hx.1 (Ne.symm he),hx.2⟩
        rw [hcover] at hxo
        rcases mem_iUnion.1 hxo with ⟨q,hq⟩
        rcases mem_iUnion.1 hq with ⟨hq,hxq⟩
        rcases List.mem_map.mp hq with ⟨v,hv,rfl⟩
        exact ⟨v,hv,hxq.1.le,hxq.2⟩
    rcases hxsome with ⟨v,hv,hxv⟩
    have hvclip : v ∈ clipped := by rw [hcl]; exact hv
    rcases List.mem_filter.mp hvclip with ⟨hvmap,hvlt⟩
    rcases List.mem_map.mp hvmap with ⟨orig,horig,heq⟩
    have hL : L ≤ v.2 := by
      rw [← hmin]
      rcases List.mem_cons.mp hv with rfl | hv
      · exact foldl_min_le_initial rs v.2
      · exact foldl_min_le_member rs r.2 v hv
    have hxorig : x ∈ Icc (orig.1.left:ℝ) (orig.1.right:ℝ) := by
      rw [← heq] at hxv
      simp only [Rat.cast_max,Rat.cast_min] at hxv
      exact ⟨(le_max_right _ _).trans hxv.1,hxv.2.trans (min_le_right _ _)⟩
    have hval : v.2=orig.2 := (congrArg Prod.snd heq).symm
    exact (show (L:ℝ) ≤ (v.2:ℝ) by exact_mod_cast hL).trans (by rw [hval]; exact hparents orig horig x hxorig)
#print axioms option_mapM_member
#print axioms clippedParentLower_pointwise
end
end CatalanCore.Li2.DecayCert
