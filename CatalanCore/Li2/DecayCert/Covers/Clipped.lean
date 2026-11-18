module
public import CatalanCore.Li2.DecayCert.BentSpec
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
noncomputable section

theorem foldl_min_le_initial (rs : List (QInterval×ℚ)) (a : ℚ) :
    rs.foldl (fun v r => min v r.2) a ≤ a := by
  induction rs generalizing a with
  | nil => exact le_rfl
  | cons r rs ih => exact (ih (min a r.2)).trans (min_le_left _ _)

theorem foldl_min_le_member (rs : List (QInterval×ℚ)) (a : ℚ) (r : QInterval×ℚ) (hr : r ∈ rs) :
    rs.foldl (fun v r => min v r.2) a ≤ r.2 := by
  induction rs generalizing a with
  | nil => simp at hr
  | cons q rs ih =>
    rcases List.mem_cons.mp hr with rfl | hr
    · exact (foldl_min_le_initial rs (min a r.2)).trans (min_le_right _ _)
    · exact ih (min a q.2) hr

theorem clippedParentLower_sound (μ : Measure ℝ) (f : ℝ → ℝ)
    (lo hi L : ℚ) (rows : List (QInterval×ℚ))
    (hatom : ∀ x : ℝ,μ {x}=0)
    (hparents : ∀ r ∈ rows,∀ᵐ x ∂μ.restrict (Icc (r.1.left:ℝ) (r.1.right:ℝ)),(r.2:ℝ) ≤ f x)
    (hc : clippedParentLower lo hi rows=some L) :
    ∀ᵐ x ∂μ.restrict (Icc (lo:ℝ) (hi:ℝ)),(L:ℝ) ≤ f x := by
  let clipped := (rows.map (fun r => ((⟨max lo r.1.left,min hi r.1.right⟩:QInterval),r.2))).filter (fun r => r.1.left < r.1.right)
  have hglobal : ∀ᵐ x ∂μ,∀ r ∈ rows,x ∈ Icc (r.1.left:ℝ) (r.1.right:ℝ) → (r.2:ℝ) ≤ f x := by
    clear hc clipped
    induction rows with
    | nil => simp
    | cons r rs ih =>
      have hr := hparents r List.mem_cons_self
      rw [ae_restrict_iff' measurableSet_Icc] at hr
      have hs := ih (fun q hq => hparents q (List.mem_cons_of_mem r hq))
      filter_upwards [hr,hs] with x hx hxs
      intro q hq hqx
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hx hqx
      · exact hxs q hq hqx
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
    have hnot : ∀ᵐ x ∂μ,x ≠ (lo:ℝ) := by
      simpa only [mem_singleton_iff] using measure_eq_zero_iff_ae_notMem.mp (hatom (lo:ℝ))
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hglobal,hnot] with x hx hxn
    intro hxr
    have hxin : x ∈ Ioc (lo:ℝ) (hi:ℝ) := ⟨lt_of_le_of_ne hxr.1 (Ne.symm hxn),hxr.2⟩
    rw [hcover] at hxin
    rcases mem_iUnion.1 hxin with ⟨q,hq⟩
    rcases mem_iUnion.1 hq with ⟨hq,hxq⟩
    rcases List.mem_map.mp hq with ⟨v,hv,hvq⟩
    subst q
    have hvclip : v ∈ clipped := by rw [hcl]; exact hv
    rcases List.mem_filter.mp hvclip with ⟨hvmap,hvlt⟩
    rcases List.mem_map.mp hvmap with ⟨orig,horig,heq⟩
    have hL : L ≤ v.2 := by
      rw [← hmin]
      rcases List.mem_cons.mp hv with rfl | hv
      · exact foldl_min_le_initial rs v.2
      · exact foldl_min_le_member rs r.2 v hv
    have hxorig : x ∈ Icc (orig.1.left:ℝ) (orig.1.right:ℝ) := by
      rw [← heq] at hxq
      simp only [Rat.cast_max,Rat.cast_min] at hxq
      exact ⟨(le_max_right _ _).trans hxq.1.le,hxq.2.trans (min_le_right _ _)⟩
    have hval : v.2=orig.2 := congrArg Prod.snd heq |>.symm
    exact (show (L:ℝ) ≤ (v.2:ℝ) by exact_mod_cast hL).trans (by rw [hval]; exact hx orig horig hxorig)
#print axioms foldl_min_le_initial
#print axioms foldl_min_le_member
#print axioms clippedParentLower_sound
end
end CatalanCore.Li2.DecayCert
