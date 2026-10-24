module
public import CatalanArchive.CatalanFrames.P6Hybrid.ProfileDenominator
@[expose] public section
open Finset Filter CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid
namespace CatalanFrames.P6Hybrid
open CatalanFrames.HybCommon CatalanFrames.P6

theorem intervalBase_sum_le {r m : ℕ} (hr : 100≤r)
    (hm1 : r≤8*m) (hm2 : 8*m≤r+9) :
    (∑p∈(range (Bnd (p6Inst r m) r m)).filter Nat.Prime,(intervalBase r m p:ℝ)*Real.log p)≤
      extraG 3 Ecub 2 (badLog (p6Inst r m)) r m+
        ∑c∈({1,5}:Finset (ZMod 6)),clsSum 6 c (fun p=>(Wn r m p:ℝ)) 0 (Rp6 r c) := by
  let I:=p6Inst r m
  have B:=p6_badInfo r m
  apply sum_Bnd_le_gen B ({1,5}:Finset (ZMod 6)) (Rp6 r) r m (intervalBase r m)
    (fun p=>(Wn r m p:ℝ)) (fun _=>Nat.cast_nonneg _) (cntG I r m)
    (fun p hp=>(cntG_le I r m p hp).trans (by rw [B.L_eq]))
    (fun p hp h=>cntG_zero I r m p hp (by rw [B.L_eq];exact h))
  · intro p hp
    have H:=tropExp_leG B r m p (by omega) hp
    have hw:=p6_trop_le_Wn hp (by omega) hm1 hm2
    have hw': (tropVal (HW I.lev p r m):ℝ)≤(Wn r m p:ℝ):=by exact_mod_cast hw
    dsimp only [I] at *
    by_cases hb : p∈(p6Inst r m).cd.bad
    · have hb' : p=2 ∨ p=3 := by
        have H:=hb
        change p∈({2,3}:Finset ℕ) at H
        simpa only [mem_insert,mem_singleton] using H
      simpa only [intervalBase,if_pos hb',if_pos hb] using H
    · have hb' : ¬(p=2 ∨ p=3) := by
        have H:=hb
        change p∉({2,3}:Finset ℕ) at H
        simpa only [mem_insert,mem_singleton] using H
      simp only [hb,if_false] at H ⊢
      rw [intervalBase,if_neg hb',Nat.cast_max]
      apply max_le
      · linarith
      · have hh : (0:ℝ)≤((2*(r+m)*cntG I r m p:ℕ):ℝ):=Nat.cast_nonneg _
        linarith
  · exact fun p hp hb=>p6_cls r m p hp hb
  · intro c hc b hb hbc
    have hb' : b∈({2,3}:Finset ℕ):=hb
    simp only [mem_insert,mem_singleton] at hb' hc
    rcases hb' with rfl|rfl <;> rcases hc with rfl|rfl <;> exact absurd hbc (by decide)
  · intro c hc p hp hb hpc ht
    simp only [mem_insert,mem_singleton] at hc
    rcases hc with rfl|rfl
    · exact_mod_cast Wn_tail1 (cls_one hpc) ht hm1 hm2 hr
    · exact_mod_cast Wn_tail5 (cls_five hpc) ht hm1 hm2 hr

theorem intervalBase_sum_uniform (mf : ℕ→ℕ)
    (hadm : ∀r,r≤8*mf r ∧ 8*mf r≤r+9) :
    ∀ε>0,∀ᶠr:ℕ in atTop,
      (∑p∈(range (Bnd (p6Inst r (mf r)) r (mf r))).filter Nat.Prime,
        (intervalBase r (mf r) p:ℝ)*Real.log p)≤(10339/3072+ε)*(r:ℝ)^2 := by
  intro ε hε
  have hx:=(p6_badInfo 0 0).extra_small (ε/2) (by positivity)
  filter_upwards [p6_hsum mf hadm (ε/2) (by positivity),hx,eventually_ge_atTop 100]
    with r hsum hex hr
  have hmr : mf r≤r := by have:=hadm r;omega
  have H:=intervalBase_sum_le hr (hadm r).1 (hadm r).2
  have he:=hex (mf r) hmr
  change extraG 3 Ecub 2 (badLog (p6Inst r (mf r))) r (mf r)≤ε/2*(r:ℝ)^2 at he
  linarith
end CatalanFrames.P6Hybrid
