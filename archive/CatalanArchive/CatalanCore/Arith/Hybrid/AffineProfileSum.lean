module
public import CatalanCore.Arith.Hybrid.AffineDeficit
@[expose] public section
open Finset Filter Topology
namespace CatalanCore.Arith.Hybrid

/-- Disjoint affine windows cannot charge one prime more than once. -/
theorem sum_clsSum_le {ι : Type*} [DecidableEq ι] {M : ℕ}
    (s : Finset ι) (c : ι→ZMod M) (A B : ι→ℕ) (N : ℕ) (w : ℕ→ℝ)
    (hB : ∀i∈s,B i<N) (hw : ∀p,0≤w p)
    (hu : ∀p, p.Prime → ∀i∈s,∀j∈s,
      A i<p → p≤B i → (p : ZMod M)=c i →
      A j<p → p≤B j → (p : ZMod M)=c j → i=j) :
    (∑i∈s,clsSum M (c i) w (A i) (B i))≤
      ∑p∈(range N).filter Nat.Prime,w p*Real.log p := by
  classical
  let T := (range N).filter Nat.Prime
  have he : ∀i∈s, clsSum M (c i) w (A i) (B i)=
      ∑p∈T,if A i<p ∧ p≤B i ∧ (p : ZMod M)=c i then w p*Real.log p else 0 := by
    intro i hi
    rw [←Finset.sum_filter]
    unfold clsSum
    apply Finset.sum_congr
    · ext p
      simp only [T, mem_filter, mem_Ioc, mem_range]
      constructor
      · rintro ⟨⟨ha,hb⟩,hp,hc⟩
        exact ⟨⟨lt_of_le_of_lt hb (hB i hi),hp⟩,ha,hb,hc⟩
      · rintro ⟨⟨hpN,hp⟩,ha,hb,hc⟩
        exact ⟨⟨ha,hb⟩,hp,hc⟩
    · intro p hp; rfl
  have hsum := Finset.sum_congr rfl he
  rw [hsum, Finset.sum_comm]
  apply Finset.sum_le_sum
  intro p hp
  have hpp : p.Prime := (mem_filter.1 hp).2
  have hlog : 0≤Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
  rw [←Finset.sum_filter]
  have hcard : (s.filter (fun i => A i<p ∧ p≤B i ∧ (p : ZMod M)=c i)).card≤1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    obtain ⟨hi,hai,hbi,hci⟩ := mem_filter.1 hi
    obtain ⟨hj,haj,hbj,hcj⟩ := mem_filter.1 hj
    exact hu p hpp i hi j hj hai hbi hci haj hbj hcj
  simp only [sum_const, nsmul_eq_mul]
  have hcardR : ((s.filter (fun i => A i<p ∧ p≤B i ∧ (p : ZMod M)=c i)).card : ℝ)≤1 := by exact_mod_cast hcard
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hcardR (mul_nonneg (hw p) hlog)
end CatalanCore.Arith.Hybrid
