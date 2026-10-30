module

public import CatalanCore.Uniform.Content.RankProducer.ClosedCount
public import CatalanCore.Uniform.Content.UFSimple.Closed

@[expose] public section
set_option Elab.async false

/-! # The closed rank price (3.1) and Theorem R at one prime (lane C2L)

`Wk m r p ρ k z` is the number of border nodes of class `(k, z)`, in UF's window conventions
(`ovl`, `candL`, `candU`); `nsqC` the number of square `(1, 0)` fibres;

  `rankPrice = 2(r+m) - max(m + nsq, W(0,0) + W(1,0) + 2 nsq, W'(h,z), W'(h+1,z))`,

`h = r / p`, `W' = W` off the D0 shapes `k ≤ 1, z = 0` and `0` on them.
`exists_member_closed`: a `RankMember` of price `≤ rankPrice` for every retained set.
-/

namespace CatalanCore.Uniform.Content.RankProducer
open Finset CatalanCore CatalanCore.Basic CatalanCore.Uniform CatalanCore.Uniform.Content.Hybrid
  CatalanCore.Uniform.Content.Member CatalanCore.Uniform.Content.Wire CatalanCore.Uniform.Content.UFSimple
open scoped Classical

/-- `W(k, z)`: border nodes of class `(k, z)`, in UF's window conventions. -/
def Wk (m r p ρ k : ℕ) (z : Bool) : ℕ :=
  ovl r (r + 2 * m) (p * k + candL ρ z) (p * k + candU p ρ z)

/-- The number of square `(1, 0)` fibres, `|[r + 2m - p, min(r, ρ))|`. -/
def nsqC (m r p ρ : ℕ) : ℕ := min r ρ - (r + 2 * m - p)

/-- The bordered term of a shape, `0` on the D0 shapes `k ≤ 1, z = 0`. -/
def Wc (m r p ρ k : ℕ) (z : Bool) : ℕ := if k ≤ 1 ∧ z = false then 0 else Wk m r p ρ k z

/-- **The closed rank price (3.1).** -/
def rankPrice (m r p ρ : ℕ) : ℕ :=
  2 * (r + m) - max (max (m + nsqC m r p ρ)
      (Wk m r p ρ 0 false + Wk m r p ρ 1 false + 2 * nsqC m r p ρ))
    (max (max (Wc m r p ρ (r / p) false) (Wc m r p ρ (r / p) true))
      (max (Wc m r p ρ (r / p + 1) false) (Wc m r p ρ (r / p + 1) true)))

theorem div_eq_iff_win {t p k : ℕ} (hp : 0 < p) : t / p = k ↔ p * k ≤ t ∧ t < p * k + p := by
  constructor
  · rintro rfl
    have h1 := (Nat.le_div_iff_mul_le hp).1 (le_refl (t / p))
    have h2 := (Nat.div_lt_iff_lt_mul hp).1 (Nat.lt_succ_self (t / p))
    rw [Nat.succ_mul] at h2
    constructor
    · rw [Nat.mul_comm]; exact h1
    · rw [Nat.mul_comm]; exact h2
  · rintro ⟨h1, h2⟩
    refine le_antisymm (Nat.lt_succ_iff.1 ((Nat.div_lt_iff_lt_mul hp).2 ?_))
      ((Nat.le_div_iff_mul_le hp).2 (by rw [Nat.mul_comm]; exact h1))
    rw [Nat.succ_mul, Nat.mul_comm]; exact h2

/-- Border nodes of class `(k, z)` number `W(k, z)`. -/
theorem card_class (m r p ρ kk : ℕ) (zz : Bool) (hp : 0 < p) (hρ1 : 1 ≤ ρ) (hρp : ρ < p) :
    ((Ico r (r + 2 * m)).filter (fun t => t / p = kk ∧ decide (ρ ≤ t % p) = zz)).card =
      Wk m r p ρ kk zz := by
  unfold Wk
  rw [← card_Ico_filter_Icc]
  congr 1
  apply Finset.filter_congr
  intro t _
  have e := Nat.div_add_mod t p
  have hm := Nat.mod_lt t hp
  rw [div_eq_iff_win hp]
  cases zz
  · simp only [candL, candU, Bool.false_eq_true, eq_self_iff_true, if_true, if_false, ↓reduceIte,
      decide_eq_false_iff_not, not_le]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      have hk : t / p = kk := (div_eq_iff_win hp).2 ⟨h1, h2⟩
      rw [hk] at e
      omega
    · rintro ⟨h1, h2⟩
      have hk : t / p = kk := (div_eq_iff_win hp).2 ⟨by omega, by omega⟩
      rw [hk] at e
      refine ⟨⟨by omega, by omega⟩, by omega⟩
  · simp only [candL, candU, Bool.false_eq_true, eq_self_iff_true, if_true, if_false, ↓reduceIte,
      decide_eq_true_eq]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      have hk : t / p = kk := (div_eq_iff_win hp).2 ⟨h1, h2⟩
      rw [hk] at e
      omega
    · rintro ⟨h1, h2⟩
      have hk : t / p = kk := (div_eq_iff_win hp).2 ⟨by omega, by omega⟩
      rw [hk] at e
      refine ⟨⟨by omega, by omega⟩, by omega⟩

theorem card_cls_some (m r p ρ kk : ℕ) (zz : Bool) (hp : 0 < p) (hρ1 : 1 ≤ ρ) (hρp : ρ < p) :
    ((Ico r (r + 2 * m)).filter
        (fun t => inCls (some (kk, zz)) (t / p) (decide (ρ ≤ t % p)))).card = Wk m r p ρ kk zz := by
  rw [← card_class m r p ρ kk zz hp hρ1 hρp]
  congr 1
  exact Finset.filter_congr (fun t _ => Iff.rfl)

theorem card_cls_none (m r p ρ : ℕ) (hp : 0 < p) (hρ1 : 1 ≤ ρ) (hρp : ρ < p) :
    ((Ico r (r + 2 * m)).filter (fun t => inCls none (t / p) (decide (ρ ≤ t % p)))).card =
      Wk m r p ρ 0 false + Wk m r p ρ 1 false := by
  rw [← card_class m r p ρ 0 false hp hρ1 hρp, ← card_class m r p ρ 1 false hp hρ1 hρp,
    ← Finset.card_union_of_disjoint]
  · congr 1
    ext t
    simp only [Finset.mem_filter, Finset.mem_union]
    show (t ∈ Ico r (r + 2 * m) ∧ (t / p ≤ 1 ∧ decide (ρ ≤ t % p) = false)) ↔ _
    constructor
    · rintro ⟨h1, h2, h3⟩
      rcases Nat.lt_or_ge (t / p) 1 with h | h
      · left; exact ⟨h1, Nat.lt_one_iff.1 h, h3⟩
      · right; exact ⟨h1, le_antisymm h2 h, h3⟩
    · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
      · exact ⟨h1, by rw [h2]; exact Nat.zero_le 1, h3⟩
      · exact ⟨h1, le_of_eq h2, h3⟩
  · rw [Finset.disjoint_left]
    intro t h1 h2
    have e1 := (Finset.mem_filter.1 h1).2.1
    have e2 := (Finset.mem_filter.1 h2).2.1
    rw [e1] at e2
    exact absurd e2 (by decide)

theorem card_sqAll (m r p ρ : ℕ) : (sqAll r m p ρ).card = nsqC m r p ρ := by
  unfold sqAll nsqC; rw [Nat.card_Ico]

/-- A class with a border node has a digit `≤ (r + 2m) / p`. -/
theorem digit_le_of_Wk {m r p ρ kk : ℕ} {zz : Bool} (hp : 0 < p) (hρ1 : 1 ≤ ρ) (hρp : ρ < p)
    (hW : Wk m r p ρ kk zz ≠ 0) : kk ≤ (r + 2 * m) / p := by
  rw [← card_class m r p ρ kk zz hp hρ1 hρp] at hW
  obtain ⟨t, ht⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero hW)
  obtain ⟨h1, h2, -⟩ := Finset.mem_filter.1 ht
  rw [← h2]
  exact Nat.div_le_div_right (Finset.mem_Ico.1 h1).2.le

section Member
variable {G : BlockGeom} {r : ℕ}

/-- Theorem R for one line class. -/
theorem exists_member_cls (hs : HybShape G r) (T : Finset (G.geometry r).C)
    (Fr : Frame) (u q : Fin Fr.d → ℕ) (p : ℕ) [hp : Fact p.Prime] (B : ℕ)
    (hcoef : ∀ j, (frameDigamma Fr u q).c j ∈ S p) (hpq : ∀ j, ¬ p ∣ (frameDigamma Fr u q).q j)
    (hp3 : 3 ≤ p)
    (hbd : ∀ j, (frameDigamma Fr u q).q j * B + (frameDigamma Fr u q).u j ≤ p ^ 2)
    (hB : B < p ^ 2) (hBr : r + 2 * (G.geometry r).k ≤ B + 1)
    (hpm : 2 * (G.geometry r).k < p) (Lz Ez : Bool → ℕ → ℚ) (ρ : ℕ) (hρp : ρ < p)
    (hLf : ∀ x0 < p, ∀ d, (frameDigamma Fr u q).Lf p (x0 + p * d) = Lz (decide (ρ ≤ x0)) d)
    (hEf : ∀ x0 < p, ∀ d, (frameDigamma Fr u q).E p (x0 + p * d) = Ez (decide (ρ ≤ x0)) d)
    (hE0 : Ez false 0 = 0)
    (hBnd : ∀ (kk : ℕ) (z : Bool), kk ≤ (r + 2 * (G.geometry r).k) / p →
      clsBnd (Lz z) (Ez z) kk z < p)
    (l : LineCls) (hl : castV p (clsMomL Lz Ez l) ≠ 0) :
    ∃ M : RankMember Fr u q (fun a : (G.geometry r).C => (a : ℕ)) (G.geometry r).xs
        (G.geometry r).ys T p,
      M.price + max ((G.geometry r).k + (sqAll r (G.geometry r).k p ρ).card)
        (((Ico r (r + 2 * (G.geometry r).k)).filter
            (fun t => inCls l (t / p) (decide (ρ ≤ t % p)))).card +
          2 * (if l = none then (sqAll r (G.geometry r).k p ρ).card else 0)) ≤
        2 * (r + (G.geometry r).k) := by
  obtain ⟨RA, CA, SQ, hA, hkill, hscore⟩ := exists_assign hs T hpm hρp
  obtain ⟨M, hM⟩ := closed_member hs T Fr u q p B hcoef hpq hp3 hbd hB hBr hpm Lz Ez ρ hLf hEf
    hE0 hBnd RA CA SQ hA l hl
  refine ⟨M, ?_⟩
  have hT : T.card ≤ r := by
    have h1 := Finset.card_le_univ T
    rw [Fintype.card_coe] at h1
    have h2 : ((G.geometry r).C).card = r := by rw [hs.C_eq, Finset.card_range]
    omega
  have h3 := hscore l
  generalize (if l = none then SQ.card else 0) = b at hM h3
  generalize (if l = none then (sqAll r (G.geometry r).k p ρ).card else 0) = a at h3 ⊢
  omega

/-- **Theorem R at one prime.**  A `RankMember` of price at most `rankPrice`. -/
theorem exists_member_closed (hs : HybShape G r) (T : Finset (G.geometry r).C)
    (Fr : Frame) (u q : Fin Fr.d → ℕ) (p : ℕ) [hp : Fact p.Prime] (B : ℕ)
    (hcoef : ∀ j, (frameDigamma Fr u q).c j ∈ S p) (hpq : ∀ j, ¬ p ∣ (frameDigamma Fr u q).q j)
    (hp3 : 3 ≤ p)
    (hbd : ∀ j, (frameDigamma Fr u q).q j * B + (frameDigamma Fr u q).u j ≤ p ^ 2)
    (hB : B < p ^ 2) (hBr : r + 2 * (G.geometry r).k ≤ B + 1)
    (hpm : 2 * (G.geometry r).k < p) (Lz Ez : Bool → ℕ → ℚ) (ρ : ℕ) (hρ1 : 1 ≤ ρ) (hρp : ρ < p)
    (hLf : ∀ x0 < p, ∀ d, (frameDigamma Fr u q).Lf p (x0 + p * d) = Lz (decide (ρ ≤ x0)) d)
    (hEf : ∀ x0 < p, ∀ d, (frameDigamma Fr u q).E p (x0 + p * d) = Ez (decide (ρ ≤ x0)) d)
    (hE0 : Ez false 0 = 0)
    (hBnd : ∀ (kk : ℕ) (z : Bool), kk ≤ (r + 2 * (G.geometry r).k) / p →
      clsBnd (Lz z) (Ez z) kk z < p) :
    ∃ M : RankMember Fr u q (fun a : (G.geometry r).C => (a : ℕ)) (G.geometry r).xs
        (G.geometry r).ys T p, M.price ≤ rankPrice (G.geometry r).k r p ρ := by
  have hp0 := hp.out.pos
  -- the D0 member
  obtain ⟨M0, hM0⟩ := exists_member_cls hs T Fr u q p B hcoef hpq hp3 hbd hB hBr hpm Lz Ez ρ hρp
    hLf hEf hE0 hBnd none (castV_one_ne_zero _)
  rw [card_cls_none (G.geometry r).k r p ρ hp0 hρ1 hρp, card_sqAll] at hM0
  rw [if_pos rfl] at hM0
  -- the bordered members
  have hsome : ∀ (kk : ℕ) (zz : Bool), Wk (G.geometry r).k r p ρ kk zz ≠ 0 → ¬ (kk ≤ 1 ∧ zz = false) →
      ∃ M : RankMember Fr u q (fun a : (G.geometry r).C => (a : ℕ)) (G.geometry r).xs
        (G.geometry r).ys T p, M.price + Wk (G.geometry r).k r p ρ kk zz ≤ 2 * (r + (G.geometry r).k) := by
    intro kk zz hW hD
    have hk := digit_le_of_Wk hp0 hρ1 hρp hW
    obtain ⟨M, hM⟩ := exists_member_cls hs T Fr u q p B hcoef hpq hp3 hbd hB hBr hpm Lz Ez ρ hρp
      hLf hEf hE0 hBnd (some (kk, zz)) (clsMom_ne (Lz zz) (Ez zz) kk zz hD (hBnd kk zz hk))
    rw [card_cls_some (G.geometry r).k r p ρ kk zz hp0 hρ1 hρp] at hM
    rw [if_neg (Option.some_ne_none _)] at hM
    exact ⟨M, by omega⟩
  -- every term of the max is attained by some member
  have hWc : ∀ (kk : ℕ) (zz : Bool), ∃ M : RankMember Fr u q (fun a : (G.geometry r).C => (a : ℕ))
      (G.geometry r).xs (G.geometry r).ys T p, M.price + Wc (G.geometry r).k r p ρ kk zz ≤ 2 * (r + (G.geometry r).k) := by
    intro kk zz
    unfold Wc
    split_ifs with hD
    · exact ⟨M0, by omega⟩
    · by_cases hW : Wk (G.geometry r).k r p ρ kk zz = 0
      · exact ⟨M0, by rw [hW]; omega⟩
      · exact hsome kk zz hW hD
  unfold rankPrice
  rcases max_choice (max ((G.geometry r).k + nsqC (G.geometry r).k r p ρ)
      (Wk (G.geometry r).k r p ρ 0 false + Wk (G.geometry r).k r p ρ 1 false + 2 * nsqC (G.geometry r).k r p ρ))
      (max (max (Wc (G.geometry r).k r p ρ (r / p) false) (Wc (G.geometry r).k r p ρ (r / p) true))
        (max (Wc (G.geometry r).k r p ρ (r / p + 1) false) (Wc (G.geometry r).k r p ρ (r / p + 1) true))) with h | h <;>
    rw [h]
  · exact ⟨M0, by omega⟩
  · rcases max_choice (max (Wc (G.geometry r).k r p ρ (r / p) false) (Wc (G.geometry r).k r p ρ (r / p) true))
        (max (Wc (G.geometry r).k r p ρ (r / p + 1) false) (Wc (G.geometry r).k r p ρ (r / p + 1) true)) with h' | h' <;>
      rw [h']
    · rcases max_choice (Wc (G.geometry r).k r p ρ (r / p) false) (Wc (G.geometry r).k r p ρ (r / p) true) with h'' | h'' <;>
        rw [h'']
      · obtain ⟨M, hM⟩ := hWc (r / p) false; exact ⟨M, by omega⟩
      · obtain ⟨M, hM⟩ := hWc (r / p) true; exact ⟨M, by omega⟩
    · rcases max_choice (Wc (G.geometry r).k r p ρ (r / p + 1) false) (Wc (G.geometry r).k r p ρ (r / p + 1) true) with h'' | h'' <;>
        rw [h'']
      · obtain ⟨M, hM⟩ := hWc (r / p + 1) false; exact ⟨M, by omega⟩
      · obtain ⟨M, hM⟩ := hWc (r / p + 1) true; exact ⟨M, by omega⟩

end Member

#print axioms exists_member_closed
end CatalanCore.Uniform.Content.RankProducer
