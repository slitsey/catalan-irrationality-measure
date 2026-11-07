module

public import CatalanCore.Uniform.Bank.Chi3Content.Win1
public import CatalanCore.Uniform.Bank.Chi3Content.Win5

@[expose] public section

/-!
# `HasContent` of the chi_{-3} common-minor family with the M3D layer (lane B, B3c)

`hasContent_m3 : HasContent (commonMinorFam p6Frame Quarter.Adm d) Λ'` with
`Λ' = 339258406689121/82516315939200 - 853129/196035840`, the old periodic content
(`Quarter.Periodic.hasContent`) minus the exact integral of the M3D saving.
-/

open Finset Filter CatalanCore CatalanCore.Rect CatalanCore.Arith CatalanCore.Arith.Hybrid
  CatalanFrames.HybCommon CatalanFrames.P6 CatalanFrames.P6Hybrid CatalanFrames.P6Hybrid.Quarter
  CatalanFrames.P6Hybrid.Quarter.Periodic

set_option maxHeartbeats 3200000
set_option maxRecDepth 4000

namespace CatalanCore.Uniform.Bank.Chi3Content

/-- Pieces of the new class-1 chain after the prefix: refined first piece, then the old tail. -/
noncomputable def lpNew1 : List Piece := newFirst1 ++ Quarter.lp1.tail
noncomputable def lpNew5 : List Piece := newFirst5 ++ Quarter.lp5.tail

theorem lpNew1_chain : Chain (1/4) lpNew1 := by
  unfold lpNew1
  rw [chain_append, newFirst1_end]
  refine ⟨newFirst1_chain, ?_⟩
  simp only [Quarter.lp1, List.tail_cons, Chain, mkPiece]; norm_num

theorem lpNew5_chain : Chain (1/4) lpNew5 := by
  unfold lpNew5
  rw [chain_append, newFirst5_end]
  refine ⟨newFirst5_chain, ?_⟩
  simp only [Quarter.lp5, List.tail_cons, Chain, mkPiece]; norm_num

theorem lpNew1_end : lastEnd (1/4) lpNew1 = 9 := by
  unfold lpNew1
  rw [lastEnd_append, newFirst1_end]
  simp only [Quarter.lp1, List.tail_cons, lastEnd, mkPiece]; norm_num

theorem lpNew5_end : lastEnd (1/4) lpNew5 = 9 := by
  unfold lpNew5
  rw [lastEnd_append, newFirst5_end]
  simp only [Quarter.lp5, List.tail_cons, lastEnd, mkPiece]; norm_num

theorem lpNew1_int : (5/2 : ℝ) * (1/4) + listInt lpNew1 = 2614595/576576 := by
  unfold lpNew1
  rw [listInt_append]
  simp only [newFirst1, Quarter.lp1, List.tail_cons, listInt, Piece.int, mkPiece]
  norm_num

theorem lpNew5_int : (5/2 : ℝ) * (1/4) + listInt lpNew5 = 13924511/3769920 := by
  unfold lpNew5
  rw [listInt_append]
  simp only [newFirst5, Quarter.lp5, List.tail_cons, listInt, Piece.int, mkPiece]
  norm_num

theorem covers_of_le {c : ZMod 6} {r : ℕ} {P : Piece} {w v : ℕ → ℝ} (hle : ∀ p, v p ≤ w p)
    (h : Covers c w r P) : Covers c v r P :=
  fun p h1 h2 h3 h4 => (hle p).trans (h p h1 h2 h3 h4)

theorem lpNew1_covers {r m : ℕ} (hm1 : r ≤ 4 * m) (hm2 : 4 * m ≤ r + 3) (hr : 100 ≤ r) :
    ∀ P ∈ lpNew1, Covers (1 : ZMod 6) (fun p => (Wn r m p : ℝ)) r P := by
  intro P hP
  have hle : ∀ p, (Wn r m p : ℝ) ≤ (Quarter.W r m p : ℝ) := fun p => by exact_mod_cast Wn_le_W r m p
  unfold lpNew1 at hP
  rcases List.mem_append.mp hP with hP | hP
  · exact newFirst1_covers hm1 hm2 hr P hP
  · simp only [Quarter.lp1, List.tail_cons, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [covers_of_le hle (c1_2 hm1 hm2 hr), covers_of_le hle (c1_3 hm1 hm2 hr),
      covers_of_le hle (c1_4 hm1 hm2 hr), covers_of_le hle (c1_5 hm1 hm2 hr),
      covers_of_le hle (c1_6 hm1 hm2 hr), covers_of_le hle (c1_7 hm1 hm2 hr),
      covers_of_le hle (c1_8 hm1 hm2 hr), covers_of_le hle (c1_9 hm1 hm2 hr)]

theorem lpNew5_covers {r m : ℕ} (hm1 : r ≤ 4 * m) (hm2 : 4 * m ≤ r + 3) (hr : 100 ≤ r) :
    ∀ P ∈ lpNew5, Covers (5 : ZMod 6) (fun p => (Wn r m p : ℝ)) r P := by
  intro P hP
  have hle : ∀ p, (Wn r m p : ℝ) ≤ (Quarter.W r m p : ℝ) := fun p => by exact_mod_cast Wn_le_W r m p
  unfold lpNew5 at hP
  rcases List.mem_append.mp hP with hP | hP
  · exact newFirst5_covers hm1 hm2 hr P hP
  · simp only [Quarter.lp5, List.tail_cons, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [covers_of_le hle (c5_2 hm1 hm2 hr), covers_of_le hle (c5_3 hm1 hm2 hr),
      covers_of_le hle (c5_4 hm1 hm2 hr), covers_of_le hle (c5_5 hm1 hm2 hr),
      covers_of_le hle (c5_6 hm1 hm2 hr), covers_of_le hle (c5_7 hm1 hm2 hr),
      covers_of_le hle (c5_8 hm1 hm2 hr)]

/-- One summation argument for the refined weight `Wn`. -/
theorem class_refined' (c : ZMod 6) (hc : IsUnit c)
    (hgood : ∀ p : ℕ, (p : ZMod 6) = c → p % 6 = 1 ∨ p % 6 = 5)
    (l : List Piece) (I : ℝ) (hchain : Chain (1/4) l)
    (hend : lastEnd (1/4) l = 9)
    (hint : (5/2 : ℝ) * (1/4) + listInt l = I)
    (hcovers : ∀ {r m : ℕ}, Adm r m → 100 ≤ r →
      ∀ P ∈ l, Covers c (fun p => (Wn r m p : ℝ)) r P)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ m, Adm r m →
      clsSum 6 c (fun p => (Wn r m p : ℝ)) 0 (9 * r) ≤
        (r : ℝ) ^ 2 * ((I - (3163/768 - 339258406689121/82516315939200) + ε/68)/2 + ε/4) := by
  have hch : Chain (1/68) ((quarterD1Prefix 16) ++ l) := by
    rw [chain_append, quarterD1Prefix16_end]
    exact ⟨quarterD1Prefix16_chain, hchain⟩
  have hpref : ∀ᶠ r : ℕ in atTop, ∀ m, Adm r m → ∀ p,
      p ≤ ⌊(1/68 : ℝ) * r⌋₊ → p.Prime → (p : ZMod 6) = c →
      (Wn r m p : ℝ) ≤ (5/2 : ℝ) * r + 2 := by
    apply Filter.Eventually.of_forall
    intro r m ha p _ _ _
    have hW : Quarter.W r m p ≤ 2 * r + 2 * m := by
      unfold Quarter.W Hb; split_ifs <;> omega
    have hle := (Wn_le_W r m p).trans hW
    have hleR : (Wn r m p : ℝ) ≤ (2 * r + 2 * m : ℕ) := by exact_mod_cast hle
    have hmR : (4 * m : ℝ) ≤ r + 3 := by exact_mod_cast ha.2
    push_cast at hleR
    nlinarith
  have hcov : ∀ᶠ r : ℕ in atTop, ∀ m, Adm r m →
      ∀ P ∈ quarterD1Prefix 16 ++ l, Covers c (fun p => (Wn r m p : ℝ)) r P := by
    filter_upwards [eventually_ge_atTop 100] with r hr100
    intro m ha P hP
    rcases List.mem_append.mp hP with hP | hP
    · exact quarterD1Prefix_covers ha.1 ha.2
        (fun p _ hpc => (Wn_le_sharp r m p).trans (sharp_exact r m p (hgood p hpc))) 16 P hP
    · exact hcovers ha hr100 P hP
  have h := CatalanFrames.HybGen.class_sum_of_family hc Adm (fun r m p => (Wn r m p : ℝ))
    (5/2) (1/68) 2 (by norm_num) (by norm_num) (quarterD1Prefix 16 ++ l)
    hch hpref hcov (ε := ε/4) (by positivity)
  filter_upwards [h] with r hr
  intro m ha
  have hh := hr m ha
  have heq : lastEnd (1/68) (quarterD1Prefix 16 ++ l) = 9 := by
    rw [lastEnd_append, quarterD1Prefix16_end, hend]
  have hfloor : ⌊(9 : ℝ) * (r : ℝ)⌋₊ = 9 * r := by
    rw [show (9 : ℝ) * (r : ℝ) = ((9 * r : ℕ) : ℝ) by push_cast; ring, Nat.floor_natCast]
  rw [heq, hfloor] at hh
  have htot : (Nat.totient 6 : ℝ) = 2 := by rw [show Nat.totient 6 = 2 by decide]; norm_num
  have hi : (5/2 : ℝ) * (1/68) + listInt (quarterD1Prefix 16 ++ l) =
      I - (3163/768 - 339258406689121/82516315939200) := by
    rw [listInt_append]
    linarith [quarterD1Prefix16_integral]
  rw [htot, hi] at hh
  have hs := sq_nonneg (r : ℝ)
  nlinarith

/-- The refined constant. -/
def LamNew : ℚ := 4744590251372789 / 1155228423148800

theorem hsum' : ∀ ε > 0, ∀ᶠ r : ℕ in atTop, ∀ m, Adm r m →
    ∑ c ∈ ({1, 5} : Finset (ZMod 6)), clsSum 6 c (fun p => (Wn r m p : ℝ)) 0 (9 * r) ≤
      ((LamNew : ℝ) + ε) * (r : ℝ) ^ 2 := by
  intro ε hε
  have h1 := class_refined' 1 (by decide) (fun p h => Or.inl (cls_one h)) lpNew1 (2614595/576576)
    lpNew1_chain lpNew1_end lpNew1_int (fun ha hr => lpNew1_covers ha.1 ha.2 hr) hε
  have h5 := class_refined' 5 (by decide) (fun p h => Or.inr (cls_five h)) lpNew5 (13924511/3769920)
    lpNew5_chain lpNew5_end lpNew5_int (fun ha hr => lpNew5_covers ha.1 ha.2 hr) hε
  filter_upwards [h1, h5] with r hr1 hr5 m ha
  rw [Finset.sum_pair (by decide : (1 : ZMod 6) ≠ 5)]
  have ha1 := hr1 m ha
  have ha5 := hr5 m ha
  have hL : (LamNew : ℝ) = 4744590251372789 / 1155228423148800 := by
    unfold LamNew; push_cast; norm_num
  rw [hL]
  nlinarith [mul_nonneg hε.le (sq_nonneg (r : ℝ))]

theorem log_content_m3 : ∀ ε > 0, ∀ᶠ r : ℕ in atTop, ∀ m, Adm r m →
    Real.log (Dnew r m) ≤ ((LamNew : ℝ) + ε) * (r : ℝ) ^ 2 := by
  intro ε hε
  have hx := (p6_badInfo 0 0).extra_small (ε/2) (by positivity)
  filter_upwards [hsum' (ε/2) (by positivity), hx, eventually_ge_atTop 100] with r hs he hr
  intro m ha
  have hD := log_Dnew_le (fun _ => 9 * r) r m (by omega)
    (fun p => (Wsharp r m p : ℝ)) (fun _ => Nat.cast_nonneg _)
    (fun p hp => by exact_mod_cast trop_sharp hp (by omega)) (by
      intro c hc p hp hb hpc hcut
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc
      have hcls : p % 6 = 1 ∨ p % 6 = 5 := by
        rcases hc with rfl | rfl
        · exact Or.inl (cls_one hpc)
        · exact Or.inr (cls_five hpc)
      have hzero := Quarter.tail ha hr hcls hcut
      have hle := sharp_le r m p
      have hz : Wsharp r m p = 0 := by omega
      simp [hz])
  have hm : m ≤ r := by have := ha.2; omega
  have hE : extraG 3 Ecub 2 (badLog (p6Inst r m)) r m ≤ (ε/2) * (r : ℝ) ^ 2 := he m hm
  have hS := hs m ha
  have hmin : ∀ p, min ((Wsharp r m p : ℕ) : ℝ) (eExp r m p : ℝ) = (Wn r m p : ℝ) := fun p => by
    unfold Wn; rw [Nat.cast_min]
  simp only [hmin] at hD
  linarith

theorem hasContent_m3 (d : ℕ) :
    HasContent (commonMinorFam p6Frame Adm d) (LamNew : ℝ) := by
  refine ⟨fun i => Dnew i.1 i.2.1, fun i => Dnew_pos _ _, ?_, ?_⟩
  · intro i _ p q hq
    exact int_clear _ i.1 (natDegree_commonMinorPoly_le p6Frame i.1 i.2.1 i.2.2) _
      (Dnew_integral i.1 i.2.1 i.2.2) p q hq
  · intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.1 (log_content_m3 ε hε)
    exact ⟨N, fun i hi hr => hN i.1 hr i.2.1 hi.1⟩

end CatalanCore.Uniform.Bank.Chi3Content
