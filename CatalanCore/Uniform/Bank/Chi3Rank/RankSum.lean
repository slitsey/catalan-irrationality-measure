import CatalanCore.Uniform.Bank.Chi3Rank.RankWin
set_option Elab.async false

/-! # The class sums of `Wn2` and the content bound with `Λ' = Λ - 3/320` (lane H, H16) -/

open Finset Filter CatalanCore CatalanCore.Rect CatalanCore.Arith CatalanCore.Arith.Hybrid
  CatalanFrames.HybCommon CatalanFrames.P6 CatalanFrames.P6Hybrid CatalanFrames.P6Hybrid.Quarter
  CatalanFrames.P6Hybrid.Quarter.Periodic CatalanCore.Uniform.Bank.Chi3Content

set_option maxHeartbeats 3200000
set_option maxRecDepth 4000

namespace CatalanCore.Uniform.Bank.Chi3Rank

/-- New class-1 chain: B3c's pieces with the three rank pieces on `[5/8, 5/6]`. -/
noncomputable def lpRank1 : List Piece :=
  newFirst1 ++ ([P1a, P1b, P1c, P1d, P1e] ++ Quarter.lp1.tail.tail.tail)
noncomputable def lpRank5 : List Piece :=
  newFirst5 ++ ([P5a, P5b, P5c, P5d] ++ Quarter.lp5.tail.tail.tail)

theorem lpRank1_chain : Chain (1/4) lpRank1 := by
  unfold lpRank1
  rw [chain_append, newFirst1_end]
  refine ⟨newFirst1_chain, ?_⟩
  simp only [P1a, P1b, P1c, P1d, P1e, Quarter.lp1, List.tail_cons, Chain, mkPiece,
    List.cons_append, List.nil_append]
  norm_num

theorem lpRank5_chain : Chain (1/4) lpRank5 := by
  unfold lpRank5
  rw [chain_append, newFirst5_end]
  refine ⟨newFirst5_chain, ?_⟩
  simp only [P5a, P5b, P5c, P5d, Quarter.lp5, List.tail_cons, Chain, mkPiece,
    List.cons_append, List.nil_append]
  norm_num

theorem lpRank1_end : lastEnd (1/4) lpRank1 = 9 := by
  unfold lpRank1
  rw [lastEnd_append, newFirst1_end]
  simp only [P1a, P1b, P1c, P1d, P1e, Quarter.lp1, List.tail_cons, lastEnd, mkPiece,
    List.cons_append, List.nil_append]
  norm_num

theorem lpRank5_end : lastEnd (1/4) lpRank5 = 9 := by
  unfold lpRank5
  rw [lastEnd_append, newFirst5_end]
  simp only [P5a, P5b, P5c, P5d, Quarter.lp5, List.tail_cons, lastEnd, mkPiece,
    List.cons_append, List.nil_append]
  norm_num

theorem lpRank1_int : (5/2 : ℝ) * (1/4) + listInt lpRank1 = 1302793/288288 := by
  unfold lpRank1
  rw [listInt_append]
  simp only [newFirst1, P1a, P1b, P1c, P1d, P1e, Quarter.lp1, List.tail_cons, listInt, Piece.int,
    mkPiece, List.cons_append, List.nil_append]
  norm_num

theorem lpRank5_int : (5/2 : ℝ) * (1/4) + listInt lpRank5 = 1391273/376992 := by
  unfold lpRank5
  rw [listInt_append]
  simp only [newFirst5, P5a, P5b, P5c, P5d, Quarter.lp5, List.tail_cons, listInt, Piece.int,
    mkPiece, List.cons_append, List.nil_append]
  norm_num

theorem lpRank1_covers {r m : ℕ} (ha : AdmR r m) (hr : R0 ≤ r) :
    ∀ P ∈ lpRank1, Covers (1 : ZMod 6) (fun p => (Wn2 r m p : ℝ)) r P := by
  intro P hP
  have hm1 := ha.1.1
  have hm2 := ha.1.2
  have hr100 : 100 ≤ r := by unfold R0 at hr; omega
  have hle : ∀ p, (Wn2 r m p : ℝ) ≤ (Quarter.W r m p : ℝ) := fun p => by
    exact_mod_cast (Wn2_le_Wn r m p).trans (Chi3Content.Wn_le_W r m p)
  unfold lpRank1 at hP
  rcases List.mem_append.mp hP with hP | hP
  · exact covers_of_le (fun p => Nat.cast_le.2 (Wn2_le_Wn r m p))
      (newFirst1_covers hm1 hm2 hr100 P hP)
  · simp only [Quarter.lp1, List.tail_cons, List.mem_append, List.mem_cons, List.mem_nil_iff,
      or_false] at hP
    rcases hP with (rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact covers_sub (P := mkPiece 1 2 3 4 9 0 100 4) (by norm_num [P1a, mkPiece])
        (by norm_num [P1a, mkPiece]) rfl rfl rfl
        (covers_of_le hle (c1_2 hm1 hm2 hr100))
    · exact cov_P1b ha.2 hr
    · exact cov_P1c ha.2 hr
    · exact cov_P1d ha.2 hr
    · exact covers_sub (P := mkPiece 3 4 15 16 9 0 100 4) (by norm_num [P1e, mkPiece])
        (by norm_num [P1e, mkPiece]) rfl rfl rfl
        (covers_of_le hle (c1_3 hm1 hm2 hr100))
    exacts [covers_of_le hle (c1_4 hm1 hm2 hr100), covers_of_le hle (c1_5 hm1 hm2 hr100),
      covers_of_le hle (c1_6 hm1 hm2 hr100), covers_of_le hle (c1_7 hm1 hm2 hr100),
      covers_of_le hle (c1_8 hm1 hm2 hr100), covers_of_le hle (c1_9 hm1 hm2 hr100)]

theorem lpRank5_covers {r m : ℕ} (ha : AdmR r m) (hr : R0 ≤ r) :
    ∀ P ∈ lpRank5, Covers (5 : ZMod 6) (fun p => (Wn2 r m p : ℝ)) r P := by
  intro P hP
  have hm1 := ha.1.1
  have hm2 := ha.1.2
  have hr100 : 100 ≤ r := by unfold R0 at hr; omega
  have hle : ∀ p, (Wn2 r m p : ℝ) ≤ (Quarter.W r m p : ℝ) := fun p => by
    exact_mod_cast (Wn2_le_Wn r m p).trans (Chi3Content.Wn_le_W r m p)
  unfold lpRank5 at hP
  rcases List.mem_append.mp hP with hP | hP
  · exact covers_of_le (fun p => Nat.cast_le.2 (Wn2_le_Wn r m p))
      (newFirst5_covers hm1 hm2 hr100 P hP)
  · simp only [Quarter.lp5, List.tail_cons, List.mem_append, List.mem_cons, List.mem_nil_iff,
      or_false] at hP
    rcases hP with (rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl)
    · exact cov_P5a ha.2 hr
    · exact cov_P5b ha.2 hr
    · exact covers_sub (P := mkPiece 1 2 3 4 9 0 100 4) (by norm_num [P5c, mkPiece])
        (by norm_num [P5c, mkPiece]) rfl rfl rfl
        (covers_of_le hle (c5_2 hm1 hm2 hr100))
    · exact covers_of_le hle (c5_3 hm1 hm2 hr100)
    exacts [covers_of_le hle (c5_4 hm1 hm2 hr100), covers_of_le hle (c5_5 hm1 hm2 hr100),
      covers_of_le hle (c5_6 hm1 hm2 hr100), covers_of_le hle (c5_7 hm1 hm2 hr100),
      covers_of_le hle (c5_8 hm1 hm2 hr100)]

/-- One summation argument for the rank-refined weight `Wn2`. -/
theorem class_refined2 (c : ZMod 6) (hc : IsUnit c)
    (hgood : ∀ p : ℕ, (p : ZMod 6) = c → p % 6 = 1 ∨ p % 6 = 5)
    (l : List Piece) (I : ℝ) (hchain : Chain (1/4) l)
    (hend : lastEnd (1/4) l = 9)
    (hint : (5/2 : ℝ) * (1/4) + listInt l = I)
    (hcovers : ∀ {r m : ℕ}, AdmR r m → R0 ≤ r →
      ∀ P ∈ l, Covers c (fun p => (Wn2 r m p : ℝ)) r P)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ m, AdmR r m →
      clsSum 6 c (fun p => (Wn2 r m p : ℝ)) 0 (9 * r) ≤
        (r : ℝ) ^ 2 * ((I - (3163/768 - 339258406689121/82516315939200) + ε/68)/2 + ε/4) := by
  have hch : Chain (1/68) ((quarterD1Prefix 16) ++ l) := by
    rw [chain_append, quarterD1Prefix16_end]
    exact ⟨quarterD1Prefix16_chain, hchain⟩
  have hpref : ∀ᶠ r : ℕ in atTop, ∀ m, AdmR r m → ∀ p,
      p ≤ ⌊(1/68 : ℝ) * r⌋₊ → p.Prime → (p : ZMod 6) = c →
      (Wn2 r m p : ℝ) ≤ (5/2 : ℝ) * r + 2 := by
    apply Filter.Eventually.of_forall
    intro r m ha p _ _ _
    have hW : Quarter.W r m p ≤ 2 * r + 2 * m := by
      unfold Quarter.W Hb; split_ifs <;> omega
    have hle := ((Wn2_le_Wn r m p).trans (Chi3Content.Wn_le_W r m p)).trans hW
    have hleR : (Wn2 r m p : ℝ) ≤ (2 * r + 2 * m : ℕ) := by exact_mod_cast hle
    have hmR : (4 * m : ℝ) ≤ r + 3 := by exact_mod_cast ha.1.2
    push_cast at hleR
    nlinarith
  have hcov : ∀ᶠ r : ℕ in atTop, ∀ m, AdmR r m →
      ∀ P ∈ quarterD1Prefix 16 ++ l, Covers c (fun p => (Wn2 r m p : ℝ)) r P := by
    filter_upwards [eventually_ge_atTop R0] with r hr0
    intro m ha P hP
    have hr100 : 100 ≤ r := by unfold R0 at hr0; omega
    rcases List.mem_append.mp hP with hP | hP
    · exact quarterD1Prefix_covers ha.1.1 ha.1.2
        (fun p _ hpc => ((Wn2_le_sharp r m p).trans (sharp_exact r m p (hgood p hpc)))) 16 P hP
    · exact hcovers ha hr0 P hP
  have h := CatalanFrames.HybGen.class_sum_of_family hc AdmR (fun r m p => (Wn2 r m p : ℝ))
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

/-- The rank-refined constant `Λ' = Λ - 3/320`. -/
def LamRank : ℚ := 4733759984905769 / 1155228423148800

theorem hsum2 : ∀ ε > 0, ∀ᶠ r : ℕ in atTop, ∀ m, AdmR r m →
    ∑ c ∈ ({1, 5} : Finset (ZMod 6)), clsSum 6 c (fun p => (Wn2 r m p : ℝ)) 0 (9 * r) ≤
      ((LamRank : ℝ) + ε) * (r : ℝ) ^ 2 := by
  intro ε hε
  have h1 := class_refined2 1 (by decide) (fun p h => Or.inl (cls_one h)) lpRank1
    (1302793/288288) lpRank1_chain lpRank1_end lpRank1_int
    (fun ha hr => lpRank1_covers ha hr) hε
  have h5 := class_refined2 5 (by decide) (fun p h => Or.inr (cls_five h)) lpRank5
    (1391273/376992) lpRank5_chain lpRank5_end lpRank5_int
    (fun ha hr => lpRank5_covers ha hr) hε
  filter_upwards [h1, h5] with r hr1 hr5 m ha
  rw [Finset.sum_pair (by decide : (1 : ZMod 6) ≠ 5)]
  have ha1 := hr1 m ha
  have ha5 := hr5 m ha
  have hL : (LamRank : ℝ) = 4733759984905769 / 1155228423148800 := by
    unfold LamRank; push_cast; norm_num
  rw [hL]
  nlinarith [mul_nonneg hε.le (sq_nonneg (r : ℝ))]

theorem log_content_rank : ∀ ε > 0, ∀ᶠ r : ℕ in atTop, ∀ m, AdmR r m →
    Real.log (Dnew2 r m) ≤ ((LamRank : ℝ) + ε) * (r : ℝ) ^ 2 := by
  intro ε hε
  have hx := (p6_badInfo 0 0).extra_small (ε/2) (by positivity)
  filter_upwards [hsum2 (ε/2) (by positivity), hx, eventually_ge_atTop 100] with r hs he hr
  intro m ha
  have hD := log_Dnew2_le (fun _ => 9 * r) r m (by omega)
    (fun p => (Wsharp r m p : ℝ)) (fun _ => Nat.cast_nonneg _)
    (fun p hp => by exact_mod_cast trop_sharp hp (by omega)) (by
      intro c hc p hp hb hpc hcut
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc
      have hcls : p % 6 = 1 ∨ p % 6 = 5 := by
        rcases hc with rfl | rfl
        · exact Or.inl (cls_one hpc)
        · exact Or.inr (cls_five hpc)
      have hzero := Quarter.tail ha.1 hr hcls hcut
      have hle := sharp_le r m p
      have hz : Wsharp r m p = 0 := by omega
      simp [hz])
  have hm : m ≤ r := by have := ha.1.2; omega
  have hE : extraG 3 Ecub 2 (badLog (p6Inst r m)) r m ≤ (ε/2) * (r : ℝ) ^ 2 := he m hm
  have hS := hs m ha
  have hmin : ∀ p, min ((Wsharp r m p : ℕ) : ℝ) (eExp2 r m p : ℝ) = (Wn2 r m p : ℝ) := fun p => by
    unfold Wn2; rw [Nat.cast_min]
  simp only [hmin] at hD
  linarith

end CatalanCore.Uniform.Bank.Chi3Rank
