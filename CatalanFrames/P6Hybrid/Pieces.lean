module

public import CatalanFrames.P6Hybrid.ZDual
public import CatalanFrames.P6Hybrid.Reduce
public import CatalanFrames.HybCommon.Pieces

@[expose] public section

/-!
# P6 hybrid content: piece tables and the class sums

The per-prime weight `Wn r m p` (`ZDual.lean`) is bounded by the linear pieces of HH's continuum law
(class 1: 8 chain pieces from `1/8` and the zero tail; class 5: 7 chain pieces and the zero tail), each
discharged by `omega` from the closed form of `Sv`.  `class_total` then gives
`Λ = (1949/512 + 1123/384)/2 = 10339/3072`.
-/

open Finset Filter CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanFrames.HybCommon
  CatalanFrames.P6

namespace CatalanFrames.P6Hybrid

lemma covers_mk (c : ZMod 6) (cn : ℕ) (hcn : ∀ p : ℕ, (p : ZMod 6) = c → p % 6 = cn)
    (wf : ℕ → ℕ) (r sn sd tn td : ℕ) (A B E D : ℤ) (hD : 0 < D)
    (h : ∀ p : ℕ, sn * r / sd < p → p ≤ tn * r / td → p % 6 = cn →
      D * (wf p : ℤ) ≤ A * r + B * p + E) :
    Covers c (fun p => (wf p : ℝ)) r (mkPiece sn sd tn td A B E D) := by
  intro p hs ht _ hpc
  rw [floor_mk_s] at hs
  rw [floor_mk_t] at ht
  exact real_of_int_bound D A B E hD (h p hs ht (hcn p hpc))

lemma cls_one {p : ℕ} (h : (p : ZMod 6) = 1) : p % 6 = 1 := by
  have := (ZMod.natCast_eq_natCast_iff' p 1 6).mp (by simpa using h)
  omega

lemma cls_five {p : ℕ} (h : (p : ZMod 6) = 5) : p % 6 = 5 := by
  have := (ZMod.natCast_eq_natCast_iff' p 5 6).mp (by simpa using h)
  omega

macro "wn_omega" : tactic =>
  `(tactic| (intro p hs ht hc; have hk := kq6_cases p; unfold Wn Sv Hb; split_ifs <;> omega))

section Class1

variable {r m : ℕ} (hm1 : r ≤ 8 * m) (hm2 : 8 * m ≤ r + 8) (hr : 100 ≤ r)
include hm1 hm2 hr

lemma c1_1 : Covers (1 : ZMod 6) (fun p => (Wn r m p : ℝ)) r (mkPiece 1 8 1 4 19 (-8) 40 8) :=
  covers_mk _ 1 (fun _ => cls_one) _ r _ _ _ _ _ _ _ _ (by norm_num) (by wn_omega)

lemma c1_2 : Covers (1 : ZMod 6) (fun p => (Wn r m p : ℝ)) r (mkPiece 1 4 27 32 17 (0) 40 8) :=
  covers_mk _ 1 (fun _ => cls_one) _ r _ _ _ _ _ _ _ _ (by norm_num) (by wn_omega)

lemma c1_3 : Covers (1 : ZMod 6) (fun p => (Wn r m p : ℝ)) r (mkPiece 27 32 15 16 39 (-16) 40 12) :=
  covers_mk _ 1 (fun _ => cls_one) _ r _ _ _ _ _ _ _ _ (by norm_num) (by wn_omega)

lemma c1_4 : Covers (1 : ZMod 6) (fun p => (Wn r m p : ℝ)) r (mkPiece 15 16 5 4 27 (-16) 40 6) :=
  covers_mk _ 1 (fun _ => cls_one) _ r _ _ _ _ _ _ _ _ (by norm_num) (by wn_omega)

lemma c1_5 : Covers (1 : ZMod 6) (fun p => (Wn r m p : ℝ)) r (mkPiece 5 4 2 1 6 (-2) 40 3) :=
  covers_mk _ 1 (fun _ => cls_one) _ r _ _ _ _ _ _ _ _ (by norm_num) (by wn_omega)

lemma c1_6 : Covers (1 : ZMod 6) (fun p => (Wn r m p : ℝ)) r (mkPiece 2 1 5 2 6 (-1) 40 6) :=
  covers_mk _ 1 (fun _ => cls_one) _ r _ _ _ _ _ _ _ _ (by norm_num) (by wn_omega)

lemma c1_7 : Covers (1 : ZMod 6) (fun p => (Wn r m p : ℝ)) r (mkPiece 5 2 3 1 27 (-8) 40 12) :=
  covers_mk _ 1 (fun _ => cls_one) _ r _ _ _ _ _ _ _ _ (by norm_num) (by wn_omega)

lemma c1_8 : Covers (1 : ZMod 6) (fun p => (Wn r m p : ℝ)) r (mkPiece 3 1 15 4 15 (-4) 40 12) :=
  covers_mk _ 1 (fun _ => cls_one) _ r _ _ _ _ _ _ _ _ (by norm_num) (by wn_omega)

lemma c1_9 : Covers (1 : ZMod 6) (fun p => (Wn r m p : ℝ)) r (mkPiece 15 4 4 1 0 (0) 40 1) :=
  covers_mk _ 1 (fun _ => cls_one) _ r _ _ _ _ _ _ _ _ (by norm_num) (by wn_omega)

end Class1

section Class5

variable {r m : ℕ} (hm1 : r ≤ 8 * m) (hm2 : 8 * m ≤ r + 8) (hr : 100 ≤ r)
include hm1 hm2 hr

lemma c5_1 : Covers (5 : ZMod 6) (fun p => (Wn r m p : ℝ)) r (mkPiece 1 8 1 4 19 (-8) 40 8) :=
  covers_mk _ 5 (fun _ => cls_five) _ r _ _ _ _ _ _ _ _ (by norm_num) (by wn_omega)

lemma c5_2 : Covers (5 : ZMod 6) (fun p => (Wn r m p : ℝ)) r (mkPiece 1 4 3 4 17 (0) 40 8) :=
  covers_mk _ 5 (fun _ => cls_five) _ r _ _ _ _ _ _ _ _ (by norm_num) (by wn_omega)

lemma c5_3 : Covers (5 : ZMod 6) (fun p => (Wn r m p : ℝ)) r (mkPiece 3 4 5 6 13 (-6) 40 4) :=
  covers_mk _ 5 (fun _ => cls_five) _ r _ _ _ _ _ _ _ _ (by norm_num) (by wn_omega)

lemma c5_4 : Covers (5 : ZMod 6) (fun p => (Wn r m p : ℝ)) r (mkPiece 5 6 1 1 9 (-6) 40 2) :=
  covers_mk _ 5 (fun _ => cls_five) _ r _ _ _ _ _ _ _ _ (by norm_num) (by wn_omega)

lemma c5_5 : Covers (5 : ZMod 6) (fun p => (Wn r m p : ℝ)) r (mkPiece 1 1 5 4 7 (-4) 40 2) :=
  covers_mk _ 5 (fun _ => cls_five) _ r _ _ _ _ _ _ _ _ (by norm_num) (by wn_omega)

lemma c5_6 : Covers (5 : ZMod 6) (fun p => (Wn r m p : ℝ)) r (mkPiece 5 4 2 1 9 (-4) 40 4) :=
  covers_mk _ 5 (fun _ => cls_five) _ r _ _ _ _ _ _ _ _ (by norm_num) (by wn_omega)

lemma c5_7 : Covers (5 : ZMod 6) (fun p => (Wn r m p : ℝ)) r (mkPiece 2 1 5 2 5 (-2) 40 4) :=
  covers_mk _ 5 (fun _ => cls_five) _ r _ _ _ _ _ _ _ _ (by norm_num) (by wn_omega)

lemma c5_8 : Covers (5 : ZMod 6) (fun p => (Wn r m p : ℝ)) r (mkPiece 5 2 3 1 0 (0) 40 1) :=
  covers_mk _ 5 (fun _ => cls_five) _ r _ _ _ _ _ _ _ _ (by norm_num) (by wn_omega)

end Class5

/-! ### The chains and the class totals -/

noncomputable def lp1 : List Piece :=
  [mkPiece 1 8 1 4 19 (-8) 40 8, mkPiece 1 4 27 32 17 0 40 8, mkPiece 27 32 15 16 39 (-16) 40 12,
   mkPiece 15 16 5 4 27 (-16) 40 6, mkPiece 5 4 2 1 6 (-2) 40 3, mkPiece 2 1 5 2 6 (-1) 40 6,
   mkPiece 5 2 3 1 27 (-8) 40 12, mkPiece 3 1 15 4 15 (-4) 40 12, mkPiece 15 4 4 1 0 0 40 1]

noncomputable def lp5 : List Piece :=
  [mkPiece 1 8 1 4 19 (-8) 40 8, mkPiece 1 4 3 4 17 0 40 8, mkPiece 3 4 5 6 13 (-6) 40 4,
   mkPiece 5 6 1 1 9 (-6) 40 2, mkPiece 1 1 5 4 7 (-4) 40 2, mkPiece 5 4 2 1 9 (-4) 40 4,
   mkPiece 2 1 5 2 5 (-2) 40 4, mkPiece 5 2 3 1 0 0 40 1]

lemma lp1_chain : Chain (1 / 8) lp1 := by
  simp only [lp1, Chain, mkPiece]; norm_num

lemma lp5_chain : Chain (1 / 8) lp5 := by
  simp only [lp5, Chain, mkPiece]; norm_num

lemma lp1_end : lastEnd (1 / 8) lp1 = ((4 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) := by
  simp [lp1, lastEnd, mkPiece]

lemma lp5_end : lastEnd (1 / 8) lp5 = ((3 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) := by
  simp [lp5, lastEnd, mkPiece]

lemma lp1_int : (9 / 4 : ℝ) * (1 / 8) + listInt lp1 = 1949 / 512 := by
  simp only [lp1, listInt, Piece.int, mkPiece]; norm_num

lemma lp5_int : (9 / 4 : ℝ) * (1 / 8) + listInt lp5 = 1123 / 384 := by
  simp only [lp5, listInt, Piece.int, mkPiece]; norm_num

lemma floor_eighth (r : ℕ) : ⌊(1 / 8 : ℝ) * r⌋₊ = r / 8 := by
  have := floor_frac 1 8 r
  simpa using this

lemma Wn_prefix {r m p : ℕ} (h : p ≤ r / 8) (hc : p % 6 = 1 ∨ p % 6 = 5) :
    Wn r m p ≤ 2 * r + 2 * m := by
  unfold Wn Hb; split_ifs <;> omega

lemma prefix_real {r m p : ℕ} {ε : ℝ} (h : p ≤ r / 8) (hc : p % 6 = 1 ∨ p % 6 = 5)
    (hm2 : 8 * m ≤ r + 8) (hrε : 2 ≤ ε * r) : (Wn r m p : ℝ) ≤ (9 / 4 + ε) * r := by
  have h1 : (Wn r m p : ℝ) ≤ ((2 * r + 2 * m : ℕ) : ℝ) := by exact_mod_cast Wn_prefix h hc
  have h2 : (8 * m : ℝ) ≤ r + 8 := by exact_mod_cast hm2
  push_cast at h1
  nlinarith

theorem class1_total_p6 (mf : ℕ → ℕ) (hadm : ∀ r, r ≤ 8 * mf r ∧ 8 * mf r ≤ r + 8) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, clsSum 6 1 (fun p => (Wn r (mf r) p : ℝ)) 0 (4 * r) ≤
      (r : ℝ) ^ 2 * ((1949 / 512 + ε / 8) / 2 + ε / 4) := by
  have h := class_total (M := 6) (c := 1) isUnit_one (α0 := 9 / 4 + ε) (t1 := 1 / 8)
    (by positivity) (by norm_num) lp1 lp1_chain (ε := ε / 4) (by positivity)
  filter_upwards [h, eventually_ge_atTop 100, eventually_ge_atTop ⌈2 / ε⌉₊] with r hr hr100 hrε
  have hε2 : 2 ≤ ε * r := by
    have := Nat.le_ceil (2 / ε)
    have h2 : (2 / ε) ≤ (r : ℝ) := this.trans (by exact_mod_cast hrε)
    rwa [div_le_iff₀ hε, mul_comm] at h2
  obtain ⟨hm1, hm2⟩ := hadm r
  have := hr (fun p => (Wn r (mf r) p : ℝ)) (by
    intro p hp _ hpc
    rw [floor_eighth] at hp
    exact prefix_real hp (Or.inl (cls_one hpc)) hm2 hε2) (by
    intro P hP
    simp only [lp1, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [c1_1 hm1 hm2 hr100, c1_2 hm1 hm2 hr100, c1_3 hm1 hm2 hr100, c1_4 hm1 hm2 hr100,
      c1_5 hm1 hm2 hr100, c1_6 hm1 hm2 hr100, c1_7 hm1 hm2 hr100, c1_8 hm1 hm2 hr100,
      c1_9 hm1 hm2 hr100])
  rw [lp1_end, floor_frac] at this
  have e : (Nat.totient 6 : ℝ) = 2 := by rw [show Nat.totient 6 = 2 by decide]; norm_num
  have e2 : (9 / 4 + ε) * (1 / 8) + listInt lp1 = 1949 / 512 + ε / 8 := by
    have := lp1_int; linarith
  rw [e, e2] at this
  simpa using this

theorem class5_total_p6 (mf : ℕ → ℕ) (hadm : ∀ r, r ≤ 8 * mf r ∧ 8 * mf r ≤ r + 8) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, clsSum 6 5 (fun p => (Wn r (mf r) p : ℝ)) 0 (3 * r) ≤
      (r : ℝ) ^ 2 * ((1123 / 384 + ε / 8) / 2 + ε / 4) := by
  have h := class_total (M := 6) (c := 5) (by decide) (α0 := 9 / 4 + ε) (t1 := 1 / 8)
    (by positivity) (by norm_num) lp5 lp5_chain (ε := ε / 4) (by positivity)
  filter_upwards [h, eventually_ge_atTop 100, eventually_ge_atTop ⌈2 / ε⌉₊] with r hr hr100 hrε
  have hε2 : 2 ≤ ε * r := by
    have := Nat.le_ceil (2 / ε)
    have h2 : (2 / ε) ≤ (r : ℝ) := this.trans (by exact_mod_cast hrε)
    rwa [div_le_iff₀ hε, mul_comm] at h2
  obtain ⟨hm1, hm2⟩ := hadm r
  have := hr (fun p => (Wn r (mf r) p : ℝ)) (by
    intro p hp _ hpc
    rw [floor_eighth] at hp
    exact prefix_real hp (Or.inr (cls_five hpc)) hm2 hε2) (by
    intro P hP
    simp only [lp5, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [c5_1 hm1 hm2 hr100, c5_2 hm1 hm2 hr100, c5_3 hm1 hm2 hr100, c5_4 hm1 hm2 hr100,
      c5_5 hm1 hm2 hr100, c5_6 hm1 hm2 hr100, c5_7 hm1 hm2 hr100, c5_8 hm1 hm2 hr100])
  rw [lp5_end, floor_frac] at this
  have e : (Nat.totient 6 : ℝ) = 2 := by rw [show Nat.totient 6 = 2 by decide]; norm_num
  have e2 : (9 / 4 + ε) * (1 / 8) + listInt lp5 = 1123 / 384 + ε / 8 := by
    have := lp5_int; linarith
  rw [e, e2] at this
  simpa using this


/-! ### The final theorem -/

/-- the class cutoffs -/
def Rp6 (r : ℕ) (c : ZMod 6) : ℕ := if c = 1 then 4 * r else 3 * r

lemma Wn_tail1 {r m p : ℕ} (hp : p % 6 = 1) (h : 4 * r < p) (h8 : r ≤ 8 * m) (h8' : 8 * m ≤ r + 8)
    (hr : 100 ≤ r) : Wn r m p = 0 := by
  have hk := kq6_cases p
  unfold Wn Sv; split_ifs <;> omega

lemma Wn_tail5 {r m p : ℕ} (hp : p % 6 = 5) (h : 3 * r < p) (h8 : r ≤ 8 * m) (h8' : 8 * m ≤ r + 8)
    (hr : 100 ≤ r) : Wn r m p = 0 := by
  have hk := kq6_cases p
  unfold Wn Sv; split_ifs <;> omega

/-- **The piece summation**: `∑_{c ∈ {1,5}} clsSum ≤ (10339/3072 + ε) r²`. -/
theorem p6_hsum (mf : ℕ → ℕ) (hadm : ∀ r, r ≤ 8 * mf r ∧ 8 * mf r ≤ r + 8) :
    ∀ ε > 0, ∀ᶠ r : ℕ in atTop,
      ∑ c ∈ ({1, 5} : Finset (ZMod 6)), clsSum 6 c (fun p => (Wn r (mf r) p : ℝ)) 0 (Rp6 r c) ≤
        (10339 / 3072 + ε) * (r : ℝ) ^ 2 := by
  intro ε hε
  filter_upwards [class1_total_p6 mf hadm (ε := ε) hε, class5_total_p6 mf hadm (ε := ε) hε]
    with r h1 h5
  rw [Finset.sum_pair (by decide : (1 : ZMod 6) ≠ 5)]
  simp only [Rp6, if_true, show ¬ ((5 : ZMod 6) = 1) by decide, if_false]
  have hr2 : 0 ≤ (r : ℝ) ^ 2 := by positivity
  nlinarith

/-- **P6 content statement, member 1, `Λ = 10339/3072`**, for any admissible `m` (`r ≤ 8m ≤ r + 8`). -/
theorem p6_content (mf : ℕ → ℕ) (hadm : ∀ r, r ≤ 8 * mf r ∧ 8 * mf r ≤ r + 8) : P6ContentStmt mf := by
  refine p6_content_of_pieces mf ?_ Rp6 (fun r p => (Wn r (mf r) p : ℝ)) (fun r p => Nat.cast_nonneg _)
    ?_ ?_ (p6_hsum mf hadm)
  · filter_upwards [eventually_ge_atTop 2] with r hr
    have := hadm r; omega
  · filter_upwards [eventually_ge_atTop 100] with r hr p hp
    have := hadm r
    exact_mod_cast p6_trop_le_Wn hp (by omega) this.1 this.2
  · filter_upwards [eventually_ge_atTop 100] with r hr c hc p hp hp23 hpc hRp
    have := hadm r
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl
    · have h1 := cls_one hpc
      simp only [Rp6, if_true] at hRp
      simp [Wn_tail1 h1 hRp this.1 this.2 hr]
    · have h5 := cls_five hpc
      simp only [Rp6, show ¬ ((5 : ZMod 6) = 1) by decide, if_false] at hRp
      simp [Wn_tail5 h5 hRp this.1 this.2 hr]

end CatalanFrames.P6Hybrid

#print axioms CatalanFrames.P6Hybrid.p6_trop_le_Wn
#print axioms CatalanFrames.P6Hybrid.p6_hsum
#print axioms CatalanFrames.P6Hybrid.p6_content
