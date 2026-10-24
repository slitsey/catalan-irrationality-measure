module
public import CatalanFrames.P6Hybrid.QuarterPieces
public import CatalanCore.Rect.MinorContent
public import CatalanFrames.HybGen.FamilySum
@[expose] public section
open Finset Filter CatalanCore CatalanCore.Rect CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanFrames.HybCommon CatalanFrames.P6
namespace CatalanFrames.P6Hybrid.Quarter
set_option maxHeartbeats 1600000

/-- The integer rounding band for the quarter border. -/
def Adm (r m : ℕ) : Prop := r ≤ 4*m ∧ 4*m ≤ r+3

theorem adm_exists (r : ℕ) : ∃ m, Adm r m := by
  refine ⟨(r+3)/4, ?_⟩
  unfold Adm; omega

lemma floor_quarter (r : ℕ) : ⌊(1/4 : ℝ)*r⌋₊ = r/4 := by
  simpa using floor_frac 1 4 r

lemma prefix_real {r m p : ℕ} {ε : ℝ} (ha : Adm r m) (he : 2 ≤ ε*r) :
    (W r m p : ℝ) ≤ (5/2+ε)*r := by
  have hW : W r m p ≤ 2*r+2*m := by
    unfold W Hb; split_ifs <;> omega
  have h1 : (W r m p : ℝ) ≤ ((2*r+2*m : ℕ) : ℝ) := by exact_mod_cast hW
  have h2 : (4*m : ℝ) ≤ r+3 := by exact_mod_cast ha.2
  push_cast at h1
  nlinarith

noncomputable def lp1 : List Piece :=
  [mkPiece 1 4 1 2 11 (-4) 100 4, mkPiece 1 2 3 4 9 (0) 100 4, mkPiece 3 4 15 16 9 (0) 100 4, mkPiece 15 16 9 8 21 (-8) 100 6, mkPiece 9 8 3 2 15 (-8) 100 3, mkPiece 3 2 2 1 6 (-2) 100 3, mkPiece 2 1 3 1 6 (-1) 100 6, mkPiece 3 1 9 2 9 (-2) 100 6, mkPiece 9 2 9 1 0 (0) 100 1]

lemma lp1_chain : Chain (1/4) lp1 := by
  simp only [lp1, Chain, mkPiece]; norm_num
lemma lp1_end : lastEnd (1/4) lp1 = ((9 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) := by
  simp [lp1, lastEnd, mkPiece]
lemma lp1_int : (5/2 : ℝ)*(1/4)+listInt lp1 = 581/128 := by
  simp only [lp1, listInt, Piece.int, mkPiece]; norm_num

theorem class1_total {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ m, Adm r m →
      clsSum 6 1 (fun p => (W r m p : ℝ)) 0 (9*r) ≤
        (r : ℝ)^2 * ((581/128+ε/4)/2+ε/4) := by
  have hpref : ∀ᶠ r : ℕ in atTop, ∀ m, Adm r m → ∀ p,
      p ≤ ⌊(1/4 : ℝ)*r⌋₊ → p.Prime → (p : ZMod 6)=1 →
      (W r m p : ℝ) ≤ (5/2 : ℝ)*r+2 := by
    apply Filter.Eventually.of_forall
    intro r m ha p _ _ _
    have hW : W r m p ≤ 2*r+2*m := by unfold W Hb; split_ifs <;> omega
    have hR : (W r m p : ℝ) ≤ (2*r+2*m : ℕ) := by exact_mod_cast hW
    have hmR : (4*m : ℝ) ≤ r+3 := by exact_mod_cast ha.2
    push_cast at hR
    nlinarith
  have hcov : ∀ᶠ r : ℕ in atTop, ∀ m, Adm r m →
      ∀ P ∈ lp1, Covers (1 : ZMod 6) (fun p => (W r m p : ℝ)) r P := by
    filter_upwards [eventually_ge_atTop 100] with r hr100
    intro m ha P hP
    simp only [lp1, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [c1_1 ha.1 ha.2 hr100, c1_2 ha.1 ha.2 hr100, c1_3 ha.1 ha.2 hr100, c1_4 ha.1 ha.2 hr100, c1_5 ha.1 ha.2 hr100, c1_6 ha.1 ha.2 hr100, c1_7 ha.1 ha.2 hr100, c1_8 ha.1 ha.2 hr100, c1_9 ha.1 ha.2 hr100]
  have h := HybGen.class_sum_of_family (c := (1 : ZMod 6)) (by decide) Adm
    (fun r m p => (W r m p : ℝ)) (5/2) (1/4) 2 (by norm_num) (by norm_num)
    lp1 lp1_chain hpref hcov (ε := ε/4) (by positivity)
  filter_upwards [h] with r hr
  intro m ha
  have hh := hr m ha
  rw [lp1_end, floor_frac] at hh
  have ht : (Nat.totient 6 : ℝ)=2 := by rw [show Nat.totient 6 = 2 by decide]; norm_num
  rw [ht, lp1_int] at hh
  simp only [Nat.div_one] at hh
  nlinarith [mul_nonneg hε.le (sq_nonneg (r : ℝ))]

noncomputable def lp5 : List Piece :=
  [mkPiece 1 4 1 2 11 (-4) 100 4, mkPiece 1 2 3 4 9 (0) 100 4, mkPiece 3 4 5 6 9 (0) 100 4, mkPiece 5 6 1 1 7 (-3) 100 2, mkPiece 1 1 3 2 4 (-2) 100 1, mkPiece 3 2 2 1 5 (-2) 100 2, mkPiece 2 1 3 1 3 (-1) 100 2, mkPiece 3 1 9 1 0 (0) 100 1]

lemma lp5_chain : Chain (1/4) lp5 := by
  simp only [lp5, Chain, mkPiece]; norm_num
lemma lp5_end : lastEnd (1/4) lp5 = ((9 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) := by
  simp [lp5, lastEnd, mkPiece]
lemma lp5_int : (5/2 : ℝ)*(1/4)+listInt lp5 = 355/96 := by
  simp only [lp5, listInt, Piece.int, mkPiece]; norm_num

theorem class5_total {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ m, Adm r m →
      clsSum 6 5 (fun p => (W r m p : ℝ)) 0 (9*r) ≤
        (r : ℝ)^2 * ((355/96+ε/4)/2+ε/4) := by
  have hpref : ∀ᶠ r : ℕ in atTop, ∀ m, Adm r m → ∀ p,
      p ≤ ⌊(1/4 : ℝ)*r⌋₊ → p.Prime → (p : ZMod 6)=5 →
      (W r m p : ℝ) ≤ (5/2 : ℝ)*r+2 := by
    apply Filter.Eventually.of_forall
    intro r m ha p _ _ _
    have hW : W r m p ≤ 2*r+2*m := by unfold W Hb; split_ifs <;> omega
    have hR : (W r m p : ℝ) ≤ (2*r+2*m : ℕ) := by exact_mod_cast hW
    have hmR : (4*m : ℝ) ≤ r+3 := by exact_mod_cast ha.2
    push_cast at hR
    nlinarith
  have hcov : ∀ᶠ r : ℕ in atTop, ∀ m, Adm r m →
      ∀ P ∈ lp5, Covers (5 : ZMod 6) (fun p => (W r m p : ℝ)) r P := by
    filter_upwards [eventually_ge_atTop 100] with r hr100
    intro m ha P hP
    simp only [lp5, List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [c5_1 ha.1 ha.2 hr100, c5_2 ha.1 ha.2 hr100, c5_3 ha.1 ha.2 hr100, c5_4 ha.1 ha.2 hr100, c5_5 ha.1 ha.2 hr100, c5_6 ha.1 ha.2 hr100, c5_7 ha.1 ha.2 hr100, c5_8 ha.1 ha.2 hr100]
  have h := HybGen.class_sum_of_family (c := (5 : ZMod 6)) (by decide) Adm
    (fun r m p => (W r m p : ℝ)) (5/2) (1/4) 2 (by norm_num) (by norm_num)
    lp5 lp5_chain hpref hcov (ε := ε/4) (by positivity)
  filter_upwards [h] with r hr
  intro m ha
  have hh := hr m ha
  rw [lp5_end, floor_frac] at hh
  have ht : (Nat.totient 6 : ℝ)=2 := by rw [show Nat.totient 6 = 2 by decide]; norm_num
  rw [ht, lp5_int] at hh
  simp only [Nat.div_one] at hh
  nlinarith [mul_nonneg hε.le (sq_nonneg (r : ℝ))]

theorem hsum : ∀ ε > 0, ∀ᶠ r : ℕ in atTop, ∀ m, Adm r m →
    ∑ c ∈ ({1,5} : Finset (ZMod 6)), clsSum 6 c (fun p => (W r m p : ℝ)) 0 (9*r) ≤
      (3163/768+ε)*(r : ℝ)^2 := by
  intro ε hε
  filter_upwards [class1_total hε, class5_total hε] with r h1 h5 m ha
  rw [Finset.sum_pair (by decide : (1 : ZMod 6) ≠ 5)]
  have ha1 := h1 m ha
  have ha5 := h5 m ha
  have : 0 ≤ (r : ℝ)^2 := sq_nonneg _
  nlinarith

lemma tail {r m p : ℕ} (ha : Adm r m) (hr : 100 ≤ r) (hc : p%6=1 ∨ p%6=5)
    (hp : 9*r < p) : W r m p = 0 := by
  obtain ⟨hm1,hm2⟩ := ha
  have hk := kq6_cases p
  unfold W Sv Hb
  split_ifs <;> omega

/-- Uniform quarter-border denominator bound, retaining all higher prime-power and bad-prime costs. -/
theorem log_content : ∀ ε > 0, ∀ᶠ r : ℕ in atTop, ∀ m, Adm r m →
    Real.log (Dhyb (p6Inst r m) r m) ≤ (3163/768+ε)*(r : ℝ)^2 := by
  intro ε hε
  have hx := (p6_badInfo 0 0).extra_small (ε/2) (by positivity)
  filter_upwards [hsum (ε/2) (by positivity), hx, eventually_ge_atTop 100] with r hs he hr
  intro m ha
  have hD := p6_log_Dhyb_le (fun _ => 9*r) r m (by omega)
    (fun p => (W r m p : ℝ)) (fun _ => Nat.cast_nonneg _)
    (fun p hp => by exact_mod_cast trop_le hp (by omega)) (by
      intro c hc p hp hb hpc hcut
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc
      have hcls : p%6=1 ∨ p%6=5 := by
        rcases hc with rfl | rfl
        · exact Or.inl (cls_one hpc)
        · exact Or.inr (cls_five hpc)
      simp [tail ha hr hcls hcut])
  have hm : m ≤ r := by have := ha.2; omega
  have hE : extraG 3 Ecub 2 (badLog (p6Inst r m)) r m ≤ (ε/2)*(r : ℝ)^2 := he m hm
  have hS := hs m ha
  linarith

theorem hasContent (d : ℕ) : HasContent (commonMinorFam p6Frame Adm d) (3163/768) :=
  hasContent_commonMinorFam p6Inst Adm d (3163/768) log_content
end CatalanFrames.P6Hybrid.Quarter
#print axioms CatalanFrames.P6Hybrid.Quarter.log_content
#print axioms CatalanFrames.P6Hybrid.Quarter.hasContent
