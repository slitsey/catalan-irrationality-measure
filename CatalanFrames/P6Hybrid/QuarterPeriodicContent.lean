module
public import CatalanFrames.P6Hybrid.QuarterContent
public import CatalanCore.Arith.Hybrid.D1QuarterPrefix
@[expose] public section
open Finset Filter CatalanCore CatalanCore.Rect CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanFrames.HybCommon CatalanFrames.P6
namespace CatalanFrames.P6Hybrid.Quarter.Periodic

/-- The same tropical weight, retaining the exact periodic D1 prefix. -/
def Wsharp (r m p : ℕ) : ℕ :=
  if p % 6 = 1 ∨ p % 6 = 5 then
    min (Quarter.W r m p) (2*r+2*m-min (m%p) (p-m%p))
  else Quarter.W r m p

lemma sharp_le (r m p : ℕ) : Wsharp r m p ≤ Quarter.W r m p := by
  unfold Wsharp; split_ifs <;> omega

lemma sharp_exact (r m p : ℕ) (hc : p%6=1 ∨ p%6=5) :
    Wsharp r m p ≤ 2*r+2*m-min (m%p) (p-m%p) := by
  simp only [Wsharp, if_pos hc]
  exact Nat.min_le_right _ _

lemma trop_sharp {r m p : ℕ} (hp : p.Prime) (hr : 16 ≤ r) :
    tropVal (HW (p6Inst r m).lev p r m) ≤ Wsharp r m p := by
  have hW := Quarter.trop_le (m := m) hp hr
  unfold Wsharp
  split_ifs with hc
  · have ho : p%2=1 := by omega
    have h := val_D1x (lev := (p6Inst r m).lev) p r ho hp.pos m
    omega
  · exact hW

private lemma covers_sharp {c : ZMod 6} {r m : ℕ} {P : Piece}
    (h : Covers c (fun p => (Quarter.W r m p : ℝ)) r P) :
    Covers c (fun p => (Wsharp r m p : ℝ)) r P := by
  intro p hlo hhi hp hc
  have hle : (Wsharp r m p : ℝ) ≤ (Quarter.W r m p : ℝ) := by exact_mod_cast sharp_le r m p
  exact hle.trans (h p hlo hhi hp hc)

/-- One summation argument serves both residue classes and every old tail table. -/
private theorem class_refined (c : ZMod 6) (hc : IsUnit c)
    (hgood : ∀ p : ℕ, (p : ZMod 6)=c → p%6=1 ∨ p%6=5)
    (l : List Piece) (I : ℝ) (hchain : Chain (1/4) l)
    (hend : lastEnd (1/4) l = 9)
    (hint : (5/2 : ℝ)*(1/4)+listInt l=I)
    (hcovers : ∀ {r m : ℕ}, Adm r m → 100 ≤ r →
      ∀ P ∈ l, Covers c (fun p => (Quarter.W r m p : ℝ)) r P)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ m, Adm r m →
      clsSum 6 c (fun p => (Wsharp r m p : ℝ)) 0 (9*r) ≤
        (r : ℝ)^2 * ((I-(3163/768-339258406689121/82516315939200)+ε/68)/2+ε/4) := by
  have hch : Chain (1/68) ((quarterD1Prefix 16) ++ l) := by
    rw [chain_append, quarterD1Prefix16_end]
    exact ⟨quarterD1Prefix16_chain, hchain⟩
  have h := class_total (M := 6) hc (α0 := 5/2+ε) (t1 := 1/68)
    (by positivity) (by norm_num) ((quarterD1Prefix 16) ++ l) hch
    (ε := ε/4) (by positivity)
  filter_upwards [h, eventually_ge_atTop 100, eventually_ge_atTop ⌈2/ε⌉₊] with r hr hr100 hre
  intro m ha
  have he : 2 ≤ ε*(r : ℝ) := by
    have h1 := Nat.le_ceil (2/ε)
    have h2 : 2/ε ≤ (r : ℝ) := h1.trans (by exact_mod_cast hre)
    rwa [div_le_iff₀ hε, mul_comm] at h2
  have hh := hr (fun p => (Wsharp r m p : ℝ)) (by
    intro p _ _ _
    have hle : (Wsharp r m p : ℝ) ≤ (Quarter.W r m p : ℝ) := by exact_mod_cast sharp_le r m p
    exact hle.trans (prefix_real ha he)) (by
    intro P hP
    rcases List.mem_append.mp hP with hP | hP
    · exact quarterD1Prefix_covers ha.1 ha.2
        (fun p _ hpc => sharp_exact r m p (hgood p hpc)) 16 P hP
    · exact covers_sharp (hcovers ha hr100 P hP))
  have heq : lastEnd (1/68) ((quarterD1Prefix 16) ++ l) = 9 := by
    rw [lastEnd_append, quarterD1Prefix16_end, hend]
  have hfloor : ⌊(9 : ℝ)*(r : ℝ)⌋₊=9*r := by
    rw [show (9 : ℝ)*(r : ℝ)=((9*r : ℕ) : ℝ) by push_cast; ring, Nat.floor_natCast]
  rw [heq, hfloor] at hh
  have htot : (Nat.totient 6 : ℝ) = 2 := by
    rw [show Nat.totient 6 = 2 by decide]; norm_num
  have hi : (5/2+ε)*(1/68)+listInt ((quarterD1Prefix 16) ++ l)=I-(3163/768-339258406689121/82516315939200)+ε/68 := by
    rw [listInt_append]
    linarith [quarterD1Prefix16_integral]
  rw [htot, hi] at hh
  simpa using hh

private lemma covers_one {r m : ℕ} (ha : Adm r m) (hr : 100 ≤ r) :
    ∀ P ∈ lp1, Covers (1 : ZMod 6) (fun p => (Quarter.W r m p : ℝ)) r P := by
  intro P hP
  simp only [lp1, List.mem_cons, List.mem_nil_iff, or_false] at hP
  rcases hP with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [c1_1 ha.1 ha.2 hr, c1_2 ha.1 ha.2 hr, c1_3 ha.1 ha.2 hr,
    c1_4 ha.1 ha.2 hr, c1_5 ha.1 ha.2 hr, c1_6 ha.1 ha.2 hr,
    c1_7 ha.1 ha.2 hr, c1_8 ha.1 ha.2 hr, c1_9 ha.1 ha.2 hr]

private lemma covers_five {r m : ℕ} (ha : Adm r m) (hr : 100 ≤ r) :
    ∀ P ∈ lp5, Covers (5 : ZMod 6) (fun p => (Quarter.W r m p : ℝ)) r P := by
  intro P hP
  simp only [lp5, List.mem_cons, List.mem_nil_iff, or_false] at hP
  rcases hP with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [c5_1 ha.1 ha.2 hr, c5_2 ha.1 ha.2 hr, c5_3 ha.1 ha.2 hr,
    c5_4 ha.1 ha.2 hr, c5_5 ha.1 ha.2 hr, c5_6 ha.1 ha.2 hr,
    c5_7 ha.1 ha.2 hr, c5_8 ha.1 ha.2 hr]

theorem hsum : ∀ ε > 0, ∀ᶠ r : ℕ in atTop, ∀ m, Adm r m →
    ∑ c ∈ ({1,5} : Finset (ZMod 6)), clsSum 6 c (fun p => (Wsharp r m p : ℝ)) 0 (9*r) ≤
      (339258406689121/82516315939200+ε)*(r : ℝ)^2 := by
  intro ε hε
  have h1 := class_refined 1 (by decide)
    (fun p h => Or.inl (cls_one h)) lp1 (581/128) lp1_chain
    (by simpa using lp1_end) lp1_int (fun ha hr => covers_one ha hr) hε
  have h5 := class_refined 5 (by decide)
    (fun p h => Or.inr (cls_five h)) lp5 (355/96) lp5_chain
    (by simpa using lp5_end) lp5_int (fun ha hr => covers_five ha hr) hε
  filter_upwards [h1, h5] with r hr1 hr5 m ha
  rw [Finset.sum_pair (by decide : (1 : ZMod 6) ≠ 5)]
  have ha1 := hr1 m ha
  have ha5 := hr5 m ha
  nlinarith [sq_nonneg (r : ℝ)]

/-- Improved estimate of the SAME full denominator, including all bad and higher-power costs. -/
theorem log_content : ∀ ε > 0, ∀ᶠ r : ℕ in atTop, ∀ m, Adm r m →
    Real.log (Dhyb (p6Inst r m) r m) ≤ (339258406689121/82516315939200+ε)*(r : ℝ)^2 := by
  intro ε hε
  have hx := (p6_badInfo 0 0).extra_small (ε/2) (by positivity)
  filter_upwards [hsum (ε/2) (by positivity), hx, eventually_ge_atTop 100] with r hs he hr
  intro m ha
  have hD := p6_log_Dhyb_le (fun _ => 9*r) r m (by omega)
    (fun p => (Wsharp r m p : ℝ)) (fun _ => Nat.cast_nonneg _)
    (fun p hp => by exact_mod_cast trop_sharp hp (by omega)) (by
      intro c hc p hp hb hpc hcut
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc
      have hcls : p%6=1 ∨ p%6=5 := by
        rcases hc with rfl | rfl
        · exact Or.inl (cls_one hpc)
        · exact Or.inr (cls_five hpc)
      have hzero := Quarter.tail ha hr hcls hcut
      have hle := sharp_le r m p
      have hz : Wsharp r m p=0 := by omega
      simp [hz])
  have hm : m ≤ r := by have := ha.2; omega
  have hE : extraG 3 Ecub 2 (badLog (p6Inst r m)) r m ≤ (ε/2)*(r : ℝ)^2 := he m hm
  have hS := hs m ha
  linarith

theorem hasContent (d : ℕ) : HasContent (commonMinorFam p6Frame Adm d) (339258406689121/82516315939200) :=
  hasContent_commonMinorFam p6Inst Adm d (339258406689121/82516315939200) log_content
end CatalanFrames.P6Hybrid.Quarter.Periodic
#print axioms CatalanFrames.P6Hybrid.Quarter.Periodic.hasContent
