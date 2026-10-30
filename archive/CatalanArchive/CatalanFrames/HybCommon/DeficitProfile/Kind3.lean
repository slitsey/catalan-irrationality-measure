module
public import CatalanFrames.HybCommon.DeficitProfile.LongCellRow
@[expose] public section
open Finset CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid
namespace CatalanFrames.HybCommon
open ChainClasses

/-! # Kind-3 (two-level) rows: arithmetic of the short arc

For a long cell between poles `A4, B4 = A4 + 3` the short arc `S` of the root `h` of `4h = o` is the
residue set of the short cells; the number `B` of short residues not covered by the zone is
`|S|` minus the zone integers lying in short cells (`zoneSb_add_le`).  `kind3_short_cover` bounds it
by the integer expression of `profileKind3Deficit`. -/

section K3
variable {p : ℕ} [Fact p.Prime]

/-- The root `h` of `4h = o` (as a natural number below `p`), by pole class. -/
def kind3H (o p c : ℕ) : ℕ := if c=1 then (p+o)/4 else (3*p+o)/4

lemma natCast_val_between {s x : ℕ} (h1 : s*p ≤ x) (h2 : x < (s+1)*p) :
    ((x : ℕ) : ZMod p).val = x - s*p := by
  have hd : x / p = s := Nat.div_eq_of_lt_le h1 h2
  rw [ZMod.val_natCast, Nat.mod_def, hd, Nat.mul_comm]

lemma card_shortArc_eq (h : ℕ) (hh : h ≤ p) :
    (shortArc p h).card = if 2*h<p then h else p-h := by
  classical
  have himg : (shortArc p h).image ZMod.val = if 2*h<p then Finset.range h else Finset.Ico h p := by
    ext k
    simp only [Finset.mem_image, mem_shortArc_iff]
    by_cases h2 : 2*h<p
    · simp only [h2, if_true, Finset.mem_range]
      constructor
      · rintro ⟨c, hc, rfl⟩; exact hc
      · intro hk
        exact ⟨(k : ZMod p), by rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]; exact hk,
          by rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]⟩
    · simp only [h2, if_false, Finset.mem_Ico]
      constructor
      · rintro ⟨c, hc, rfl⟩; exact ⟨hc, ZMod.val_lt c⟩
      · intro hk
        exact ⟨(k : ZMod p), by rw [ZMod.val_natCast, Nat.mod_eq_of_lt hk.2]; exact hk.1,
          by rw [ZMod.val_natCast, Nat.mod_eq_of_lt hk.2]⟩
  rw [← Finset.card_image_of_injective _ (ZMod.val_injective p), himg]
  by_cases h2 : 2*h<p
  · simp [h2]
  · simp [h2]

lemma zoneSb_add_le {r m h : ℕ} (hm : 2*m < p) (U : Finset ℕ)
    (hU : ∀ k ∈ U, r ≤ k ∧ k < r+2*m ∧ ((k:ℕ):ZMod p) ∈ shortArc p h) :
    (zoneSb p r m h).card + U.card ≤ (shortArc p h).card := by
  classical
  have hinj : Set.InjOn (fun k:ℕ => ((k:ℕ):ZMod p)) U := by
    intro a ha b hb hab
    have ha' := hU a ha
    have hb' := hU b hb
    simp only at hab
    have hd : (p:ℤ) ∣ (a:ℤ) - b := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hab]; ring
    have := Int.eq_zero_of_abs_lt_dvd hd (by rw [abs_lt]; constructor <;> omega)
    omega
  have hdisj : Disjoint (zoneSb p r m h) (U.image fun k:ℕ => ((k:ℕ):ZMod p)) := by
    rw [Finset.disjoint_left]
    intro c hc hc2
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hc2
    have := hU k hk
    simp only [zoneSb, Finset.mem_filter] at hc
    exact hc.2 ⟨k, this.1, this.2.1, rfl⟩
  have hsub : zoneSb p r m h ∪ U.image (fun k:ℕ => ((k:ℕ):ZMod p)) ⊆ shortArc p h := by
    intro c hc
    rcases Finset.mem_union.1 hc with hc | hc
    · exact (Finset.mem_filter.1 hc).1
    · obtain ⟨k,hk,rfl⟩ := Finset.mem_image.1 hc
      exact (hU k hk).2.2
  have := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn hinj] at this
  exact this

/-- Residues of the short and long cells of a period (class 1: short = `[sp, sp+h)`;
class 3: short = `[sp+h, (s+1)p)`). -/
lemma kind3_arc {o c s x : ℕ} (hp13 : 13 ≤ p) (ho : o=1 ∨ o=3) (hc : c=1 ∨ c=3) :
    (profileShortLo o p c s ≤ x → x < profileShortHi o p c s →
      ((x:ℕ):ZMod p) ∈ shortArc p (kind3H o p c)) ∧
    (c=1 → s*p + kind3H o p c ≤ x → x < (s+1)*p → ((x:ℕ):ZMod p) ∉ shortArc p (kind3H o p c)) ∧
    (c=3 → s*p ≤ x → x < s*p + kind3H o p c → ((x:ℕ):ZMod p) ∉ shortArc p (kind3H o p c)) := by
  have ho3 : o ≤ 3 := by omega
  rcases hc with rfl | rfl
  · refine ⟨?_, ?_, ?_⟩
    · intro h1 h2
      simp only [profileShortLo, profileShortHi, if_true] at h1 h2
      rw [mem_shortArc_iff]
      simp only [kind3H, if_true]
      rw [if_pos (by omega), natCast_val_between (s:=s) h1 (by rw [add_mul, one_mul]; omega)]
      omega
    · intro _ h1 h2
      simp only [kind3H, if_true] at h1
      rw [mem_shortArc_iff]
      simp only [kind3H, if_true]
      rw [if_pos (by omega), natCast_val_between (s:=s) (by omega) h2]
      omega
    · intro h; omega
  · refine ⟨?_, ?_, ?_⟩
    · intro h1 h2
      simp only [profileShortLo, profileShortHi, if_neg (by omega : ¬ (3:ℕ)=1)] at h1 h2
      rw [mem_shortArc_iff]
      simp only [kind3H, if_neg (by omega : ¬ (3:ℕ)=1)]
      rw [if_neg (by omega), natCast_val_between (s:=s) (by omega) h2]
      omega
    · intro h; omega
    · intro _ h1 h2
      simp only [kind3H, if_neg (by omega : ¬ (3:ℕ)=1)] at h2
      rw [mem_shortArc_iff]
      simp only [kind3H, if_neg (by omega : ¬ (3:ℕ)=1)]
      rw [if_neg (by omega), natCast_val_between (s:=s) h1 (by rw [add_mul, one_mul]; omega)]
      omega


lemma kind3_short_cover {o r c s : ℕ} (hp13 : 13 ≤ p) (ho : o=1 ∨ o=3) (hc : c=1 ∨ c=3)
    (hpc : p%4 = if c=1 then 4-o else o) (hm : 2*(r/8) < p) :
    (zoneSb p r (r/8) (kind3H o p c)).card + profileShortCell o r p c s +
      profileShortCell o r p c (s+1) ≤ profileShortSize o p c := by
  classical
  have ho3 : o ≤ 3 := by omega
  have hsz : (shortArc p (kind3H o p c)).card = profileShortSize o p c := by
    rw [card_shortArc_eq _ (by unfold kind3H; split_ifs <;> omega)]
    rcases hc with rfl | rfl
    · simp only [kind3H, profileShortSize, if_true]
      rw [if_pos (by omega)]
    · simp only [kind3H, profileShortSize, if_neg (by omega : ¬ (3:ℕ)=1)]
      rw [if_neg (by omega)]
      simp only [if_neg (by omega : ¬ (3:ℕ)=1)] at hpc
      omega
  set I : ℕ → Finset ℕ := fun t => Finset.Ico (max r (profileShortLo o p c t))
    (min (r+2*(r/8)) (profileShortHi o p c t)) with hI
  have hdisj : Disjoint (I s) (I (s+1)) := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    simp only [hI, Finset.mem_Ico, max_le_iff, lt_min_iff] at hk1 hk2
    have e : (s+1)*p = s*p+p := by rw [add_mul, one_mul]
    rcases hc with rfl | rfl
    · simp only [profileShortLo, profileShortHi, if_true] at hk1 hk2
      omega
    · simp only [profileShortLo, profileShortHi, if_neg (by omega : ¬ (3:ℕ)=1)] at hk1 hk2
      omega
  have hU : ∀ k ∈ I s ∪ I (s+1), r ≤ k ∧ k < r+2*(r/8) ∧ ((k:ℕ):ZMod p) ∈ shortArc p (kind3H o p c) := by
    intro k hk
    have key : ∀ t, k ∈ I t → r ≤ k ∧ k < r+2*(r/8) ∧ ((k:ℕ):ZMod p) ∈ shortArc p (kind3H o p c) := by
      intro t ht
      simp only [hI, Finset.mem_Ico, max_le_iff, lt_min_iff] at ht
      exact ⟨ht.1.1, ht.2.1, (kind3_arc (o:=o) (c:=c) (s:=t) hp13 ho hc).1 ht.1.2 ht.2.2⟩
    rcases Finset.mem_union.1 hk with h | h
    · exact key s h
    · exact key (s+1) h
  have H := zoneSb_add_le (r:=r) (m:=r/8) (h:=kind3H o p c) hm (I s ∪ I (s+1)) hU
  rw [Finset.card_union_of_disjoint hdisj, hsz] at H
  simp only [hI, Nat.card_Ico] at H
  unfold profileShortCell
  omega

lemma kind3H_root {o c : ℕ} (hp13 : 13 ≤ p) (ho : o=1 ∨ o=3) (hc : c=1 ∨ c=3)
    (hpc : p%4 = if c=1 then 4-o else o) :
    (4 : ZMod p) * ((kind3H o p c : ℕ) : ZMod p) = (o : ZMod p) ∧ kind3H o p c < p := by
  have ho3 : o ≤ 3 := by omega
  rcases hc with rfl | rfl
  · simp only [kind3H, if_true]
    simp only [if_true] at hpc
    have h4 : 4*((p+o)/4) = p+o := by omega
    refine ⟨?_, by omega⟩
    have : ((4*((p+o)/4) : ℕ) : ZMod p) = ((p+o : ℕ) : ZMod p) := by rw [h4]
    push_cast at this
    rw [this]; simp
  · simp only [kind3H, if_neg (by omega : ¬ (3:ℕ)=1)]
    simp only [if_neg (by omega : ¬ (3:ℕ)=1)] at hpc
    have h4 : 4*((3*p+o)/4) = 3*p+o := by omega
    refine ⟨?_, by omega⟩
    have : ((4*((3*p+o)/4) : ℕ) : ZMod p) = ((3*p+o : ℕ) : ZMod p) := by rw [h4]
    push_cast at this
    rw [this]; simp

lemma kind3_cuts {o c A B : ℕ} (ho : o=1 ∨ o=3) (hc : c=1 ∨ c=3)
    (hpc : p%4 = if c=1 then 4-o else o) (hA : (c=1 ∧ A%4=1) ∨ (c=3 ∧ A%4=0)) (hB : B = A+3) :
    (c=1 → profileCut o p A = (A/4)*p + (p+o)/4 ∧ profileCut o p B = (A/4+1)*p) ∧
    (c=3 → profileCut o p A = (A/4)*p ∧ profileCut o p B = (A/4)*p + (3*p+o)/4) := by
  have ho3 : o ≤ 3 := by omega
  obtain ⟨s, hs⟩ : ∃ s, A/4 = s := ⟨_, rfl⟩
  rcases hA with ⟨rfl, hA⟩ | ⟨rfl, hA⟩
  · have hAe : A = 4*s+1 := by omega
    refine ⟨fun _ => ?_, fun h => by omega⟩
    have h1 := poleCut_exact (p:=p) (o:=o) (c:=1) (j:=A) ho hc hpc (Or.inr hA)
    have h2 := poleCut_exact (p:=p) (o:=o) (c:=1) (j:=B) ho hc hpc (Or.inl (by omega))
    simp only [poleOffset, if_neg (by omega : ¬ A%4=0), if_pos (by omega : B%4=0)] at h1 h2
    have e1 : A*p = 4*(s*p)+p := by rw [hAe]; ring
    have e2 : B*p = 4*(s*p)+4*p := by rw [hB, hAe]; ring
    simp only [profileCut_poleCut]
    rw [hs]
    have e3 : (s+1)*p = s*p+p := by rw [add_mul, one_mul]
    omega
  · have hAe : A = 4*s := by omega
    refine ⟨fun h => by omega, fun _ => ?_⟩
    have h1 := poleCut_exact (p:=p) (o:=o) (c:=3) (j:=A) ho hc hpc (Or.inl hA)
    have h2 := poleCut_exact (p:=p) (o:=o) (c:=3) (j:=B) ho hc hpc (Or.inr (by omega))
    simp only [poleOffset, if_pos (by omega : A%4=0), if_neg (by omega : ¬ B%4=0)] at h1 h2
    have e1 : A*p = 4*(s*p) := by rw [hAe]; ring
    have e2 : B*p = 4*(s*p)+3*p := by rw [hB, hAe]; ring
    simp only [profileCut_poleCut]
    rw [hs]
    omega

end K3

/-- Shape of a kind-3 row: the long cell between poles `A4`, `A4 + 3`. -/
def Kind3Shape (P : DeficitRow) : Prop :=
  P.kind=3 ∧ ((P.poleClass=1 ∧ P.A4%4=1) ∨ (P.poleClass=3 ∧ P.A4%4=0)) ∧ P.B4=P.A4+3 ∧
  PolePair P.poleClass P.A4 P.B4 ∧ (1/4:ℚ)≤P.lo ∧ P.hi≤3/5


lemma k3_min (σ m Bq : ℕ) (h : σ ≤ m) :
    min m (σ + (σ - Bq)) ≤ σ + (σ - max Bq (2*σ-m)) ∧ σ + (σ - max Bq (2*σ-m)) ≤ m := by omega
lemma k3_pos (σ m Bq : ℕ) (h : 0 < min m (σ + (σ - Bq))) : 0 < σ := by omega
lemma k3_cell (L R r m : ℕ) (hm : 2 ≤ m) (h : 0 < (R - L) - m) (hL : r ≤ L) (hR : R ≤ r + 2*m) :
    L + 2 ≤ R ∧ (L - r + 1)/2 < m ∧ L ≤ r + 2*((L - r + 1)/2) ∧ r + 2*((L - r + 1)/2) < R := by omega
lemma k3_sig (L R r m : ℕ) (hL : r ≤ L) (hR : R ≤ r + 2*m) : (R - L) - m ≤ m := by omega

/-- **The row-local bounds of a kind-3 row**: for an active positive-deficit row of the shape
`Kind3Shape`, the deficit `min m (σ + (σ - B'))` satisfies the three conjuncts of `ProfileRowLocal`.
This is `longCell_rowLocal` for the long cell of the row, with `B'` the integer short-arc count. -/
theorem kind3_rowLocal {Fr : Frame} (I : HybInst Fr) {o : ℕ} (hL : LamData Fr o) (ho : o=1 ∨ o=3)
    {P : DeficitRow} (hsh : Kind3Shape P) {r p : ℕ} [Fact p.Prime] [I.DiagOK r (r/8)]
    (hr : 1000000000≤r) (ha : profileRowActive o r p P) (hg : profilePrimeGood o r p)
    (hpos : 0<profileRowDeficit o r p P) :
    profileRowDeficit o r p P≤profileBaseline r p ∧
    GLE p (profileBaseline r p-profileRowDeficit o r p P) (Fr.fullPoly r (r/8)) ∧
    GLE p (profileBaseline r p-profileRowDeficit o r p P+topC I r (r/8) p)
      ((Rect.afterTop r (r/8)).fullPolyG Fr) := by
  obtain ⟨hk3, hcls, hB4, hpair, hlo, hhi⟩ := hsh
  have hdef : profileRowDeficit o r p P = profileKind3Deficit o r p P := if_pos hk3
  have hpcls : P.poleClass=1 ∨ P.poleClass=3 := by rcases hcls with h|h <;> omega
  have hp13 := hg.1
  have hN : 4*(r+2*(r/8)+1) < p*p := by simpa only [pow_two] using hg.2.1
  have hpmod := profile_class_mod_pair ho ha
  have hp5 : 5 ≤ p := by omega
  have ho3 : o ≤ 3 := by omega
  -- size of p
  have hpge : r/4 < p := by
    have hs : r/4 ≤ ⌊(P.lo:ℝ)*r⌋₊ := by
      rw [← Nat.floor_div_eq_div (K:=ℝ)]
      apply Nat.floor_mono
      have h1 : ((1/4:ℚ):ℝ) ≤ (P.lo:ℝ) := (Rat.cast_le (K:=ℝ)).2 hlo
      push_cast at h1
      push_cast
      have := mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg r : (0:ℝ) ≤ r)
      linarith
    exact lt_of_le_of_lt hs ha.2.1
  have hm : 2*(r/8) < p := by omega
  have hpr : p ≤ r := by
    have hh1 : (P.hi:ℝ) ≤ 1 := by
      have : ((P.hi:ℚ):ℝ) ≤ ((1:ℚ):ℝ) := (Rat.cast_le (K:=ℝ)).2 (hhi.trans (by norm_num))
      simpa using this
    have hx := Nat.floor_le_floor (mul_le_mul_of_nonneg_right hh1 (Nat.cast_nonneg r : (0:ℝ) ≤ r))
    simp only [one_mul, Nat.floor_natCast] at hx
    exact ha.2.2.trans hx
  have hb : p ≤ r + 2*(r/8) := by omega
  -- cell geometry
  have hLr : r ≤ profileLeft o r p P := le_max_left _ _
  have hRr : profileRight o r p P ≤ r + 2*(r/8) := min_le_left _ _
  have hLA : profileCut o p P.A4 ≤ profileLeft o r p P := le_max_right _ _
  have hRB : profileRight o r p P ≤ profileCut o p P.B4 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hbp : profileRight o r p P ≤ r + p := by omega
  -- positivity of the deficit gives a nonempty overfull cell
  have hσpos : 0 < (profileRight o r p P - profileLeft o r p P) - r/8 := by
    rw [hdef] at hpos
    unfold profileKind3Deficit at hpos
    exact k3_pos _ _ _ hpos
  have hm2 : 2 ≤ r/8 := by omega
  -- the cuts
  have hcuts := kind3_cuts (p:=p) (o:=o) (c:=P.poleClass) (A:=P.A4) (B:=P.B4) ho hpcls hpmod hcls hB4
  -- the root and short arc
  obtain ⟨hroot, hhp⟩ := kind3H_root (p:=p) (o:=o) (c:=P.poleClass) hp13 ho hpcls hpmod
  -- the long node: the left end of the cell
  have hl0 : (((profileLeft o r p P : ℕ)) : ZMod p) ∉ shortArc p (kind3H o p P.poleClass) := by
    have harc := kind3_arc (p:=p) (o:=o) (c:=P.poleClass) (s:=P.A4/4) (x:=profileLeft o r p P) hp13 ho hpcls
    rcases hcls with ⟨hc1, hA⟩ | ⟨hc3, hA⟩
    · obtain ⟨hA1, hB1⟩ := hcuts.1 hc1
      apply harc.2.1 hc1
      · rw [hc1] at *; simp only [kind3H, if_true] at *; omega
      · have e : (P.A4/4+1)*p = (P.A4/4+1)*p := rfl
        omega
    · obtain ⟨hA1, hB1⟩ := hcuts.2 hc3
      apply harc.2.2 hc3
      · omega
      · simp only [kind3H, if_neg (by omega : ¬ P.poleClass=1)]
        omega
  obtain ⟨hn2, hz, hz0a, hz0b⟩ := k3_cell _ _ r _ hm2 hσpos hLr hRr
  let z0 : Fin (r/8) := ⟨(profileLeft o r p P - r + 1)/2, hz⟩
  have hz0 : profileLeft o r p P ≤ r + 2*z0.val ∧ r + 2*z0.val < profileRight o r p P := ⟨hz0a, hz0b⟩
  have hk0 : profileLeft o r p P ≤ profileLeft o r p P ∧ profileLeft o r p P < profileRight o r p P :=
    ⟨le_rfl, by omega⟩
  let c := longCellOfRow (p:=p) (h:=kind3H o p P.poleClass) ho hpcls hpair ha hp5 hbp hhp hroot
    z0 hz0 (profileLeft o r p P) hk0 hl0
  have hcB : c.B ≤ profileShortSize o p P.poleClass -
      (profileShortCell o r p P.poleClass P.q4 + profileShortCell o r p P.poleClass (P.q4+1)) := by
    have := kind3_short_cover (p:=p) (o:=o) (r:=r) (c:=P.poleClass) (s:=P.q4) hp13 ho hpcls hpmod hm
    show (zoneSb p r (r/8) (kind3H o p P.poleClass)).card ≤ _
    exact Nat.le_sub_of_add_le (by rw [← add_assoc]; exact this)
  have hcs : c.sigma = (profileRight o r p P - profileLeft o r p P) - r/8 := rfl
  have hsz : profileShortSize o p P.poleClass ≤ p := by
    unfold profileShortSize; split_ifs <;> omega
  have hk : (4:ZMod p) * ((((4:ZMod p)⁻¹) * (o:ZMod p)).val : ℕ) = (o:ZMod p) := by
    rw [ZMod.natCast_zmod_val, ← mul_assoc, mul_inv_cancel₀ (four_ne_zmod p hp5), one_mul]
  have H := longCell_rowLocal I hL c hp13 hm hN hk hb hhp hroot
    (B' := max (profileShortSize o p P.poleClass -
      (profileShortCell o r p P.poleClass P.q4 + profileShortCell o r p P.poleClass (P.q4+1)))
      (2*c.sigma - r/8)) (δ := profileRowDeficit o r p P)
    (le_max_of_le_left hcB) (max_le (Nat.sub_le_of_le_add (by omega)) (by omega))
    (by rw [hcs]; exact (k3_min _ _ _ (k3_sig _ _ r _ hLr hRr)).2)
    (by rw [hdef]; unfold profileKind3Deficit; exact (k3_min _ _ _ (k3_sig _ _ r _ hLr hRr)).1)
  exact H

end CatalanFrames.HybCommon
