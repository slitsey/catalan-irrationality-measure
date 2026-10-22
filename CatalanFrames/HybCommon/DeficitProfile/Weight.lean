module
public import CatalanCore.Arith.Hybrid.PiecePatch
public import CatalanFrames.HybCommon.DeficitProfile.Family
public import CatalanFrames.HybCommon.LogDhybT
@[expose] public section
open Finset Filter Classical CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid
namespace CatalanFrames.HybCommon
variable {Fr : Frame}

noncomputable def lowLiftPiece : Piece := mkPiece 1 8 1 4 19 (-8) 320 8
noncomputable def flatLift1 : Piece := mkPiece 1 4 9 10 17 0 64 8
noncomputable def flatLift3 : Piece := mkPiece 1 4 9 14 17 0 64 8

noncomputable def profileWeight (I : HybInst Fr) (o r : ℕ) : ℕ→ℝ :=
  patchPiece (fun p => (p : ZMod 4)=cJ3 o) r flatLift3
    (patchPiece (fun p => (p : ZMod 4)=cJ1 o) r flatLift1
      (patchPiece (fun _ => True) r lowLiftPiece (WTG I o r)))

theorem WTG_le_profileWeight (I : HybInst Fr) (o r p : ℕ) :
    WTG I o r p≤profileWeight I o r p :=
  (le_patchPiece _ _ _ _ _).trans ((le_patchPiece _ _ _ _ _).trans (le_patchPiece _ _ _ _ _))

theorem profileWeight_nonneg (I : HybInst Fr) (o r p : ℕ) : 0≤profileWeight I o r p :=
  (WTG_nonneg _ _ _ _).trans (WTG_le_profileWeight I o r p)

theorem lowLift_compatible1 : ∀Q∈l3x, Q=lowLiftPiece ∨ lowLiftPiece.t≤Q.s ∨ Q.t≤lowLiftPiece.s := by
  norm_num [l3x,ld1,l3,lowLiftPiece,mkPiece,Piece.mk.injEq]
theorem lowLift_compatible3 : ∀Q∈l1x, Q=lowLiftPiece ∨ lowLiftPiece.t≤Q.s ∨ Q.t≤lowLiftPiece.s := by
  norm_num [l1x,ld1,l1,lowLiftPiece,mkPiece,Piece.mk.injEq]
theorem flatLift_compatible1 : ∀Q∈l3x, Q=flatLift1 ∨ flatLift1.t≤Q.s ∨ Q.t≤flatLift1.s := by
  norm_num [l3x,ld1,l3,flatLift1,mkPiece,Piece.mk.injEq]
theorem flatLift_compatible3 : ∀Q∈l1x, Q=flatLift3 ∨ flatLift3.t≤Q.s ∨ Q.t≤flatLift3.s := by
  norm_num [l1x,ld1,l1,flatLift3,mkPiece,Piece.mk.injEq]

theorem profileWeight_covers1 {I : HybInst Fr} {o : ℕ} (T : TropFacts I o)
    (r : ℕ) (hr : 400≤r) : ∀Q∈l3x, Covers (cJ1 o) (profileWeight I o r) r Q := by
  intro Q hQ
  have h := (WTG_covers_l3x T r hr Q hQ).patch_compatible (fun _ => True) (lowLift_compatible1 Q hQ)
  have h' := h.patch_compatible (fun p : ℕ => (p : ZMod 4)=cJ1 o) (flatLift_compatible1 Q hQ)
  apply h'.patch_inactive (fun p : ℕ => (p : ZMod 4)=cJ3 o)
  intro p hp hc he
  have hn : cJ1 o≠cJ3 o := by rcases T.ho with rfl | rfl <;> decide
  exact hn (hc.symm.trans he)

theorem profileWeight_covers3 {I : HybInst Fr} {o : ℕ} (T : TropFacts I o)
    (r : ℕ) (hr : 400≤r) : ∀Q∈l1x, Covers (cJ3 o) (profileWeight I o r) r Q := by
  intro Q hQ
  have h := (WTG_covers_l1x T r hr Q hQ).patch_compatible (fun _ => True) (lowLift_compatible3 Q hQ)
  have h' := h.patch_inactive (P := flatLift1) (fun p : ℕ => (p : ZMod 4)=cJ1 o) (by
    intro p hp hc he
    have hn : cJ3 o≠cJ1 o := by rcases T.ho with rfl | rfl <;> decide
    exact hn (hc.symm.trans he))
  exact h'.patch_compatible (fun p : ℕ => (p : ZMod 4)=cJ3 o) (flatLift_compatible3 Q hQ)

theorem profileWeight_prefix (I : HybInst Fr) (o r p : ℕ) (hp : p≤⌊(1/68 : ℝ)*r⌋₊) :
    profileWeight I o r p=WTG I o r p := by
  have hlow : p≤⌊lowLiftPiece.s*r⌋₊ := hp.trans (Nat.floor_le_floor (by
    norm_num [lowLiftPiece,mkPiece]; nlinarith [Nat.cast_nonneg (α := ℝ) r]))
  have hf1 : p≤⌊flatLift1.s*r⌋₊ := hp.trans (Nat.floor_le_floor (by
    norm_num [flatLift1,mkPiece]; nlinarith [Nat.cast_nonneg (α := ℝ) r]))
  have hf3 : p≤⌊flatLift3.s*r⌋₊ := hp.trans (Nat.floor_le_floor (by
    norm_num [flatLift3,mkPiece]; nlinarith [Nat.cast_nonneg (α := ℝ) r]))
  unfold profileWeight
  rw [patchPiece_eq_of_le_start _ _ _ _ hf3,patchPiece_eq_of_le_start _ _ _ _ hf1,
    patchPiece_eq_of_le_start _ _ _ _ hlow]

theorem profileWeight_class1 {I : HybInst Fr} {o : ℕ} (T : TropFacts I o) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠr : ℕ in atTop, clsSum 4 (cJ1 o) (profileWeight I o r) 0 (5*r)≤
      (r : ℝ)^2 * (((9/4 : ℝ)*(1/68)+listInt l3x)/2+ε) := by
  have h := class_total (M := 4) (isUnit_cJ1 T.ho) (α0 := 9/4) (t1 := 1/68)
    (by norm_num) (by norm_num) l3x l3x_chain hε
  filter_upwards [h,eventually_ge_atTop 400] with r hr hr400
  have hh := hr (profileWeight I o r) (by
    intro p hp hprime hc
    rw [profileWeight_prefix I o r p hp]
    exact WTG_prefix T r p (by omega)) (profileWeight_covers1 T r hr400)
  rw [l3x_end,floor_frac] at hh
  simpa [tot4] using hh

theorem profileWeight_class3 {I : HybInst Fr} {o : ℕ} (T : TropFacts I o) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠr : ℕ in atTop, clsSum 4 (cJ3 o) (profileWeight I o r) 0 (5*r/3)≤
      (r : ℝ)^2 * (((9/4 : ℝ)*(1/68)+listInt l1x)/2+ε) := by
  have h := class_total (M := 4) (isUnit_cJ3 T.ho) (α0 := 9/4) (t1 := 1/68)
    (by norm_num) (by norm_num) l1x l1x_chain hε
  filter_upwards [h,eventually_ge_atTop 400] with r hr hr400
  have hh := hr (profileWeight I o r) (by
    intro p hp hprime hc
    rw [profileWeight_prefix I o r p hp]
    exact WTG_prefix T r p (by omega)) (profileWeight_covers3 T r hr400)
  rw [l1x_end,floor_frac] at hh
  simpa [tot4] using hh

theorem profileSupport_lower {L : List DeficitRow} (hD : RowData L) {o r p : ℕ}
    (hs : profileSupportL L o r p) : r/8<p := by
  obtain ⟨P,hP,ha⟩ := hs
  have hh := (hD.lift P hP).1
  have hhR := (Rat.cast_le (K := ℝ)).2 hh
  push_cast at hhR
  have hR : (1/8 : ℝ)*r≤(P.lo : ℝ)*r := mul_le_mul_of_nonneg_right hhR (Nat.cast_nonneg r)
  have hf := Nat.floor_le_floor hR
  have he : ⌊(1/8 : ℝ)*r⌋₊=r/8 := by simpa using floor_frac 1 8 r
  rw [he] at hf
  exact lt_of_le_of_lt hf ha.2.1

theorem profileBaseline_le_weight {L : List DeficitRow} (hD : RowData L)
    {I : HybInst Fr} {o r p : ℕ}
    (hs : profileSupportL L o r p) : (profileBaseline r p : ℝ)≤profileWeight I o r p := by
  obtain ⟨P,hP,ha⟩ := hs
  have hcert := hD.basic P hP
  have hmeta := hD.lift P hP
  by_cases hk : P.kind=0
  · have hhi := hmeta.2
    rw [if_pos hk] at hhi
    have hloR := (Rat.cast_le (K := ℝ)).2 hmeta.1
    have hhiR := (Rat.cast_le (K := ℝ)).2 hhi
    push_cast at hloR hhiR
    have hlo : ⌊lowLiftPiece.s*r⌋₊<p := by
      have hf := Nat.floor_le_floor (mul_le_mul_of_nonneg_right hloR (Nat.cast_nonneg r))
      simpa [lowLiftPiece,mkPiece] using lt_of_le_of_lt hf ha.2.1
    have hhi' : p≤⌊lowLiftPiece.t*r⌋₊ := ha.2.2.trans (Nat.floor_le_floor
      (mul_le_mul_of_nonneg_right (by simpa [lowLiftPiece,mkPiece] using hhiR) (Nat.cast_nonneg r)))
    have hpn : p≤r/4 := by simpa [lowLiftPiece,floor_mk_t] using hhi'
    have hx : (profileBaseline r p : ℝ)≤lowLiftPiece.α*r+lowLiftPiece.β*p+lowLiftPiece.C := by
      have hh := real_of_int_bound (x := profileBaseline r p) (r := r) (p := p) 8 19 (-8) 320 (by norm_num) (by
        unfold profileBaseline
        split_ifs <;> omega)
      simpa [lowLiftPiece,mkPiece] using hh
    exact hx.trans ((bound_le_patchPiece (fun _ => True) r lowLiftPiece (WTG I o r) trivial hlo hhi').trans
      ((le_patchPiece _ _ _ _ _).trans (le_patchPiece _ _ _ _ _)))
  · rw [if_neg hk] at hmeta
    have hloR := (Rat.cast_le (K := ℝ)).2 hmeta.2.1
    push_cast at hloR
    have hlo : ⌊(1/4 : ℝ)*r⌋₊<p := lt_of_le_of_lt
      (Nat.floor_le_floor (mul_le_mul_of_nonneg_right hloR (Nat.cast_nonneg r))) ha.2.1
    have hpn : r/4<p := by
      have he : ⌊(1/4 : ℝ)*r⌋₊=r/4 := by simpa using floor_frac 1 4 r
      rwa [he] at hlo
    have he : profileBaseline r p=2*r+r/8 := by unfold profileBaseline; rw [if_neg (by omega)]
    rcases hcert.1 with hc | hc
    · have hclass : (p : ZMod 4)=cJ1 o := by simpa [profileClass,hc,cJ1] using ha.1
      have hhiR : (P.hi : ℝ)≤9/10 := by
        have hh := (Rat.cast_le (K := ℝ)).2 (show P.hi≤(9/10 : ℚ) by simpa [hc] using hmeta.2.2)
        push_cast at hh; exact hh
      have hhi : p≤⌊flatLift1.t*r⌋₊ := ha.2.2.trans (Nat.floor_le_floor
        (mul_le_mul_of_nonneg_right (by simpa [flatLift1,mkPiece] using hhiR) (Nat.cast_nonneg r)))
      have hx : (profileBaseline r p : ℝ)≤flatLift1.α*r+flatLift1.β*p+flatLift1.C := by
        rw [he]
        have hh := real_of_int_bound (x := 2*r+r/8) (r := r) (p := p) 8 17 0 64 (by norm_num) (by omega)
        simpa [flatLift1,mkPiece] using hh
      exact hx.trans ((bound_le_patchPiece _ r flatLift1 _ hclass (by simpa [flatLift1,mkPiece] using hlo) hhi).trans (le_patchPiece _ _ _ _ _))
    · have hclass : (p : ZMod 4)=cJ3 o := by simpa [profileClass,hc,cJ3] using ha.1
      have hhiR : (P.hi : ℝ)≤9/14 := by
        have hh := (Rat.cast_le (K := ℝ)).2 (show P.hi≤(9/14 : ℚ) by simpa [hc] using hmeta.2.2)
        push_cast at hh; exact hh
      have hhi : p≤⌊flatLift3.t*r⌋₊ := ha.2.2.trans (Nat.floor_le_floor
        (mul_le_mul_of_nonneg_right (by simpa [flatLift3,mkPiece] using hhiR) (Nat.cast_nonneg r)))
      have hx : (profileBaseline r p : ℝ)≤flatLift3.α*r+flatLift3.β*p+flatLift3.C := by
        rw [he]
        have hh := real_of_int_bound (x := 2*r+r/8) (r := r) (p := p) 8 17 0 64 (by norm_num) (by omega)
        simpa [flatLift3,mkPiece] using hh
      exact hx.trans (bound_le_patchPiece _ r flatLift3 _ hclass (by simpa [flatLift3,mkPiece] using hlo) hhi)

theorem profileWeight_tail (I : HybInst Fr) (o r p : ℕ) (hp : r<p) :
    profileWeight I o r p=WTG I o r p := by
  have hlow : ⌊lowLiftPiece.t*r⌋₊<p := by simp only [lowLiftPiece,floor_mk_t]; omega
  have hf1 : ⌊flatLift1.t*r⌋₊<p := by simp only [flatLift1,floor_mk_t]; omega
  have hf3 : ⌊flatLift3.t*r⌋₊<p := by simp only [flatLift3,floor_mk_t]; omega
  unfold profileWeight
  rw [patchPiece_eq_of_gt_end _ _ _ _ hf3,patchPiece_eq_of_gt_end _ _ _ _ hf1,
    patchPiece_eq_of_gt_end _ _ _ _ hlow]

end CatalanFrames.HybCommon
