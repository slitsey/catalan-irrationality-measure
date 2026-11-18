module
public import CatalanCore.Li2.DecayCert.Holder.CopyPrelude
public import CatalanCore.Li2.DecayCert.Holder.Analytic
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay CatalanCore.Tools.Joukowski
noncomputable section

theorem holderCopyBound_own_gate (d : QSegment) (p e : CQ) (R : ℚ) (w : HolderCopyWitness) (H : ℚ)
    (hk : w.kind=0) (hc : holderCopyBound d p e R w=some H) :
    (cqDiv (cqSub p d.mid) d.half).2=0 ∧ (cqDiv e d.half).2=0 ∧
    intervalInside (-1) 1 (cqDiv (cqSub p d.mid) d.half).1
      ((cqDiv (cqSub p d.mid) d.half).1+(cqDiv e d.half).1*R)=true ∧ H=holderAQ d 1*(w.gammaHi*R) := by
  unfold holderCopyBound at hc
  dsimp only at hc
  rw [if_pos hk] at hc
  split at hc
  · contradiction
  · split at hc
    · rename_i hg
      have hH := Option.some.inj hc
      refine ⟨hg.1,hg.2.1,hg.2.2,?_⟩
      rw [← hH]
      simp [holderAQ]
    · contradiction

theorem holderCopyBound_sound_own (d : QSegment) (p e : CQ) (R : ℚ) (w : HolderCopyWitness) (H : ℚ)
    (hpos : ∀ x ∈ Icc (-1:ℝ) 1,0 ≤ CatalanCore.Zeta5.Potential.chebF
      (fun k => (d.c k:ℝ)) (d.coeff.length-1) x)
    (hk : w.kind=0) (hc : holderCopyBound d p e R w=some H) :
    ∀ t ∈ Icc 0 (R:ℝ),|P d.measure (cqReal p+cqReal e*(t:ℂ))-P d.measure (cqReal p)| ≤ (H:ℝ) := by
  rcases holderCopyBound_ellipse d p e R w H hc with ⟨hh,hR,hL,hΦ,hF,hA⟩
  rcases holderCopyBound_own_gate d p e R w H hk hc with ⟨hx,hγ,hb,hH⟩
  have hgeom := pure_affine_own_geometry d hh p e R hR hx hγ hb
  have hv := holder_own_cell (d.toSegment hh) hpos (cqReal p) (cqReal e) R (by exact_mod_cast hR) hgeom
  have he : endMajorant (d.toSegment hh) (cqReal p) (cqReal e) R .own ≤ (H:ℝ) := by
    rw [hH,Rat.cast_mul,holderAQ_value]
    simp only [Rat.cast_one,one_pow,mul_one]
    change (∑ k ∈ Finset.range (d.coeff.length-1),(k+1:ℕ)*|(d.c (k+1):ℝ)|)*
      ‖cqReal e/cqReal d.half‖*(R:ℝ) ≤
      (∑ k ∈ Finset.range (d.coeff.length-1),(k+1:ℕ)*|(d.c (k+1):ℝ)|)*(w.gammaHi*R:ℚ)
    calc
      _ = (∑ k ∈ Finset.range (d.coeff.length-1),(k+1:ℕ)*|(d.c (k+1):ℝ)|)*
          (‖cqReal e/cqReal d.half‖*(R:ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hL (by apply Finset.sum_nonneg; intro k hk; positivity)
  intro t ht
  exact (hv t ht).trans he
theorem holderCopyBound_branch_gate (d : QSegment) (p e : CQ) (R : ℚ) (w : HolderCopyWitness) (H : ℚ)
    (hk : w.kind=1) (hc : holderCopyBound d p e R w=some H) :
    let ζ := cqDiv (cqSub p d.mid) d.half
    let γ := cqDiv e d.half
    let L := w.gammaHi*R
    (ζ=(1,0) ∨ ζ=(-1,0)) ∧ 0 ≤ L ∧ L < 1 ∧
    (γ.2 ≠ 0 ∨ (ζ=(1,0) ∧ 0 < γ.1) ∨ (ζ=(-1,0) ∧ γ.1 < 0)) ∧
    0 ≤ w.rootHi ∧ L ≤ w.rootHi^2 ∧ 0 < w.denominatorLo ∧ w.denominatorLo^2 ≤ 2-L ∧
    H=2*holderFQ d w.phiHi*w.rootHi/w.denominatorLo+holderAQ d w.phiHi*L := by
  have hk0 : w.kind ≠ 0 := by omega
  unfold holderCopyBound at hc
  dsimp only at hc ⊢
  rw [if_neg hk0,if_pos hk] at hc
  split at hc
  · contradiction
  · split at hc
    · rename_i hg
      have hH := Option.some.inj hc
      exact ⟨hg.1,hg.2.1,hg.2.2.1,hg.2.2.2.1,hg.2.2.2.2.1,hg.2.2.2.2.2.1,
        hg.2.2.2.2.2.2.1,hg.2.2.2.2.2.2.2,hH.symm⟩
    · contradiction

theorem holderCopyBound_sound_branch (d : QSegment) (p e : CQ) (R : ℚ) (w : HolderCopyWitness) (H : ℚ)
    (hpos : ∀ x ∈ Icc (-1:ℝ) 1,0 ≤ CatalanCore.Zeta5.Potential.chebF
      (fun k => (d.c k:ℝ)) (d.coeff.length-1) x)
    (hk : w.kind=1) (hc : holderCopyBound d p e R w=some H) :
    ∀ t ∈ Icc 0 (R:ℝ),|P d.measure (cqReal p+cqReal e*(t:ℂ))-P d.measure (cqReal p)| ≤ (H:ℝ) := by
  let ζ := cqDiv (cqSub p d.mid) d.half
  let γ := cqDiv e d.half
  let L := w.gammaHi*R
  rcases holderCopyBound_ellipse d p e R w H hc with ⟨hh,hR,hL,hΦ,hF,hA⟩
  rcases holderCopyBound_branch_gate d p e R w H hk hc with ⟨hζ,hL0,hL1,hdir,hroot,hsqrt,hden,hdsq,hH⟩
  have hr : 0 ≤ (R:ℝ) := by exact_mod_cast hR
  have hz (t : ℝ) : (cqReal p+cqReal e*(t:ℂ)-cqReal d.mid)/cqReal d.half=
      cqReal ζ+cqReal γ*(t:ℂ) := by
    dsimp only [ζ,γ]
    rw [cqReal_div,cqReal_sub,cqReal_div]
    ring
  have hγne : γ ≠ (0,0) := by
    intro he
    have hdir' : γ.2 ≠ 0 ∨ (ζ=(1,0) ∧ 0 < γ.1) ∨ (ζ=(-1,0) ∧ γ.1 < 0) := hdir
    simp [he] at hdir'
  have hgne : cqReal γ ≠ 0 := cqReal_ne_of_cqSq_ne γ (fun he => hγne (cq_eq_zero_of_sq γ he))
  have he : cqReal e ≠ 0 := by
    intro he
    apply hgne
    dsimp only [γ]
    rw [cqReal_div,he,zero_div]
  have hgeom : EndCellGeometry (d.toSegment hh) (cqReal p) (cqReal e) R .branch := by
    refine ⟨?_,he,?_⟩
    · change (cqReal p-cqReal d.mid)/cqReal d.half=1 ∨ (cqReal p-cqReal d.mid)/cqReal d.half= -1
      have hζ' : cqReal ζ=1 ∨ cqReal ζ= -1 := by
        have hζ0 : ζ=(1,0) ∨ ζ=(-1,0) := hζ
        rcases hζ0 with hζ0 | hζ0 <;> simp [hζ0,cqReal]
      simpa only [ζ,cqReal_div,cqReal_sub] using hζ'
    · intro t ht
      change 1 < jc ((cqReal p+cqReal e*(t:ℂ)-cqReal d.mid)/cqReal d.half)
      rw [hz]
      exact cq_affine_branch_off ζ γ hζ hdir t ht.1
  have hsmall : ‖cqReal e/cqReal d.half‖*(R:ℝ)<1 := hL.trans_lt (by exact_mod_cast hL1)
  have hv := holder_branch_cell (d.toSegment hh) hpos (cqReal p) (cqReal e) R hr hsmall hgeom
  have hp0 : 0 ≤ endPhi (d.toSegment hh) (cqReal p) (cqReal e) R :=
    zero_le_one.trans (endPhi_one_le _ _ _ _ hr)
  have hF0 : 0 ≤ ∑ k ∈ Finset.range (d.coeff.length-1+1),|(d.c k:ℝ)| *
      (endPhi (d.toSegment hh) (cqReal p) (cqReal e) R)^k := by
    apply Finset.sum_nonneg; intro k hk; positivity
  have hA0 : 0 ≤ ∑ k ∈ Finset.range (d.coeff.length-1),(k+1:ℕ)*|(d.c (k+1):ℝ)| *
      (endPhi (d.toSegment hh) (cqReal p) (cqReal e) R)^k := by
    apply Finset.sum_nonneg; intro k hk; positivity
  have hmaj := branch_majorant_le _ _ (‖cqReal e/cqReal d.half‖*(R:ℝ))
    (holderFQ d w.phiHi:ℝ) (holderAQ d w.phiHi:ℝ) (L:ℝ) w.rootHi w.denominatorLo
    hF0 hA0 (mul_nonneg (norm_nonneg _) hr) hF hA hL
    (by exact_mod_cast hroot) (by exact_mod_cast hsqrt) (by exact_mod_cast hden) (by exact_mod_cast hdsq)
  have hmajor : endMajorant (d.toSegment hh) (cqReal p) (cqReal e) R .branch ≤ (H:ℝ) := by
    rw [hH]
    dsimp only [endMajorant,QSegment.toSegment]
    simp only [Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat]
    convert hmaj using 1 <;> dsimp only [QSegment.toSegment,L] <;> push_cast <;> ring
  intro t ht
  exact (hv t ht).trans hmajor
theorem holderCopyBound_off_gate (d : QSegment) (p e : CQ) (R : ℚ) (w : HolderCopyWitness) (H : ℚ)
    (hk : w.kind=2) (hc : holderCopyBound d p e R w=some H) :
    let ζ := cqDiv (cqSub p d.mid) d.half
    let L := w.gammaHi*R
    0 ≤ L ∧ L^2 < slitDistSq ζ ∧ L < w.d1Lo ∧ L < w.d2Lo ∧
    w.d1Lo^2 ≤ cqSq (cqSub ζ (1,0)) ∧ w.d2Lo^2 ≤ cqSq (cqAdd ζ (1,0)) ∧
    0 < w.denominatorLo ∧ w.denominatorLo^2 ≤ (w.d1Lo-L)*(w.d2Lo-L) ∧
    H=holderFQ d w.phiHi*L/w.denominatorLo+holderAQ d w.phiHi*L := by
  have hk0 : w.kind ≠ 0 := by omega
  have hk1 : w.kind ≠ 1 := by omega
  unfold holderCopyBound at hc
  dsimp only at hc ⊢
  rw [if_neg hk0,if_neg hk1,if_pos hk] at hc
  split at hc
  · contradiction
  · split at hc
    · rename_i hg
      have hH := Option.some.inj hc
      exact ⟨hg.1,hg.2.1,hg.2.2.1,hg.2.2.2.1,hg.2.2.2.2.1,hg.2.2.2.2.2.1,
        hg.2.2.2.2.2.2.1,hg.2.2.2.2.2.2.2,hH.symm⟩
    · contradiction

theorem cqSq_lower_norm (q : CQ) (a : ℚ) (ha : 0 ≤ a) (hsq : a^2 ≤ cqSq q) :
    (a:ℝ) ≤ ‖cqReal q‖ := by
  have he : (a:ℝ)^2 ≤ ‖cqReal q‖^2 := by rw [← cqSq_eq_norm_sq]; exact_mod_cast hsq
  have haR : 0 ≤ (a:ℝ) := by exact_mod_cast ha
  nlinarith [norm_nonneg (cqReal q)]

theorem holderCopyBound_sound_off (d : QSegment) (p e : CQ) (R : ℚ) (w : HolderCopyWitness) (H : ℚ)
    (hpos : ∀ x ∈ Icc (-1:ℝ) 1,0 ≤ CatalanCore.Zeta5.Potential.chebF
      (fun k => (d.c k:ℝ)) (d.coeff.length-1) x)
    (hk : w.kind=2) (hc : holderCopyBound d p e R w=some H) :
    ∀ t ∈ Icc 0 (R:ℝ),|P d.measure (cqReal p+cqReal e*(t:ℂ))-P d.measure (cqReal p)| ≤ (H:ℝ) := by
  let ζ := cqDiv (cqSub p d.mid) d.half
  let γ := cqDiv e d.half
  let L := w.gammaHi*R
  rcases holderCopyBound_ellipse d p e R w H hc with ⟨hh,hR,hL,hΦ,hF,hA⟩
  rcases holderCopyBound_off_gate d p e R w H hk hc with ⟨hL0,hLsq,hL1,hL2,hd1sq,hd2sq,hden,hdsq,hH⟩
  have hr : 0 ≤ (R:ℝ) := by exact_mod_cast hR
  have hL0R : 0 ≤ (L:ℝ) := by exact_mod_cast hL0
  have hL1R : (L:ℝ)<(w.d1Lo:ℝ) := by exact_mod_cast hL1
  have hL2R : (L:ℝ)<(w.d2Lo:ℝ) := by exact_mod_cast hL2
  have hone : cqReal (1,0)=(1:ℂ) := by norm_num [cqReal]
  have hd1 : (w.d1Lo:ℝ) ≤ ‖cqReal ζ-1‖ := by
    have h := cqSq_lower_norm (cqSub ζ (1,0)) w.d1Lo (hL0.trans hL1.le) hd1sq
    simpa only [cqReal_sub,hone] using h
  have hd2 : (w.d2Lo:ℝ) ≤ ‖cqReal ζ+1‖ := by
    have h := cqSq_lower_norm (cqAdd ζ (1,0)) w.d2Lo (hL0.trans hL2.le) hd2sq
    simpa only [cqReal_add,hone] using h
  have hz (t : ℝ) : (cqReal p+cqReal e*(t:ℂ)-cqReal d.mid)/cqReal d.half=
      cqReal ζ+cqReal γ*(t:ℂ) := by
    dsimp only [ζ,γ]
    rw [cqReal_div,cqReal_sub,cqReal_div]
    ring
  have hz0 : (cqReal p-cqReal d.mid)/cqReal d.half=cqReal ζ := by
    dsimp only [ζ]; rw [cqReal_div,cqReal_sub]
  have hgeom : EndCellGeometry (d.toSegment hh) (cqReal p) (cqReal e) R .off := by
    refine ⟨?_,?_⟩
    · change ‖cqReal e/cqReal d.half‖*(R:ℝ)<min
        ‖(cqReal p-cqReal d.mid)/cqReal d.half-1‖ ‖(cqReal p-cqReal d.mid)/cqReal d.half+1‖
      rw [hz0]
      exact lt_min ((hL.trans_lt hL1R).trans_le hd1) ((hL.trans_lt hL2R).trans_le hd2)
    · intro t ht
      change 1 < jc ((cqReal p+cqReal e*(t:ℂ)-cqReal d.mid)/cqReal d.half)
      rw [hz]
      exact cq_affine_off_of_slitSq ζ γ R L hR hL0 (by simpa only [γ,cqReal_div] using hL) hLsq t ht
  have hv := holder_off_cell (d.toSegment hh) hpos (cqReal p) (cqReal e) R hr hgeom
  have hp0 : 0 ≤ endPhi (d.toSegment hh) (cqReal p) (cqReal e) R :=
    zero_le_one.trans (endPhi_one_le _ _ _ _ hr)
  have hF0 : 0 ≤ ∑ k ∈ Finset.range (d.coeff.length-1+1),|(d.c k:ℝ)| *
      (endPhi (d.toSegment hh) (cqReal p) (cqReal e) R)^k := by
    apply Finset.sum_nonneg; intro k hk; positivity
  have hA0 : 0 ≤ ∑ k ∈ Finset.range (d.coeff.length-1),(k+1:ℕ)*|(d.c (k+1):ℝ)| *
      (endPhi (d.toSegment hh) (cqReal p) (cqReal e) R)^k := by
    apply Finset.sum_nonneg; intro k hk; positivity
  have hmaj := off_majorant_le _ _ (‖cqReal e/cqReal d.half‖*(R:ℝ)) ‖cqReal ζ-1‖ ‖cqReal ζ+1‖
    (holderFQ d w.phiHi:ℝ) (holderAQ d w.phiHi:ℝ) (L:ℝ) w.d1Lo w.d2Lo w.denominatorLo
    hF0 hA0 (mul_nonneg (norm_nonneg _) hr) hF hA hL hd1 hd2 hL1R hL2R
    (by exact_mod_cast hden) (by exact_mod_cast hdsq)
  have hmajor : endMajorant (d.toSegment hh) (cqReal p) (cqReal e) R .off ≤ (H:ℝ) := by
    change (∑ k ∈ Finset.range (d.coeff.length-1+1),|(d.c k:ℝ)| *
      (endPhi (d.toSegment hh) (cqReal p) (cqReal e) R)^k)*
      ((‖cqReal e/cqReal d.half‖*(R:ℝ))/Real.sqrt
        ((‖(cqReal p-cqReal d.mid)/cqReal d.half-1‖-‖cqReal e/cqReal d.half‖*(R:ℝ))*
          (‖(cqReal p-cqReal d.mid)/cqReal d.half+1‖-‖cqReal e/cqReal d.half‖*(R:ℝ))))+
      (∑ k ∈ Finset.range (d.coeff.length-1),(k+1:ℕ)*|(d.c (k+1):ℝ)| *
      (endPhi (d.toSegment hh) (cqReal p) (cqReal e) R)^k)*(‖cqReal e/cqReal d.half‖*(R:ℝ)) ≤ (H:ℝ)
    rw [hz0,hH]
    simp only [Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat]
    convert hmaj using 1 <;> dsimp only [QSegment.toSegment,L] <;> push_cast <;> ring
  intro t ht
  exact (hv t ht).trans hmajor

theorem holderCopyBound_sound (d : QSegment) (p e : CQ) (R : ℚ) (w : HolderCopyWitness) (H : ℚ)
    (hpos : ∀ x ∈ Icc (-1:ℝ) 1,0 ≤ CatalanCore.Zeta5.Potential.chebF
      (fun k => (d.c k:ℝ)) (d.coeff.length-1) x)
    (hc : holderCopyBound d p e R w=some H) :
    ∀ t ∈ Icc 0 (R:ℝ),|P d.measure (cqReal p+cqReal e*(t:ℂ))-P d.measure (cqReal p)| ≤ (H:ℝ) := by
  by_cases hk0 : w.kind=0
  · exact holderCopyBound_sound_own d p e R w H hpos hk0 hc
  by_cases hk1 : w.kind=1
  · exact holderCopyBound_sound_branch d p e R w H hpos hk1 hc
  by_cases hk2 : w.kind=2
  · exact holderCopyBound_sound_off d p e R w H hpos hk2 hc
  · unfold holderCopyBound at hc
    dsimp only at hc
    simp only [if_neg hk0,if_neg hk1,if_neg hk2] at hc
    split at hc <;> contradiction
#print axioms holderCopyBound_own_gate
#print axioms holderCopyBound_sound_own
#print axioms holderCopyBound_branch_gate
#print axioms holderCopyBound_sound_branch
#print axioms holderCopyBound_off_gate
#print axioms cqSq_lower_norm
#print axioms holderCopyBound_sound_off
#print axioms holderCopyBound_sound
end
end CatalanCore.Li2.DecayCert
