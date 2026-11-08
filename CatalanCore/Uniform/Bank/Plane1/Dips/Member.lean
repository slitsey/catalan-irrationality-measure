module

public import CatalanCore.Uniform.Bank.Plane1.Dips.Entry
public import CatalanCore.Rect.CommonMinor

@[expose] public section
set_option Elab.async false
set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option maxHeartbeats 1600000

/-! # The dip price of a member (wave R0; ledger R01-R03)

`restrict_gle` is Lemma 5.1' for a member: a dual `ρ x + γ y ≥ Wd x y` of the **full** system (all common nodes retained,
every pivot present) prices every principal restriction (a retained set of common nodes with the full border): the
member's pivots are those of the full system whose target is retained; the others are *reverted* (unpivoted), which costs
one unit on the reverted line (`Wd_restrict_le`) and is paid for by a deleted node (`debit 2` of the catalogue: at most
one reverted row and one reverted column per deleted node, `2 m < p`).

* `GData.restrict G e`: the gauge data of the sub-index `e : κ → ι`;
* `restrict_GOK`: the hypotheses of the entry lemma pass to the restriction (the levels of reverted lines are their own);
* `Wd_restrict_le`: `Wd' x y ≤ Wd (e x) (e y) + revR x + revC y`;
* `restrict_gle`: `GLE p B (det Ment')` for `B ≥ Σ ρ + Σ γ + #reverted`.

The hybrid specialisation (`member_gle`) is at the end: index `Fin r ⊕ Fin m`, member `↥s ⊕ Fin m`, `det = commonMinorPoly`. -/

namespace CatalanCore.Uniform.Bank.Plane1.Dips
open Finset Polynomial CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Rect

section Restrict

variable {ι κ : Type} (G : GData ι) (e : κ → ι)

/-- The gauge data of the sub-index `e`: pivots whose target is not in the range of `e` are dropped. -/
noncomputable def GData.restrict : GData κ where
  rn x := G.rn (e x)
  cn x := G.cn (e x)
  isC x := G.isC (e x)
  π x := match G.π (e x) with
    | some a => open Classical in if h : ∃ b, e b = a then some h.choose else none
    | none => none
  π' x := match G.π' (e x) with
    | some a => open Classical in if h : ∃ b, e b = a then some h.choose else none
    | none => none
  lr x := G.lr (e x)
  lc x := G.lc (e x)

variable {G e}

theorem restrict_π_some (he : Function.Injective e) {x b : κ} (h : (G.restrict e).π x = some b) :
    G.π (e x) = some (e b) := by
  unfold GData.restrict at h
  simp only at h
  rcases hπ : G.π (e x) with _ | a
  · rw [hπ] at h; simp at h
  · rw [hπ] at h
    simp only at h
    by_cases hex : ∃ b', e b' = a
    · rw [dif_pos hex] at h
      have : hex.choose = b := Option.some.inj h
      rw [← this, hex.choose_spec]
    · rw [dif_neg hex] at h; simp at h

theorem restrict_π_of (he : Function.Injective e) {x b : κ} (h : G.π (e x) = some (e b)) :
    (G.restrict e).π x = some b := by
  unfold GData.restrict
  simp only
  rw [h]
  simp only
  have hex : ∃ b', e b' = e b := ⟨b, rfl⟩
  rw [dif_pos hex]
  exact congrArg some (he hex.choose_spec)

theorem restrict_π_none_of (he : Function.Injective e) {x : κ} {a : ι} (h : G.π (e x) = some a)
    (hn : ¬ ∃ b, e b = a) : (G.restrict e).π x = none := by
  unfold GData.restrict
  simp only
  rw [h]
  simp only
  rw [dif_neg hn]

theorem restrict_π_none (x : κ) (h : G.π (e x) = none) : (G.restrict e).π x = none := by
  unfold GData.restrict
  simp only
  rw [h]

theorem restrict_π'_some (he : Function.Injective e) {x b : κ} (h : (G.restrict e).π' x = some b) :
    G.π' (e x) = some (e b) := by
  unfold GData.restrict at h
  simp only at h
  rcases hπ : G.π' (e x) with _ | a
  · rw [hπ] at h; simp at h
  · rw [hπ] at h
    simp only at h
    by_cases hex : ∃ b', e b' = a
    · rw [dif_pos hex] at h
      have : hex.choose = b := Option.some.inj h
      rw [← this, hex.choose_spec]
    · rw [dif_neg hex] at h; simp at h

theorem restrict_π'_of (he : Function.Injective e) {x b : κ} (h : G.π' (e x) = some (e b)) :
    (G.restrict e).π' x = some b := by
  unfold GData.restrict
  simp only
  rw [h]
  simp only
  have hex : ∃ b', e b' = e b := ⟨b, rfl⟩
  rw [dif_pos hex]
  exact congrArg some (he hex.choose_spec)

theorem restrict_π'_none (x : κ) (h : G.π' (e x) = none) : (G.restrict e).π' x = none := by
  unfold GData.restrict
  simp only
  rw [h]

/-- The reverted rows: pivoted in the full system, not in the restriction. -/
noncomputable def revR (G : GData ι) (e : κ → ι) (x : κ) : ℕ :=
  if (G.π (e x)).isSome && ((G.restrict e).π x).isNone then 1 else 0

noncomputable def revC (G : GData ι) (e : κ → ι) (x : κ) : ℕ :=
  if (G.π' (e x)).isSome && ((G.restrict e).π' x).isNone then 1 else 0

end Restrict

section RestrictLemmas

variable {ι κ : Type} [DecidableEq ι] [DecidableEq κ]
variable {p : ℕ} [hp : Fact p.Prime] {Fr : Frame}
variable {G : GData ι} {Vr Vc : ι → ℚ} {e : κ → ι}

/-- The levels of the restriction: the full level where the pivot is retained, the plain level elsewhere. -/
noncomputable def restrictVr (p : ℕ) (Fr : Frame) (G : GData ι) (Vr : ι → ℚ) (e : κ → ι) (x : κ) : ℚ :=
  open Classical in
  if (G.restrict e).π x = none then Vp p Fr (G.rn (e x)) else Vr (e x)

noncomputable def restrictVc (p : ℕ) (Fr : Frame) (G : GData ι) (Vc : ι → ℚ) (e : κ → ι) (x : κ) : ℚ :=
  open Classical in
  if (G.restrict e).π' x = none then Vp p Fr (G.cn (e x)) else Vc (e x)

theorem restrict_GOK (hG : GOK p Fr G Vr Vc) (he : Function.Injective e) :
    GOK p Fr (G.restrict e) (restrictVr p Fr G Vr e) (restrictVc p Fr G Vc e) where
  hden := hG.hden
  h5 := hG.h5
  hnorm := hG.hnorm
  small_r u := hG.small_r (e u)
  small_c u := hG.small_c (e u)
  isC_node u hu := hG.isC_node (e u) hu
  rowPiv x b h := by
    obtain ⟨hC, hCx, j, hj0, hX, hrel⟩ := hG.rowPiv (e x) (e b) (restrict_π_some he h)
    exact ⟨hC, hCx, j, hj0, hX, hrel⟩
  colPiv y b h := by
    obtain ⟨hC, hCx, j, hj0, hX, hrel⟩ := hG.colPiv (e y) (e b) (restrict_π'_some he h)
    exact ⟨hC, hCx, j, hj0, hX, hrel⟩
  lr_mem x := hG.lr_mem (e x)
  lc_mem y := hG.lc_mem (e y)
  Vr_spec x := by
    classical
    unfold restrictVr
    rcases h : (G.restrict e).π x with _ | b
    · have e1 : (G.restrict e).rr x = 0 := by simp [GData.rr, h]
      simp [e1]
      rfl
    · have h' := restrict_π_some he h
      have e1 : (G.restrict e).rr x = G.rr (e x) := by simp [GData.rr, h, h', GData.restrict]
      have e2 : (G.restrict e).aR x = b := by simp [GData.aR, h]
      have e3 : G.aR (e x) = e b := by simp [GData.aR, h']
      have := hG.Vr_spec (e x)
      rw [e3] at this
      rw [e1, e2]
      simpa [GData.restrict] using this
  Vc_spec y := by
    classical
    unfold restrictVc
    rcases h : (G.restrict e).π' y with _ | b
    · have e1 : (G.restrict e).cc y = 0 := by simp [GData.cc, h]
      simp [e1]
      rfl
    · have h' := restrict_π'_some he h
      have e1 : (G.restrict e).cc y = G.cc (e y) := by simp [GData.cc, h, h', GData.restrict]
      have e2 : (G.restrict e).aC y = b := by simp [GData.aC, h]
      have e3 : G.aC (e y) = e b := by simp [GData.aC, h']
      have := hG.Vc_spec (e y)
      rw [e3] at this
      rw [e1, e2]
      simpa [GData.restrict] using this

theorem restrictVr_eq (hG : GOK p Fr G Vr Vc) (x : κ) (h : revR G e x = 0) :
    restrictVr p Fr G Vr e x = Vr (e x) := by
  classical
  unfold restrictVr
  by_cases h1 : (G.restrict e).π x = none
  · rw [if_pos h1]
    have h2 : G.π (e x) = none := by
      unfold revR at h
      rcases h3 : G.π (e x) with _ | a
      · rfl
      · rw [h3] at h
        simp [h1] at h
    have := hG.Vr_spec (e x)
    have e1 : G.rr (e x) = 0 := by simp [GData.rr, h2]
    rw [e1] at this
    simpa using this.symm
  · rw [if_neg h1]

theorem restrictVc_eq (hG : GOK p Fr G Vr Vc) (x : κ) (h : revC G e x = 0) :
    restrictVc p Fr G Vc e x = Vc (e x) := by
  classical
  unfold restrictVc
  by_cases h1 : (G.restrict e).π' x = none
  · rw [if_pos h1]
    have h2 : G.π' (e x) = none := by
      unfold revC at h
      rcases h3 : G.π' (e x) with _ | a
      · rfl
      · rw [h3] at h
        simp [h1] at h
    have := hG.Vc_spec (e x)
    have e1 : G.cc (e x) = 0 := by simp [GData.cc, h2]
    rw [e1] at this
    simpa using this.symm
  · rw [if_neg h1]

theorem restrict_rn_aR (he : Function.Injective e) (x : κ) :
    (G.restrict e).rn ((G.restrict e).aR x) = G.rn (e x) ∨
      (G.restrict e).rn ((G.restrict e).aR x) = G.rn (G.aR (e x)) := by
  rcases h : (G.restrict e).π x with _ | b
  · left
    have e2 : (G.restrict e).aR x = x := by simp [GData.aR, h]
    rw [e2]; rfl
  · right
    have e2 : (G.restrict e).aR x = b := by simp [GData.aR, h]
    have e3 : G.aR (e x) = e b := by simp [GData.aR, restrict_π_some he h]
    rw [e2, e3]
    rfl

theorem restrict_cn_aC (he : Function.Injective e) (x : κ) :
    (G.restrict e).cn ((G.restrict e).aC x) = G.cn (e x) ∨
      (G.restrict e).cn ((G.restrict e).aC x) = G.cn (G.aC (e x)) := by
  rcases h : (G.restrict e).π' x with _ | b
  · left
    have e2 : (G.restrict e).aC x = x := by simp [GData.aC, h]
    rw [e2]; rfl
  · right
    have e2 : (G.restrict e).aC x = b := by simp [GData.aC, h]
    have e3 : G.aC (e x) = e b := by simp [GData.aC, restrict_π'_some he h]
    rw [e2, e3]
    rfl


theorem restrict_rn (x : κ) : (G.restrict e).rn x = G.rn (e x) := rfl
theorem restrict_cn (x : κ) : (G.restrict e).cn x = G.cn (e x) := rfl

theorem le_max4 {a b c d X : ℕ} (h : (a ≤ X ∨ b ≤ X ∨ c ≤ X ∨ d ≤ X)) : a ≤ max (max a b) (max c d) := by
  omega

/-- **The weights of a restriction are those of the full system, plus the reverted lines.** -/
theorem Wd_restrict_le (hG : GOK p Fr G Vr Vc) (he : Function.Injective e) (x y : κ) :
    Wd p Fr (G.restrict e) (restrictVr p Fr G Vr e) (restrictVc p Fr G Vc e) x y ≤
      Wd p Fr G Vr Vc (e x) (e y) + revR G e x + revC G e y := by
  classical
  unfold Wd
  by_cases hp' : ((G.restrict e).π x = some y ∨ (G.restrict e).π' y = some x)
  · rw [if_pos hp']; exact Nat.zero_le _
  · rw [if_neg hp']
    have hp'' : ¬ (G.π (e x) = some (e y) ∨ G.π' (e y) = some (e x)) := by
      rintro (h | h)
      · exact hp' (Or.inl (restrict_π_of he h))
      · exact hp' (Or.inr (restrict_π'_of he h))
    rw [if_neg hp'']
    by_cases hf : (((G.restrict e).rn x : ℤ) ≡ (G.restrict e).cn y [ZMOD p])
    · have hf' : ((G.rn (e x) : ℕ) : ℤ) ≡ G.cn (e y) [ZMOD p] := hf
      rw [if_pos hf, if_pos hf']
      simp only [restrict_rn, restrict_cn]
      have hr : G.rn (e ((G.restrict e).aR x)) = G.rn (e x) ∨
          G.rn (e ((G.restrict e).aR x)) = G.rn (G.aR (e x)) := restrict_rn_aR he x
      have hc : G.cn (e ((G.restrict e).aC y)) = G.cn (e y) ∨
          G.cn (e ((G.restrict e).aC y)) = G.cn (G.aC (e y)) := restrict_cn_aC he y
      rcases hr with hr | hr <;> rcases hc with hc | hc <;> rw [hr, hc] <;> omega
    · have hf' : ¬ (((G.rn (e x) : ℕ) : ℤ) ≡ G.cn (e y) [ZMOD p]) := hf
      rw [if_neg hf, if_neg hf']
      by_cases h0 : revR G e x = 0 ∧ revC G e y = 0
      · rw [restrictVr_eq hG x h0.1, restrictVc_eq hG y h0.2]
        split_ifs <;> omega
      · have h1 : 1 ≤ revR G e x + revC G e y := by
          by_contra hlt
          exact h0 ⟨by omega, by omega⟩
        split_ifs <;> omega

end RestrictLemmas

section Gle

variable {ι κ : Type} [DecidableEq ι] [Fintype κ] [DecidableEq κ] [LinearOrder κ]
variable {p : ℕ} [hp : Fact p.Prime] {Fr : Frame}
variable {G : GData ι} {Vr Vc : ι → ℚ} {e : κ → ι}

/-- **Lemma 5.1' for a restriction** (a member): a dual of the full system prices `det Ment'`, with one extra unit
for each reverted line. -/
theorem restrict_gle (hG : GOK p Fr G Vr Vc) (he : Function.Injective e)
    (hord : ∀ x b, (G.restrict e).π x = some b → b < x) (hordc : ∀ y b, (G.restrict e).π' y = some b → b < y)
    (ρ γ : ι → ℚ) (hfeas : ∀ x y, ((Wd p Fr G Vr Vc x y : ℕ) : ℚ) ≤ ρ x + γ y) {B : ℕ}
    (hB : ∑ x : κ, ρ (e x) + ∑ y : κ, γ (e y) +
      ((∑ x : κ, revR G e x + ∑ y : κ, revC G e y : ℕ) : ℚ) ≤ B) :
    GLE p B (Ment Fr (G.restrict e)).det := by
  have hG' := restrict_GOK hG he
  refine trop_cell_gauge (Ment Fr (G.restrict e))
    (pivotRowGauge (G.restrict e).π (fun x => C ((G.restrict e).lr x)))
    (pivotColGauge (G.restrict e).π' (fun y => C ((G.restrict e).lc y)))
    (det_pivotRowGauge _ _ hord) (det_pivotColGauge _ _ hordc)
    (fun a b => Wd p Fr (G.restrict e) (restrictVr p Fr G Vr e) (restrictVc p Fr G Vc e) a b)
    (fun a b => entry_gle hG' hord a b)
    (fun a => ρ (e a) + revR G e a) (fun b => γ (e b) + revC G e b) ?_ ?_
  · intro a b
    have h1 := Wd_restrict_le hG he a b
    have h2 := hfeas (e a) (e b)
    have h3 : ((Wd p Fr (G.restrict e) (restrictVr p Fr G Vr e) (restrictVc p Fr G Vc e) a b : ℕ) : ℚ) ≤
        ((Wd p Fr G Vr Vc (e a) (e b) : ℕ) : ℚ) + (revR G e a : ℕ) + (revC G e b : ℕ) := by exact_mod_cast h1
    linarith
  · rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    push_cast at hB
    linarith

end Gle


/-! ### The hybrid: `Fin r ⊕ Fin m`, members `↥s ⊕ Fin m` -/

section Hybrid

variable {p : ℕ} [hp : Fact p.Prime] {Fr : Frame} (r m : ℕ)

/-- The gauge data of the full hybrid: common nodes `c < r` (rows and columns), border rows `r + 2 i`, border columns
`r + 2 i + 1`, the pivots of the border lines on common nodes. -/
def hfData (pR pC : Fin m → Option (Fin r)) (lR lC : Fin m → ℚ) : GData (Fin r ⊕ Fin m) where
  rn := Sum.elim (fun c => c.1) (fun i => r + 2 * i.1)
  cn := Sum.elim (fun c => c.1) (fun i => r + 2 * i.1 + 1)
  isC := Sum.elim (fun _ => true) (fun _ => false)
  π := Sum.elim (fun _ => none) (fun i => (pR i).map Sum.inl)
  π' := Sum.elim (fun _ => none) (fun i => (pC i).map Sum.inl)
  lr := Sum.elim (fun _ => 0) (fun i => lR i)
  lc := Sum.elim (fun _ => 0) (fun i => lC i)

/-- The embedding of a member into the full index. -/
def memEmb (s : Finset (Fin r)) : (↥s ⊕ Fin m) → (Fin r ⊕ Fin m) := Sum.map Subtype.val id

theorem memEmb_inj (s : Finset (Fin r)) : Function.Injective (memEmb r m s) := by
  intro a b h
  rcases a with a | a <;> rcases b with b | b <;> simp [memEmb] at h
  · exact congrArg Sum.inl h
  · exact congrArg Sum.inr h

/-- The order of a member: common nodes before the border, each by index. -/
def memKey (s : Finset (Fin r)) : (↥s ⊕ Fin m) → ℕ := Sum.elim (fun c => c.1.1) (fun i => r + i.1)

theorem memKey_inj (s : Finset (Fin r)) : Function.Injective (memKey r m s) := by
  intro a b h
  rcases a with a | a <;> rcases b with b | b <;> simp [memKey] at h
  · exact congrArg Sum.inl (Subtype.ext (Fin.ext h))
  · have := a.1.2; omega
  · have := b.1.2; omega
  · exact congrArg Sum.inr (Fin.ext h)

@[instance_reducible] def memLO (s : Finset (Fin r)) : LinearOrder (↥s ⊕ Fin m) := LinearOrder.lift' (memKey r m s) (memKey_inj r m s)

/-- The hypotheses on the pivots of the full hybrid (`2 m < p` and `3 (r + 2 m) < p²` are those of the catalogue).
`VR`, `VC` are the effective levels `V*` of the border rows and columns. -/
structure HybPiv (p : ℕ) [Fact p.Prime] (Fr : Frame) (pR pC : Fin m → Option (Fin r)) (lR lC : Fin m → ℚ)
    (VR VC : Fin m → ℚ) : Prop where
  hden : ∀ i, (Fr.μ i).den ≤ 3
  h5 : 5 ≤ p
  hnorm : Fr.norm = 1
  hN : 3 * (r + 2 * m) < p * p
  hm : 2 * m < p
  rowP : ∀ i c, pR i = some c → ∃ j : ℕ, 0 < j ∧ r + 2 * i.1 = c.1 + j * p ∧
    lR i * (j * Up p Fr c.1) = Vp p Fr (r + 2 * i.1) - Vp p Fr c.1 ∧
    (1 - lR i) * VR i = Vp p Fr (r + 2 * i.1) - lR i * Vp p Fr c.1
  rowN : ∀ i, pR i = none → VR i = Vp p Fr (r + 2 * i.1)
  colP : ∀ i c, pC i = some c → ∃ j : ℕ, 0 < j ∧ r + 2 * i.1 + 1 = c.1 + j * p ∧
    lC i * (j * Up p Fr c.1) = Vp p Fr (r + 2 * i.1 + 1) - Vp p Fr c.1 ∧
    (1 - lC i) * VC i = Vp p Fr (r + 2 * i.1 + 1) - lC i * Vp p Fr c.1
  colN : ∀ i, pC i = none → VC i = Vp p Fr (r + 2 * i.1 + 1)
  lR_mem : ∀ i, lR i ∈ LocRing p
  lC_mem : ∀ i, lC i ∈ LocRing p

/-- The effective levels of the full hybrid. -/
noncomputable def hfVr (p : ℕ) (Fr : Frame) (VR : Fin m → ℚ) : Fin r ⊕ Fin m → ℚ :=
  Sum.elim (fun c => Vp p Fr c.1) VR

variable {r m}
variable {pR pC : Fin m → Option (Fin r)} {lR lC : Fin m → ℚ} {VR VC : Fin m → ℚ}

theorem hyb_GOK (h : HybPiv r m p Fr pR pC lR lC VR VC) :
    GOK p Fr (hfData r m pR pC lR lC) (hfVr r m p Fr VR) (hfVr r m p Fr VC) where
  hden := h.hden
  h5 := h.h5
  hnorm := h.hnorm
  small_r u := by
    rcases u with c | i
    · have := c.2; have := h.hN; simp [hfData]; omega
    · have := i.2; have := h.hN; simp [hfData]; omega
  small_c u := by
    rcases u with c | i
    · have := c.2; have := h.hN; simp [hfData]; omega
    · have := i.2; have := h.hN; simp [hfData]; omega
  isC_node u hu := by
    rcases u with c | i
    · rfl
    · simp [hfData] at hu
  rowPiv x a hx := by
    rcases x with c | i
    · simp [hfData] at hx
    · simp only [hfData, Sum.elim_inr] at hx
      rcases hpi : pR i with _ | c
      · rw [hpi] at hx; simp at hx
      · rw [hpi] at hx
        simp only [Option.map_some, Option.some.injEq] at hx
        subst hx
        obtain ⟨j, hj0, hj, hrel, -⟩ := h.rowP i c hpi
        exact ⟨rfl, rfl, j, hj0, hj, hrel⟩
  colPiv x a hx := by
    rcases x with c | i
    · simp [hfData] at hx
    · simp only [hfData, Sum.elim_inr] at hx
      rcases hpi : pC i with _ | c
      · rw [hpi] at hx; simp at hx
      · rw [hpi] at hx
        simp only [Option.map_some, Option.some.injEq] at hx
        subst hx
        obtain ⟨j, hj0, hj, hrel, -⟩ := h.colP i c hpi
        exact ⟨rfl, rfl, j, hj0, hj, hrel⟩
  lr_mem x := by
    rcases x with c | i
    · exact (LocRing p).zero_mem
    · exact h.lR_mem i
  lc_mem x := by
    rcases x with c | i
    · exact (LocRing p).zero_mem
    · exact h.lC_mem i
  Vr_spec x := by
    rcases x with c | i
    · simp [hfVr, hfData, GData.rr, GData.aR]
    · rcases hpi : pR i with _ | c
      · have e1 : (hfData r m pR pC lR lC).rr (Sum.inr i) = 0 := by simp [GData.rr, hfData, hpi]
        rw [e1]
        simp [hfVr, hfData, h.rowN i hpi]
      · obtain ⟨j, hj0, hj, hrel, hV⟩ := h.rowP i c hpi
        have e1 : (hfData r m pR pC lR lC).rr (Sum.inr i) = lR i := by simp [GData.rr, hfData, hpi]
        have e2 : (hfData r m pR pC lR lC).aR (Sum.inr i) = Sum.inl c := by simp [GData.aR, hfData, hpi]
        rw [e1, e2]
        simpa [hfVr, hfData] using hV
  Vc_spec x := by
    rcases x with c | i
    · simp [hfVr, hfData, GData.cc, GData.aC]
    · rcases hpi : pC i with _ | c
      · have e1 : (hfData r m pR pC lR lC).cc (Sum.inr i) = 0 := by simp [GData.cc, hfData, hpi]
        rw [e1]
        simp [hfVr, hfData, h.colN i hpi]
      · obtain ⟨j, hj0, hj, hrel, hV⟩ := h.colP i c hpi
        have e1 : (hfData r m pR pC lR lC).cc (Sum.inr i) = lC i := by simp [GData.cc, hfData, hpi]
        have e2 : (hfData r m pR pC lR lC).aC (Sum.inr i) = Sum.inl c := by simp [GData.aC, hfData, hpi]
        rw [e1, e2]
        simpa [hfVr, hfData] using hV

theorem pivR_inj (h : HybPiv r m p Fr pR pC lR lC VR VC) {i i' : Fin m} {c : Fin r} (hi : pR i = some c)
    (hi' : pR i' = some c) : i = i' := by
  obtain ⟨j, hj0, hj, -⟩ := h.rowP i c hi
  obtain ⟨j', hj0', hj', -⟩ := h.rowP i' c hi'
  have hm := h.hm
  have hi2 := i.2
  have hi2' := i'.2
  have hjj : j = j' := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have : (j + 1) * p ≤ j' * p := Nat.mul_le_mul_right p hlt
      rw [Nat.succ_mul] at this
      omega
    · have : (j' + 1) * p ≤ j * p := Nat.mul_le_mul_right p hlt
      rw [Nat.succ_mul] at this
      omega
  subst hjj
  exact Fin.ext (by omega)

theorem pivC_inj (h : HybPiv r m p Fr pR pC lR lC VR VC) {i i' : Fin m} {c : Fin r} (hi : pC i = some c)
    (hi' : pC i' = some c) : i = i' := by
  obtain ⟨j, hj0, hj, -⟩ := h.colP i c hi
  obtain ⟨j', hj0', hj', -⟩ := h.colP i' c hi'
  have hm := h.hm
  have hi2 := i.2
  have hi2' := i'.2
  have hjj : j = j' := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have : (j + 1) * p ≤ j' * p := Nat.mul_le_mul_right p hlt
      rw [Nat.succ_mul] at this
      omega
    · have : (j' + 1) * p ≤ j * p := Nat.mul_le_mul_right p hlt
      rw [Nat.succ_mul] at this
      omega
  subst hjj
  exact Fin.ext (by omega)

theorem ment_restrict_eq (s : Finset (Fin r)) :
    Ment Fr ((hfData r m pR pC lR lC).restrict (memEmb r m s)) =
      FullN Fr (fun a : s => (a.1 : ℕ)) (fun i : Fin m => r + 2 * (i : ℕ))
        (fun i : Fin m => r + 2 * (i : ℕ) + 1) (X : ℚ[X]) := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Ment, GData.restrict, hfData, memEmb, FullN, Blk, blkA, blkB, blkC, blkD, Matrix.fromBlocks,
      Matrix.one_apply, Polynomial.algebraMap_eq]

theorem sum_emb_le (s : Finset (Fin r)) (f : Fin r ⊕ Fin m → ℚ) (hf : ∀ x, 0 ≤ f x) :
    ∑ x : ↥s ⊕ Fin m, f (memEmb r m s x) ≤ ∑ x : Fin r ⊕ Fin m, f x := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  have h1 : ∑ c : ↥s, f (memEmb r m s (Sum.inl c)) = ∑ c ∈ s, f (Sum.inl c) :=
    Finset.sum_coe_sort s (fun c => f (Sum.inl c))
  have h2 : ∑ c ∈ s, f (Sum.inl c) ≤ ∑ c : Fin r, f (Sum.inl c) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s) (fun c _ _ => hf _)
  have h3 : ∑ i : Fin m, f (memEmb r m s (Sum.inr i)) = ∑ i : Fin m, f (Sum.inr i) := rfl
  linarith

theorem revR_inl (s : Finset (Fin r)) (c : ↥s) :
    revR (hfData r m pR pC lR lC) (memEmb r m s) (Sum.inl c) = 0 := by
  unfold revR
  have : (hfData r m pR pC lR lC).π (memEmb r m s (Sum.inl c)) = none := rfl
  rw [this]
  simp

theorem revC_inl (s : Finset (Fin r)) (c : ↥s) :
    revC (hfData r m pR pC lR lC) (memEmb r m s) (Sum.inl c) = 0 := by
  unfold revC
  have : (hfData r m pR pC lR lC).π' (memEmb r m s (Sum.inl c)) = none := rfl
  rw [this]
  simp

theorem revR_inr_le (s : Finset (Fin r)) (i : Fin m) :
    revR (hfData r m pR pC lR lC) (memEmb r m s) (Sum.inr i) ≤
      (open Classical in if ∃ c, pR i = some c ∧ c ∉ s then 1 else 0) := by
  classical
  unfold revR
  rcases hpc : pR i with _ | c
  · have : (hfData r m pR pC lR lC).π (memEmb r m s (Sum.inr i)) = none := by simp [hfData, memEmb, hpc]
    rw [this]
    simp
  · by_cases hcs : c ∈ s
    · have hπ : (hfData r m pR pC lR lC).π (memEmb r m s (Sum.inr i)) =
          some (memEmb r m s (Sum.inl ⟨c, hcs⟩)) := by simp [hfData, memEmb, hpc]
      have := restrict_π_of (memEmb_inj r m s) hπ
      rw [this]
      simp
    · have hq : ∃ c', some c = some c' ∧ c' ∉ s := ⟨c, rfl, hcs⟩
      simp only [hq, if_true]
      split_ifs <;> omega

theorem revC_inr_le (s : Finset (Fin r)) (i : Fin m) :
    revC (hfData r m pR pC lR lC) (memEmb r m s) (Sum.inr i) ≤
      (open Classical in if ∃ c, pC i = some c ∧ c ∉ s then 1 else 0) := by
  classical
  unfold revC
  rcases hpc : pC i with _ | c
  · have : (hfData r m pR pC lR lC).π' (memEmb r m s (Sum.inr i)) = none := by simp [hfData, memEmb, hpc]
    rw [this]
    simp
  · by_cases hcs : c ∈ s
    · have hπ : (hfData r m pR pC lR lC).π' (memEmb r m s (Sum.inr i)) =
          some (memEmb r m s (Sum.inl ⟨c, hcs⟩)) := by simp [hfData, memEmb, hpc]
      have := restrict_π'_of (memEmb_inj r m s) hπ
      rw [this]
      simp
    · have hq : ∃ c', some c = some c' ∧ c' ∉ s := ⟨c, rfl, hcs⟩
      simp only [hq, if_true]
      split_ifs <;> omega

theorem card_T_le (h : HybPiv r m p Fr pR pC lR lC VR VC) (s : Finset (Fin r)) :
    (open Classical in (Finset.univ.filter (fun i : Fin m => ∃ c, pR i = some c ∧ c ∉ s)).card) ≤ r - s.card := by
  classical
  have hT : (Finset.univ.filter (fun i : Fin m => ∃ c, pR i = some c ∧ c ∉ s)).card ≤
      (sᶜ.map ⟨some, Option.some_injective (Fin r)⟩).card := by
    refine Finset.card_le_card_of_injOn pR ?_ ?_
    · intro i hi
      obtain ⟨c, hc, hcs⟩ := (Finset.mem_filter.1 hi).2
      rw [hc]
      exact Finset.mem_coe.2 (Finset.mem_map.2 ⟨c, Finset.mem_compl.2 hcs, rfl⟩)
    · intro i hi i' hi' hpp
      obtain ⟨c, hc, -⟩ := (Finset.mem_filter.1 hi).2
      exact pivR_inj h hc (hpp ▸ hc)
  rw [Finset.card_map, Finset.card_compl, Fintype.card_fin] at hT
  exact hT

theorem card_TC_le (h : HybPiv r m p Fr pR pC lR lC VR VC) (s : Finset (Fin r)) :
    (open Classical in (Finset.univ.filter (fun i : Fin m => ∃ c, pC i = some c ∧ c ∉ s)).card) ≤ r - s.card := by
  classical
  have hT : (Finset.univ.filter (fun i : Fin m => ∃ c, pC i = some c ∧ c ∉ s)).card ≤
      (sᶜ.map ⟨some, Option.some_injective (Fin r)⟩).card := by
    refine Finset.card_le_card_of_injOn pC ?_ ?_
    · intro i hi
      obtain ⟨c, hc, hcs⟩ := (Finset.mem_filter.1 hi).2
      rw [hc]
      exact Finset.mem_coe.2 (Finset.mem_map.2 ⟨c, Finset.mem_compl.2 hcs, rfl⟩)
    · intro i hi i' hi' hpp
      obtain ⟨c, hc, -⟩ := (Finset.mem_filter.1 hi).2
      exact pivC_inj h hc (hpp ▸ hc)
  rw [Finset.card_map, Finset.card_compl, Fintype.card_fin] at hT
  exact hT

theorem rev_sum_le (h : HybPiv r m p Fr pR pC lR lC VR VC) (s : Finset (Fin r)) :
    ∑ x : ↥s ⊕ Fin m, revR (hfData r m pR pC lR lC) (memEmb r m s) x +
      ∑ x : ↥s ⊕ Fin m, revC (hfData r m pR pC lR lC) (memEmb r m s) x ≤ 2 * (r - s.card) := by
  classical
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [revR_inl, revC_inl, Finset.sum_const_zero, zero_add]
  have h1 : ∑ i : Fin m, revR (hfData r m pR pC lR lC) (memEmb r m s) (Sum.inr i) ≤
      (Finset.univ.filter (fun i : Fin m => ∃ c, pR i = some c ∧ c ∉ s)).card := by
    rw [Finset.card_filter]
    exact Finset.sum_le_sum fun i _ => revR_inr_le s i
  have h2 : ∑ i : Fin m, revC (hfData r m pR pC lR lC) (memEmb r m s) (Sum.inr i) ≤
      (Finset.univ.filter (fun i : Fin m => ∃ c, pC i = some c ∧ c ∉ s)).card := by
    rw [Finset.card_filter]
    exact Finset.sum_le_sum fun i _ => revC_inr_le s i
  have h3 := card_T_le h s
  have h4 := card_TC_le h s
  omega

/-- **The dip price of a member.**  A dual `ρ x + γ y ≥ Wd x y` of the full hybrid (every common node retained,
every pivot present) prices every member `commonMinorPoly Fr r m s`, with two extra units per deleted common node. -/
theorem member_gle (h : HybPiv r m p Fr pR pC lR lC VR VC) (s : Finset (Fin r))
    (ρ γ : Fin r ⊕ Fin m → ℚ) (hρ : ∀ x, 0 ≤ ρ x) (hγ : ∀ x, 0 ≤ γ x)
    (hfeas : ∀ x y, ((Wd p Fr (hfData r m pR pC lR lC) (hfVr r m p Fr VR) (hfVr r m p Fr VC) x y : ℕ) : ℚ) ≤
      ρ x + γ y) {B : ℕ} (hB : ∑ x, ρ x + ∑ y, γ y + 2 * ((r - s.card : ℕ) : ℚ) ≤ B) :
    GLE p B (commonMinorPoly Fr r m s) := by
  letI := memLO r m s
  rw [commonMinorPoly, ← ment_restrict_eq (pR := pR) (pC := pC) (lR := lR) (lC := lC) s]
  refine restrict_gle (hyb_GOK h) (memEmb_inj r m s) ?_ ?_ ρ γ hfeas ?_
  · intro x b hxb
    have h1 := restrict_π_some (memEmb_inj r m s) hxb
    rcases x with c | i
    · simp [hfData, memEmb] at h1
    · rcases hpi : pR i with _ | c
      · simp [hfData, memEmb, hpi] at h1
      · rcases b with b | b
        · show memKey r m s (Sum.inl b) < memKey r m s (Sum.inr i)
          simp [memKey]
          have := b.1.2
          omega
        · simp [hfData, memEmb, hpi] at h1
  · intro x b hxb
    have h1 := restrict_π'_some (memEmb_inj r m s) hxb
    rcases x with c | i
    · simp [hfData, memEmb] at h1
    · rcases hpi : pC i with _ | c
      · simp [hfData, memEmb, hpi] at h1
      · rcases b with b | b
        · show memKey r m s (Sum.inl b) < memKey r m s (Sum.inr i)
          simp [memKey]
          have := b.1.2
          omega
        · simp [hfData, memEmb, hpi] at h1
  have h1 := sum_emb_le (m := m) s ρ hρ
  have h2 := sum_emb_le (m := m) s γ hγ
  have h3 : ((∑ x : ↥s ⊕ Fin m, revR (hfData r m pR pC lR lC) (memEmb r m s) x +
      ∑ x : ↥s ⊕ Fin m, revC (hfData r m pR pC lR lC) (memEmb r m s) x : ℕ) : ℚ) ≤ 2 * ((r - s.card : ℕ) : ℚ) := by
    exact_mod_cast rev_sum_le h s
  linarith

end Hybrid

end CatalanCore.Uniform.Bank.Plane1.Dips

#print axioms CatalanCore.Uniform.Bank.Plane1.Dips.restrict_GOK
#print axioms CatalanCore.Uniform.Bank.Plane1.Dips.Wd_restrict_le
#print axioms CatalanCore.Uniform.Bank.Plane1.Dips.restrict_gle
#print axioms CatalanCore.Uniform.Bank.Plane1.Dips.hyb_GOK
#print axioms CatalanCore.Uniform.Bank.Plane1.Dips.member_gle
