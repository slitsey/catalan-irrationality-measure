module

public import CatalanFrames.Lambda.HybDefC5Lam
public import CatalanFrames.Lambda.HybContent2C
public import CatalanFrames.Lambda.HybTopE
public import CatalanCore.Arith.Hybrid.BorderB
public import CatalanCore.Arith.Hybrid.BorderC5
public import CatalanFrames.Lambda.HybTopSum
public import CatalanFrames.LambdaHybrid.Assembly
public import CatalanCore.Rect.PairBridgeTop

@[expose] public section

/-!
# λ: the bordered deficit family and `Mem2Content` (MEM2C)

`lam_defBoth_all2`: the family `B + E (both classes) + C5` of `lam_defHypT_all2`, simultaneously
as `DefHypT` (member 1) and `DefHypTop` (member 2, the bordered twin), with the same `δ`.
`lam_mem2Content`: `Mem2Content lamFrame Λ` for `Λ ≥ 24729491161/6665218560`.
-/

open Finset Filter CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanCore.Rect

namespace CatalanFrames.Lambda

/-- Member-1 and member-2 deficit hypotheses together. -/
def DefBoth (r : ℕ) (T δ : ℕ → ℕ) : Prop :=
  DefHypT lamInst r (r / 8) T δ ∧ DefHypTop lamInst r (r / 8) T δ

lemma DefBoth.mono_T {r : ℕ} {T T' δ : ℕ → ℕ} (h : DefBoth r T δ)
    (hle : ∀ p, p.Prime → p < Bnd lamInst r (r / 8) → T p ≤ T' p) : DefBoth r T' δ :=
  ⟨h.1.mono_T hle, h.2.mono_T hle⟩

lemma DefBoth.add {r : ℕ} {T δ₁ δ₂ : ℕ → ℕ} (h1 : DefBoth r T δ₁) (h2 : DefBoth r T δ₂)
    (hdisj : ∀ p, p.Prime → p < Bnd lamInst r (r / 8) → δ₁ p = 0 ∨ δ₂ p = 0) :
    DefBoth r T (fun p => δ₁ p + δ₂ p) :=
  ⟨defHypT_add h1.1 h2.1 hdisj, h1.2.add h2.2 hdisj⟩

lemma DefBoth.glue {r : ℕ} {T δ₁ δ₂ : ℕ → ℕ} (S : ℕ → Prop) [DecidablePred S]
    (h1 : DefBoth r T δ₁) (h2 : DefBoth r T δ₂) :
    DefBoth r T (fun p => if S p then δ₂ p else δ₁ p) :=
  ⟨h1.1.glue S h2.1, h1.2.glue S h2.2⟩

/-- **B, E (class 1), E (class 3) as a single `DefBoth` family.** -/
theorem lam_defBoth_all {r : ℕ} (hr : 16 ≤ r) :
    ∃ δ : ℕ → ℕ, DefBoth r (Tfun r) δ ∧
      (∀ p, cleanE1 r p → δ p = r / 8) ∧ (∀ p, cleanE3 r p → δ p = r / 8) ∧
      (∀ p, WB r p → δ p = r / 8 - (p - r)) := by
  classical
  set T : ℕ → ℕ := Tfun r with hT
  have hT1 : ∀ p, p.Prime → p < Bnd lamInst r (r / 8) → tropExp lamInst r (r / 8) p ≤ T p :=
    fun p _ _ => le_max_left _ _
  have hd1 : ∀ p, cleanE1 r p → dualE1 r (r / 8) p ≤ T p := fun p hc => by
    simp only [hT, Tfun, eN]
    refine le_trans ?_ (le_max_right _ _)
    refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_left _ _)
    rw [if_pos hc]
  have hd3 : ∀ p, cleanE3 r p → 2 * r + r / 8 ≤ T p := fun p hc => by
    simp only [hT, Tfun, eN]
    refine le_trans ?_ (le_max_right _ _)
    refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_right _ _)
    rw [if_pos hc]
  have hE1 : DefBoth r T (defE1 r) := ⟨defHypT_E1 r T hT1 hd1, defHypTop_E1 r T hT1 hd1⟩
  have hE3 : DefBoth r T (defE3 r) :=
    ⟨defHypT_E3 hr T hT1 hd3, defHypTop_E3 hr T hT1 hd3⟩
  have hBd : ∀ p : ℕ, p.Prime → WB r p → ∀ j k, BSetup 1 p r (r / 8) j k →
      ∑ a, uPot p r k (Frame.hybRow r (r / 8) a) + ∑ b, uPot p r k (Frame.hybCol r (r / 8) b)
        ≤ T p := fun p hp hW j k S => by
    rw [bsetup_k hW.1 S]
    simp only [hT, Tfun, eN]
    refine le_trans ?_ (le_max_right _ _)
    refine le_trans ?_ (le_max_right _ _)
    rw [if_pos hW]
    exact le_rfl
  have hB : DefBoth r T (fun p => if WB r p then r / 8 - (p - r) else 0) :=
    ⟨defHypT_B lamInst lamData r (r / 8) T (WB r) (fun p hp => hp.2.2)
      (fun p hp hW => ⟨_, _, bsetup_of hr hW.1 hW.2.1 hW.2.2⟩) hT1 hBd,
     defHypTop_B lamInst lamData r (r / 8) T (WB r) (fun p hp => hp.2.2)
      (fun p hp hW => ⟨_, _, bsetup_of hr hW.1 hW.2.1 hW.2.2⟩) hT1 hBd⟩
  have d13 : ∀ p, defE1 r p = 0 ∨ defE3 r p = 0 := by
    intro p
    by_cases hc : cleanE1 r p
    · right
      have : ¬ cleanE3 r p := fun h => by have := hc.2.1; have := h.2.1; omega
      simp [defE3, this]
    · left; simp [defE1, hc]
  refine ⟨_, DefBoth.add (DefBoth.add hE1 hE3 (fun p _ _ => d13 p)) hB ?_, ?_, ?_, ?_⟩
  · intro p hp hb
    by_cases hc : cleanE1 r p ∨ cleanE3 r p
    · right
      have : ¬ WB r p := fun hw => by
        rcases hc with hc | hc
        · have := hc.2.2.2; have := hw.2.1; omega
        · have : p < r := by have := hc.2.2.2.1; omega
          have := hw.2.1; omega
      simp [this]
    · left
      push_neg at hc
      simp [defE1, defE3, hc.1, hc.2]
  · intro p hc
    have : ¬ cleanE3 r p := fun h => by have := hc.2.1; have := h.2.1; omega
    have : ¬ WB r p := fun hw => by have := hc.2.2.2; have := hw.2.1; omega
    simp [defE1, defE3, hc, *]
  · intro p hc
    have h1 : ¬ cleanE1 r p := fun h => by have := hc.2.1; have := h.2.1; omega
    have : ¬ WB r p := fun hw => by
      have : p < r := by have := hc.2.2.2.1; omega
      have := hw.2.1; omega
    simp [defE1, defE3, hc, *]
  · intro p hW
    have h1 : ¬ cleanE1 r p := fun hc => by have := hc.2.2.2; have := hW.2.1; omega
    have h3 : ¬ cleanE3 r p := fun hc => by
      have : p < r := by have := hc.2.2.2.1; omega
      have := hW.2.1; omega
    simp [defE1, defE3, h1, h3, hW]

/-- **B, E (both classes), C5 as a single `DefBoth` family** (twin of `lam_defHypT_all2`). -/
theorem lam_defBoth_all2 {r : ℕ} (hr : 16 ≤ r) :
    ∃ δ : ℕ → ℕ, DefBoth r (Tfun2 r) δ ∧
      (∀ p, cleanE1 r p → δ p = r / 8) ∧ (∀ p, cleanE3 r p → δ p = r / 8) ∧
      (∀ p, WB r p → δ p = r / 8 - (p - r)) ∧
      (∀ p, WC5 r p → δ p = p + (p + 1) / 4 - r - r / 8) := by
  classical
  obtain ⟨δ0, h0, h1, h3, hB⟩ := lam_defBoth_all hr
  have h0' : DefBoth r (Tfun2 r) δ0 := h0.mono_T fun p _ _ => le_max_left _ _
  have hCs : ∀ p : ℕ, p.Prime → WC5 r p → ∀ k, CSetup 1 p r (r / 8) k →
      ∑ a, wC p r k (Frame.hybRow r (r / 8) a) + ∑ b, wC p r k (Frame.hybCol r (r / 8) b)
        ≤ Tfun2 r p := fun p hp hW k S => by
    have hk : k = (p + 1) / 4 := by have := S.hk; omega
    rw [wC_dual_eq S]
    refine le_trans ?_ (le_max_right _ _)
    simp only [eC5, if_pos hW, hk]
    omega
  have hC : DefBoth r (Tfun2 r) (fun p => if WC5 r p then p + (p + 1) / 4 - r - r / 8 else 0) :=
    ⟨defHypT_C5 lamInst lamData r (r / 8) (Tfun2 r) (WC5 r)
      (fun p _ hW => ⟨_, csetup_of_wc5 hr hW⟩)
      (fun p _ _ => le_trans (le_max_left _ _) (le_max_left _ _)) hCs,
     defHypTop_C5 lamInst lamData r (r / 8) (Tfun2 r) (WC5 r)
      (fun p _ hW => ⟨_, csetup_of_wc5 hr hW⟩)
      (fun p _ _ => le_trans (le_max_left _ _) (le_max_left _ _)) hCs⟩
  refine ⟨_, h0'.glue (WC5 r) hC, ?_, ?_, ?_, ?_⟩
  · intro p hc
    have : ¬ WC5 r p := fun hw => by have := hc.2.1; have := hw.2.1; omega
    simp only [if_neg this]; exact h1 p hc
  · intro p hc
    have : ¬ WC5 r p := fun hw => by have := hc.2.2.2.1; have := hw.2.2.2.2; have := hw.2.2.1; omega
    simp only [if_neg this]; exact h3 p hc
  · intro p hW
    have : ¬ WC5 r p := fun hw => by have := hW.2.1; have := hw.2.2.2.2; omega
    simp only [if_neg this]; exact hB p hW
  · intro p hW
    simp only [if_pos hW]

theorem lam_content_deficit2_gen {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ δ : ℕ → ℕ, DefHypT lamInst r (r / 8) (Tfun2 r) δ →
      (∀ p, cleanE1 r p → δ p = r / 8) → (∀ p, cleanE3 r p → δ p = r / 8) →
      (∀ p, WB r p → δ p = r / 8 - (p - r)) →
      (∀ p, WC5 r p → δ p = p + (p + 1) / 4 - r - r / 8) →
      Real.log (DhybT lamInst r (r / 8) (Tfun2 r) δ) ≤
        (24994314577 / 6665218560 + ε) * (r : ℝ) ^ 2 -
        ((r / 8 : ℕ) : ℝ) * (((1 / 7 : ℝ) - ε) * r - 4 * Real.log r) -
        ((r / 8 : ℕ) : ℝ) * (((7 / 80 : ℝ) - ε) * r - 6 * Real.log r) -
        (1 / 128 - ε) * (r : ℝ) ^ 2 - (1 / 320 - ε) * (r : ℝ) ^ 2 := by
  have h3 := class3_totalT2 (ε := ε / 4) (by positivity)
  have h1 := class1_totalT2 (ε := ε / 4) (by positivity)
  have hx := extra_small (ε / 2) (by positivity)
  have hE1 := lam_E1_deficit_sum hε
  have hE3 := lam_E3_deficit_sum hε
  have hBs := lam_B_deficit_sum hε
  have hCs := lam_C5_deficit_sum hε
  filter_upwards [h3, h1, hx, hE1, hE3, hBs, hCs, eventually_ge_atTop 16] with r hr3 hr1 hrx hD1 hD3
    hDB hDC hr16
  intro δ hδ hδ1 hδ3 hδB hδC
  have hmain := lam_log_DhybT_le2 hr16 hδ
  have hex := hrx (r / 8) (Nat.div_le_self r 8)
  have hc := lam_const8
  have e : (r : ℝ) ^ 2 * (((9 / 4 : ℝ) * (1 / 68) + listInt l3x) / 2 + ε / 4) +
      (r : ℝ) ^ 2 * (((9 / 4 : ℝ) * (1 / 68) + listInt l1x) / 2 + ε / 4) =
      (r : ℝ) ^ 2 * (24994314577 / 6665218560 + ε / 2) := by
    rw [← mul_add]
    congr 1
    linarith
  have hlogp : ∀ p ∈ (Finset.range (Bnd lamInst r (r / 8))).filter Nat.Prime,
      0 ≤ Real.log p := fun p hp =>
    Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt.le)
  have key := defSum_ge (Finset.univ : Finset (Fin 4))
    ((Finset.range (Bnd lamInst r (r / 8))).filter Nat.Prime) δ
    (fun i => ![defE1 r, defE3 r, defB r, defC5 r] i)
    (fun i => ![((r / 8 : ℕ) : ℝ) * (((1 / 7 : ℝ) - ε) * r - 4 * Real.log r),
      ((r / 8 : ℕ) : ℝ) * (((7 / 80 : ℝ) - ε) * r - 6 * Real.log r),
      (1 / 128 - ε) * (r : ℝ) ^ 2, (1 / 320 - ε) * (r : ℝ) ^ 2] i)
    (fun p _ => by
      simpa [Fin.sum_univ_four] using defs_le_delta hδ1 hδ3 hδB hδC p)
    (fun i _ => by
      fin_cases i
      · exact hD1
      · exact hD3
      · exact hDB
      · exact hDC)
    hlogp
  simp only [Fin.sum_univ_four] at key
  simp at key
  nlinarith [hmain, hr3, hr1, hrx, e, hD1, hD3, key]


end CatalanFrames.Lambda

namespace CatalanFrames.LambdaHybrid

open CatalanFrames.Lambda

/-- **Generic bordering step**: a content bound for a family that is simultaneously a
member-1 and member-2 deficit family (`DefBoth`) gives `Mem2Content`, because the border cost
is `O(r log r)` (`lam_topC_sum`).  Any later deficit family (e.g. with GK bordered) plugs in here. -/
theorem lam_mem2Content_of_both {Λ0 Λ : ℝ} (hΛ : Λ0 ≤ Λ)
    (h : ∀ ε > 0, ∀ᶠ r : ℕ in atTop, ∃ T δ : ℕ → ℕ, DefBoth r T δ ∧
      Real.log (DhybT lamInst r (r / 8) T δ) ≤ (Λ0 + ε) * (r : ℝ) ^ 2) :
    Mem2Content lamFrame Λ := by
  refine mem2Content_of_top lamInst ?_
  intro ε hε
  filter_upwards [h (ε / 2) (by positivity), lam_topC_sum (ε := ε / 2) (by positivity)] with r
    ⟨T, δ, hδ, hlog⟩ hS
  refine ⟨T, δ, hδ.2, ?_⟩
  rw [log_DhybTop lamInst r (r / 8) hδ.1]
  nlinarith [hlog, hS, mul_le_mul_of_nonneg_right hΛ (sq_nonneg (r : ℝ))]

/-- The `ε`-form of the member-1/member-2 content bound for the deficit family `B, E, C5`. -/
theorem lam_both_eps {Λ : ℝ} (hΛ : 24729491161 / 6665218560 ≤ Λ) :
    ∀ ε > 0, ∀ᶠ r : ℕ in atTop, ∃ T δ : ℕ → ℕ, DefBoth r T δ ∧
      Real.log (DhybT lamInst r (r / 8) T δ) ≤ (Λ + ε) * (r : ℝ) ^ 2 := by
  intro ε hε
  set ε₁ : ℝ := min ε (1 / 100) with hε₁
  have hε₁0 : 0 < ε₁ := lt_min hε (by norm_num)
  have hε₁1 : ε₁ ≤ 1 / 100 := min_le_right _ _
  have hε₁2 : ε₁ ≤ ε := min_le_left _ _
  have hd := lam_content_deficit2_gen (ε := ε₁ / 10) (by positivity)
  have hl := eventually_log_le (e := ε₁ / 10) (by positivity)
  have hbig : ∀ᶠ r : ℕ in atTop, 3 ≤ ε₁ * r := by
    have : Tendsto (fun r : ℕ => ε₁ * (r : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop hε₁0
    exact this.eventually_ge_atTop 3
  filter_upwards [hd, hl, hbig, eventually_ge_atTop 16] with r hdr hL hb hr16
  obtain ⟨δ, hδ, hδ1, hδ3, hδB, hδC⟩ := lam_defBoth_all2 hr16
  refine ⟨Tfun2 r, δ, hδ, ?_⟩
  have hlog := hdr δ hδ.1 hδ1 hδ3 hδB hδC
  have hm : (r : ℝ) / 8 - 1 ≤ ((r / 8 : ℕ) : ℝ) := by
    have : (r : ℝ) < 8 * ((r / 8 : ℕ) : ℝ) + 8 := by
      exact_mod_cast (by omega : r < 8 * (r / 8) + 8)
    linarith
  have hL0 : 0 ≤ Real.log r := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ r))
  have key := lam_num (Λ := Λ + (ε - ε₁)) (ε := ε₁) (r := (r : ℝ)) (L := Real.log r)
    (m := ((r / 8 : ℕ) : ℝ)) (lg := Real.log (DhybT lamInst r (r / 8) (Tfun2 r) δ))
    (by linarith) hε₁0 hε₁1 hb hL0 hL hm hlog
  have : (Λ + (ε - ε₁) + ε₁) = Λ + ε := by ring
  rwa [this] at key

/-- **`Mem2Content` for λ** (bordering of the member-1 deficit families B, E, C5). -/
theorem lam_mem2Content {Λ : ℝ} (hΛ : 24729491161 / 6665218560 ≤ Λ) :
    Mem2Content lamFrame Λ :=
  lam_mem2Content_of_both le_rfl (lam_both_eps hΛ)

end CatalanFrames.LambdaHybrid
