module

public import CatalanCore.Zeta5.Sum.Final
public import CatalanCore.Zeta5.Sum.PrimeProfile

@[expose] public section

/-!
# ZC32, prime sums of the profiles on arbitrary intervals

`psum H a b R = R⁻² Σ_{R/b < p ≤ R/a} p H(R/p) log p`.

* `cell_prime_sum`: if `H` is continuous (up to its values at the cell ends) on every open
  interval of `[a, b]` free of a finite set `S` of break points, then `psum H a b R → ∫_a^b H/x³`
  (`0 < a ≤ b`). Proof: induction on the number of break points inside, one cell by ZC28
  (`weighted_prime_sum_tendsto`) and the substitution `θ = 1/x`.
* `rg_psum`, `gref_psum`: the profiles `R` and `g_ref` on any `[a, b] ⊂ (0, ∞)`; the break
  points are the lattice points `n/c` of the slopes of ZC30/ZC31 (`Rg_affine_cell`).
* `ex_psum`, `hp_psum`: the outer profiles on the cut lists of `DataOuter` (ZC34, ZC35).
-/

open Filter Set MeasureTheory
open scoped Topology

set_option linter.deprecated false

namespace CatalanCore.Zeta5.Content

open CatalanCore.Zeta5.Profile CatalanCore.Zeta5.Sum OAI.Zeta5.Workers.W14

/-- `R⁻² Σ_{R/b < p ≤ R/a} p H(R/p) log p`. -/
noncomputable def psum (H : ℝ → ℝ) (a b R : ℝ) : ℝ :=
  (∑ p ∈ Finset.Ioc ⌊R / b⌋₊ ⌊R / a⌋₊ with p.Prime, (p : ℝ) * H (R / p) * Real.log p) / R ^ 2

/-- `H` is continuous on every cell of `[a, b]` free of the points of `S`. -/
def CellCont (H : ℝ → ℝ) (S : Finset ℝ) (a b : ℝ) : Prop :=
  ∀ l r, a ≤ l → l < r → r ≤ b → (∀ s ∈ S, s ∉ Ioo l r) →
    ∃ G : ℝ → ℝ, ContinuousOn G (Icc l r) ∧ ∀ x ∈ Ioo l r, H x = G x

lemma CellCont.mono {H : ℝ → ℝ} {S : Finset ℝ} {a b a' b' : ℝ} (h : CellCont H S a b)
    (ha : a ≤ a') (hb : b' ≤ b) : CellCont H S a' b' :=
  fun l r hl hlr hr hS => h l r (ha.trans hl) hlr (hr.trans hb) hS

/-- One cell. -/
lemma one_cell_prime_sum {H G : ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hG : ContinuousOn G (Icc a b)) (hHG : ∀ x ∈ Ioo a b, H x = G x) :
    IntervalIntegrable (fun x => H x / x ^ 3) volume a b ∧
      Tendsto (psum H a b) atTop (𝓝 (∫ x in a..b, H x / x ^ 3)) := by
  have hb : 0 < b := ha.trans hab
  constructor
  · have hc : ContinuousOn (fun x => G x / x ^ 3) (Icc a b) := by
      apply hG.div (continuousOn_pow 3)
      intro x hx
      have : 0 < x := lt_of_lt_of_le ha hx.1
      positivity
    have hGi : IntervalIntegrable (fun x => G x / x ^ 3) volume a b :=
      (hc.mono (by rw [Set.uIcc_of_le hab.le])).intervalIntegrable
    refine hGi.congr_uIoo ?_
    intro x hx
    rw [Set.uIoo_of_le hab.le] at hx
    simp only [hHG x hx]
  · set c : ℕ → ℝ := fun i => if i = 0 then 1 / b else 1 / a with hc
    have hc0 : c 0 = 1 / b := by simp [hc]
    have hc1 : c 1 = 1 / a := by simp [hc]
    have hlt : 1 / b < 1 / a := one_div_lt_one_div_of_lt ha hab
    have hpc : PiecewiseCont (fun θ => θ * H (1 / θ)) c 1 := by
      refine ⟨fun i hi => ?_, fun i hi => ?_⟩
      · have : i = 0 := by omega
        subst this; rw [hc0, hc1]; exact hlt
      · have : i = 0 := by omega
        subst this
        rw [hc0, show (0 + 1 : ℕ) = 1 from rfl, hc1]
        refine ⟨fun θ => θ * G (1 / θ), ?_, ?_⟩
        · apply ContinuousOn.mul continuousOn_id
          refine hG.comp (f := fun θ : ℝ => 1 / θ) ?_ ?_
          · apply ContinuousOn.div continuousOn_const continuousOn_id
            intro θ hθ
            have : 0 < θ := lt_of_lt_of_le (by positivity) hθ.1
            exact this.ne'
          · intro θ hθ
            have hθ0 : 0 < θ := lt_of_lt_of_le (by positivity) hθ.1
            constructor
            · rw [le_div_iff₀ hθ0]
              have := hθ.2
              rw [le_div_iff₀ ha] at this
              linarith
            · rw [div_le_iff₀ hθ0]
              have := hθ.1
              rw [div_le_iff₀ hb] at this
              linarith
        · intro θ hθ
          have hθ0 : 0 < θ := lt_trans (by positivity) hθ.1
          have hx : 1 / θ ∈ Ioo a b := by
            constructor
            · rw [lt_div_iff₀ hθ0]
              have := hθ.2
              rw [lt_div_iff₀ ha] at this
              linarith
            · rw [div_lt_iff₀ hθ0]
              have := hθ.1
              rw [div_lt_iff₀ hb] at this
              linarith
          simp only [hHG _ hx]
    have hc0' : 0 < c 0 := by rw [hc0]; positivity
    have hT := (weighted_prime_sum_tendsto hc0' hpc).2
    rw [hc0, hc1] at hT
    have hint : (∫ θ in (1 / b)..(1 / a), θ * H (1 / θ)) = ∫ x in a..b, H x / x ^ 3 := by
      rw [← integral_inv_comp (fun θ => θ * H (1 / θ)) ha hab.le]
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hab.le] at hx
      have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
      simp only [one_div, inv_inv]
      field_simp
    rw [hint] at hT
    refine hT.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    unfold weightedPrimeIntervalSum psum
    have e1 : (1 / b) * R = R / b := by ring
    have e2 : (1 / a) * R = R / a := by ring
    rw [e1, e2, Finset.sum_div, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro p hp
    have : 1 / ((p : ℝ) / R) = R / p := one_div_div _ _
    simp only [this]
    field_simp

/-- Splitting the prime sum at an interior point. -/
lemma psum_split (H : ℝ → ℝ) {a s b R : ℝ} (ha : 0 < a) (has : a ≤ s) (hsb : s ≤ b) (hR : 0 ≤ R) :
    psum H a b R = psum H a s R + psum H s b R := by
  unfold psum
  rw [← add_div]
  congr 1
  have hs : 0 < s := lt_of_lt_of_le ha has
  have hb : 0 < b := lt_of_lt_of_le hs hsb
  have h1 : ⌊R / b⌋₊ ≤ ⌊R / s⌋₊ := Nat.floor_le_floor (div_le_div_of_nonneg_left hR hs hsb)
  have h2 : ⌊R / s⌋₊ ≤ ⌊R / a⌋₊ := Nat.floor_le_floor (div_le_div_of_nonneg_left hR ha has)
  simp only [Finset.sum_filter]
  rw [← Finset.sum_Ioc_consecutive _ h1 h2, add_comm]

/-- **ZC32, prime sums on cells.** -/
theorem cell_prime_sum {H : ℝ → ℝ} (S : Finset ℝ) :
    ∀ (N : ℕ) (a b : ℝ), (S.filter (fun s => a < s ∧ s < b)).card ≤ N → 0 < a → a ≤ b →
      CellCont H S a b →
      IntervalIntegrable (fun x => H x / x ^ 3) volume a b ∧
        Tendsto (psum H a b) atTop (𝓝 (∫ x in a..b, H x / x ^ 3)) := by
  intro N
  induction N with
  | zero =>
    intro a b hN ha hab hH
    rcases hab.eq_or_lt with heq | hlt
    · subst heq
      refine ⟨IntervalIntegrable.refl, ?_⟩
      simp only [intervalIntegral.integral_same]
      have : psum H a a = fun _ => 0 := by
        funext R; simp [psum]
      rw [this]; exact tendsto_const_nhds
    · have hS : ∀ s ∈ S, s ∉ Ioo a b := by
        intro s hs hs'
        have : s ∈ S.filter (fun s => a < s ∧ s < b) := Finset.mem_filter.mpr ⟨hs, hs'⟩
        have := Finset.card_pos.mpr ⟨s, this⟩
        omega
      obtain ⟨G, hG, hHG⟩ := hH a b le_rfl hlt le_rfl hS
      exact one_cell_prime_sum ha hlt hG hHG
  | succ N ih =>
    intro a b hN ha hab hH
    by_cases hex : ∃ s ∈ S, a < s ∧ s < b
    · obtain ⟨s, hsS, has, hsb⟩ := hex
      have hsf : s ∈ S.filter (fun s => a < s ∧ s < b) := Finset.mem_filter.mpr ⟨hsS, has, hsb⟩
      have hc1 : (S.filter (fun t => a < t ∧ t < s)).card ≤ N := by
        have hss : S.filter (fun t => a < t ∧ t < s) ⊂ S.filter (fun t => a < t ∧ t < b) := by
          refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
          · intro t ht
            rw [Finset.mem_filter] at ht ⊢
            exact ⟨ht.1, ht.2.1, ht.2.2.trans hsb⟩
          · intro heq
            rw [← heq, Finset.mem_filter] at hsf
            exact lt_irrefl s hsf.2.2
        have := Finset.card_lt_card hss
        omega
      have hc2 : (S.filter (fun t => s < t ∧ t < b)).card ≤ N := by
        have hss : S.filter (fun t => s < t ∧ t < b) ⊂ S.filter (fun t => a < t ∧ t < b) := by
          refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
          · intro t ht
            rw [Finset.mem_filter] at ht ⊢
            exact ⟨ht.1, has.trans ht.2.1, ht.2.2⟩
          · intro heq
            rw [← heq, Finset.mem_filter] at hsf
            exact lt_irrefl s hsf.2.1
        have := Finset.card_lt_card hss
        omega
      obtain ⟨I1, T1⟩ := ih a s hc1 ha has.le (hH.mono le_rfl hsb.le)
      obtain ⟨I2, T2⟩ := ih s b hc2 (ha.trans has) hsb.le (hH.mono has.le le_rfl)
      refine ⟨I1.trans I2, ?_⟩
      rw [← intervalIntegral.integral_add_adjacent_intervals I1 I2]
      refine (T1.add T2).congr' ?_
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
      exact (psum_split H ha has.le hsb.le hR).symm
    · push Not at hex
      rcases hab.eq_or_lt with heq | hlt
      · subst heq
        refine ⟨IntervalIntegrable.refl, ?_⟩
        simp only [intervalIntegral.integral_same]
        have : psum H a a = fun _ => 0 := by
          funext R; simp [psum]
        rw [this]; exact tendsto_const_nhds
      · have hS : ∀ s ∈ S, s ∉ Ioo a b := fun s hs hs' => absurd (hex s hs hs'.1) (not_le.mpr hs'.2)
        obtain ⟨G, hG, hHG⟩ := hH a b le_rfl hlt le_rfl hS
        exact one_cell_prime_sum ha hlt hG hHG

/-- The lattice points `n/c` in `[a, b]`. -/
noncomputable def latPts (c a b : ℝ) : Finset ℝ :=
  (Finset.Icc ⌈c * a⌉ ⌊c * b⌋).image (fun n : ℤ => (n : ℝ) / c)

lemma noPt_of_latPts {c a b l r : ℝ} (hc : 0 < c) (hl : a ≤ l) (hr : r ≤ b)
    (h : ∀ s ∈ latPts c a b, s ∉ Ioo l r) : NoPt c l r := by
  intro n ⟨h1, h2⟩
  apply h ((n : ℝ) / c) _ ⟨h1, h2⟩
  unfold latPts
  rw [Finset.mem_image]
  refine ⟨n, ?_, rfl⟩
  rw [Finset.mem_Icc]
  have h1' : c * a < n := by
    have := lt_of_le_of_lt hl h1
    rw [lt_div_iff₀ hc] at this; linarith
  have h2' : (n : ℝ) < c * b := by
    have := lt_of_lt_of_le h2 hr
    rw [div_lt_iff₀ hc] at this; linarith
  exact ⟨Int.ceil_le.mpr h1'.le, Int.le_floor.mpr h2'.le⟩

/-- The break points of `R` in `[a, b]` (slopes of ZC30). -/
noncomputable def ptsR (a b : ℝ) : Finset ℝ :=
  latPts 2 a b ∪ latPts (37 / 20) a b ∪ latPts (23 / 10) a b ∪ latPts (43 / 40) a b ∪
    latPts (3 / 10) a b

theorem cellCont_Rg (a b : ℝ) : CellCont (Rg : ℝ → ℝ) (ptsR a b) a b := by
  intro l r hl hlr hr hS
  have hS' : ∀ c, latPts c a b ⊆ ptsR a b → ∀ s ∈ latPts c a b, s ∉ Ioo l r :=
    fun c hsub s hs => hS s (hsub hs)
  have h2 := noPt_of_latPts (by norm_num) hl hr (hS' 2 (by unfold ptsR; intro x hx; simp [hx]))
  have h3 := noPt_of_latPts (by norm_num) hl hr (hS' (37 / 20) (by unfold ptsR; intro x hx; simp [hx]))
  have h4 := noPt_of_latPts (by norm_num) hl hr (hS' (23 / 10) (by unfold ptsR; intro x hx; simp [hx]))
  have h5 := noPt_of_latPts (by norm_num) hl hr (hS' (43 / 40) (by unfold ptsR; intro x hx; simp [hx]))
  have h6 := noPt_of_latPts (by norm_num) hl hr (hS' (3 / 10) (by unfold ptsR; intro x hx; simp [hx]))
  obtain ⟨A, B, hAB⟩ := Rg_affine_cell hlr h2 h3 h4 h5 h6
  exact ⟨fun t => A * t + B, by fun_prop, hAB⟩

/-- The break points of `g_ref` in `[a, b]`. -/
noncomputable def ptsG (a b : ℝ) : Finset ℝ :=
  latPts 2 a b ∪ latPts (23 / 10) a b ∪ latPts (3 / 10) a b

theorem cellCont_gref (a b : ℝ) : CellCont (gref : ℝ → ℝ) (ptsG a b) a b := by
  intro l r hl hlr hr hS
  have hS' : ∀ c, latPts c a b ⊆ ptsG a b → ∀ s ∈ latPts c a b, s ∉ Ioo l r :=
    fun c hsub s hs => hS s (hsub hs)
  have h2 := noPt_of_latPts (by norm_num) hl hr (hS' 2 (by unfold ptsG; intro x hx; simp [hx]))
  have h4 := noPt_of_latPts (by norm_num) hl hr (hS' (23 / 10) (by unfold ptsG; intro x hx; simp [hx]))
  have h6 := noPt_of_latPts (by norm_num) hl hr (hS' (3 / 10) (by unfold ptsG; intro x hx; simp [hx]))
  set m : ℝ := (l + r) / 2 with hmdef
  have hm : m ∈ Ioo l r := ⟨by rw [hmdef]; linarith, by rw [hmdef]; linarith⟩
  -- frozen pieces
  set A1 : ℝ → ℝ := fun t => (1 - sg m) / 2 + sg m * (t - ⌊m⌋) with hA1
  set A2 : ℝ → ℝ := fun t => (1 - sg (al * m)) / 2 + sg (al * m) * (al * t - ⌊al * m⌋) with hA2
  set U : ℝ → ℝ := fun t => 23 / 20 * t - ((gT m : ℤ) : ℝ) / 2 with hU
  set Sf : ℝ → ℝ := fun t => 1 / 2 - A1 t with hSf
  set Qf : ℝ → ℝ := fun t => max 0 (A2 t - A1 t) with hQf
  set Ef : ℝ → ℝ := fun t => if Int.fract m < 1 / 2 then max 0 (U t - A1 t) else min (U t) (Sf t)
    with hEf
  set Gf : ℝ → ℝ := fun t => if gT m % 2 = 0 then max 0 (Ef t - Qf t)
    else max 0 (Sf t - Ef t - Qf t) with hGf
  refine ⟨Gf, ?_, ?_⟩
  · have cA1 : Continuous A1 := by rw [hA1]; fun_prop
    have cA2 : Continuous A2 := by rw [hA2]; fun_prop
    have cU : Continuous U := by rw [hU]; fun_prop
    have cS : Continuous Sf := by rw [hSf]; fun_prop
    have cQ : Continuous Qf := by rw [hQf]; fun_prop
    have cE : Continuous Ef := by
      rw [hEf]
      split_ifs
      · fun_prop
      · fun_prop
    apply Continuous.continuousOn
    rw [hGf]
    split_ifs
    · fun_prop
    · fun_prop
  · intro t ht
    obtain ⟨s1, f1⟩ := sg_const h2 ht hm
    obtain ⟨s2, f2⟩ := sg_const_al h6 ht hm
    have hT1 : tri t = A1 t := by rw [hA1, tri_eq, s1, Int.fract, f1]
    have hT2 : tri (al * t) = A2 t := by rw [hA2, tri_eq, s2, Int.fract, f2]
    have hgT : gT t = gT m := by
      unfold gT
      exact floor_const (by norm_num) h4 ht hm
    have hu : gu t = U t := by rw [hU]; unfold gu; rw [hgT]
    have hs : gs t = Sf t := by rw [hSf]; unfold gs; rw [hT1]
    have hq : gq t = Qf t := by rw [hQf]; unfold gq; rw [hT1, hT2]
    have hfr : (Int.fract t < 1 / 2 ↔ Int.fract m < 1 / 2) := fract_lt_iff_sg s1
    have he : ge t = Ef t := by
      rw [hEf]; unfold ge
      by_cases hc : Int.fract m < 1 / 2
      · rw [if_pos (hfr.2 hc)]; beta_reduce; rw [if_pos hc, hu, hT1]
      · rw [if_neg (fun h => hc (hfr.1 h))]; beta_reduce; rw [if_neg hc, hu, hs]
    rw [hGf]; beta_reduce; unfold gref
    rw [hgT, he, hq, hs]

theorem rg_psum {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun x => (Rg x : ℝ) / x ^ 3) volume a b ∧
      Tendsto (psum Rg a b) atTop (𝓝 (∫ x in a..b, (Rg x : ℝ) / x ^ 3)) :=
  cell_prime_sum (ptsR a b) _ a b le_rfl ha hab (cellCont_Rg a b)

theorem gref_psum {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun x => (gref x : ℝ) / x ^ 3) volume a b ∧
      Tendsto (psum gref a b) atTop (𝓝 (∫ x in a..b, (gref x : ℝ) / x ^ 3)) :=
  cell_prime_sum (ptsG a b) _ a b le_rfl ha hab (cellCont_gref a b)

/-- The outer profile `x T₀(1/x)` on `[20/37, 3]` (ZC34). -/
theorem ex_psum : Tendsto (psum Ex (20 / 37) 3) atTop (𝓝 (127751 / 96000)) := by
  have h := e01
  unfold segE at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hl, hok⟩, hv⟩, he⟩ := h
  have hT := prime_sum_okChain (H := (Ex : ℝ → ℝ)) hl (okChain_of_chainOKE _ _ hok)
  rw [he] at hT
  have e1 : ((20 / 37 : ℚ) : ℝ) = 20 / 37 := by norm_num
  have e2 : ((3 : ℚ) : ℝ) = 3 := by norm_num
  rw [e1, e2, zc34_x] at hT
  exact hT

/-- The outer saving `[x T₀(1/x) − R(x)]₊` on `[1, 3]` (ZC35). -/
theorem hp_psum : Tendsto (psum (fun t => max 0 (Ex t - Rg t)) 1 3) atTop (𝓝 (3203 / 163200)) := by
  have h := h01
  unfold segH at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hl, hok⟩, hv⟩, he⟩ := h
  have hT := prime_sum_okChain (H := fun t : ℝ => max 0 (Ex t - Rg t)) hl
    (okChain_of_chainOKH _ _ hok)
  rw [he] at hT
  have e1 : ((1 : ℚ) : ℝ) = 1 := by norm_num
  have e2 : ((3 : ℚ) : ℝ) = 3 := by norm_num
  rw [e1, e2, zc35_x] at hT
  exact hT

end CatalanCore.Zeta5.Content
