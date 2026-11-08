module

public import CatalanMeasure.GenD.DesignInstance.PositiveCert.RTab
public import CatalanMeasure.GenD.DesignInstance.PositiveCert.RZ
public import CatalanMeasure.GenD.DesignInstance.PositiveCert.Data
public import CatalanMeasure.GenD.Cert.WLogSpec
public import CatalanMeasure.GenD.Cert.Assembly
public import CatalanMeasure.GenD.DesignInstance.PositiveCert.RPairData
public import CatalanMeasure.GenD.Cert.AssemblyCap
public import CatalanMeasure.GenD.Cert.TrialCell
public import CatalanMeasure.GenD.DesignInstance.PositiveCert.RN002
public import CatalanMeasure.GenD.DesignInstance.PositiveCert.RN003
public import CatalanMeasure.GenD.DesignInstance.PositiveCert.RN004
public import CatalanMeasure.GenD.DesignInstance.PositiveCert.RN005
public import CatalanMeasure.GenD.DesignInstance.PositiveCert.RN006
public import CatalanMeasure.GenD.DesignInstance.PositiveCert.RN007
public import CatalanMeasure.GenD.DesignInstance.PositiveCert.RN008
public import CatalanMeasure.GenD.DesignInstance.PositiveCert.RN009
public import CatalanMeasure.GenD.DesignInstance.PositiveCert.RN010

@[expose] public section

/-!
# The residual pair cover (G32d)

`residual_pair`: for `τ ∈ {0, 1}` and every `x ∈ [-1,1]` with `G x`,
`F₁(x) - 2 τ T(du, x) + δ(x) ≤ res_τ`, where `F₁ = resFieldW (53/58) (trialSeqS Pc P)`,
`T(du, x) = ∑ du_i T_{i+1}(x)/(i+1)` (`qSum aDuList 1 x`, `du` on the `2^-24` grid), `δ(x) = dh(2x/(1+x²))/58`
and `res_0 = 7/1000`, `res_1 = -268/10000`.  The cells are the built `RM` cells (and 25 new or split cells) with
one cap per cell, `capC0 = res_0 - dd`, `capC1 = res_1 - dd + 2 lw`, where `dd c` is the chord maximum on `c`
and `lw c ≤ T(du, ·)` on `c` (`TrialCell.lowT_le`).  The chord bound `hdh` is the hypothesis `dh/58 ≤ dd` per cell
(proved from the chord table by the consumer); `hG` is the window: `G ⊆ [-0.9636, 0.99942] ∩ {|x| ≥ 401/2500}`.
-/

namespace CatalanMeasure.GenD.D58.Cert590
open CatalanMeasure.CellCert CatalanMeasure.Cert CatalanMeasure.GenD.Cert.TrialCell OAI.InternalCatalan Set
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem sound_R (t : ℕ) : (resSpecW (53/58 : ℚ) Pc P t).Sound D_R.toD (resFieldW (((53/58 : ℚ) : ℚ) : ℝ) (trialSeqS Pc P)) :=
  resSpecW_sound (53/58 : ℚ) tailsP P_nonzero D_R.toD hZ_R t

def blocksP : List Block := [PB004, PB005, PB006, PB007, PB008, PB009, PB010, PB011, PB012, PB013, PB014, PB015, PB016, PB017, PB018, PB019, PB020, PB021]

theorem blocksP_ok0 : ∀ b ∈ blocksP, blockOKc (resSpecW (53/58 : ℚ) Pc P) D_R.toD 5 65 MGL_R capC0 b = true := by
  intro b hb
  simp only [blocksP, List.mem_cons, List.mem_nil_iff, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact PB004_ok0
  · exact PB005_ok0
  · exact PB006_ok0
  · exact PB007_ok0
  · exact PB008_ok0
  · exact PB009_ok0
  · exact PB010_ok0
  · exact PB011_ok0
  · exact PB012_ok0
  · exact PB013_ok0
  · exact PB014_ok0
  · exact PB015_ok0
  · exact PB016_ok0
  · exact PB017_ok0
  · exact PB018_ok0
  · exact PB019_ok0
  · exact PB020_ok0
  · exact PB021_ok0

theorem blocksP_ok1 : ∀ b ∈ blocksP, blockOKc (resSpecW (53/58 : ℚ) Pc P) D_R.toD 5 65 MGL_R capC1 b = true := by
  intro b hb
  simp only [blocksP, List.mem_cons, List.mem_nil_iff, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact PB004_ok1
  · exact PB005_ok1
  · exact PB006_ok1
  · exact PB007_ok1
  · exact PB008_ok1
  · exact PB009_ok1
  · exact PB010_ok1
  · exact PB011_ok1
  · exact PB012_ok1
  · exact PB013_ok1
  · exact PB014_ok1
  · exact PB015_ok1
  · exact PB016_ok1
  · exact PB017_ok1
  · exact PB018_ok1
  · exact PB019_ok1
  · exact PB020_ok1
  · exact PB021_ok1

theorem lw_P : ∀ b ∈ blocksP, ∀ c ∈ b.cells, 0 < c.2.1 ∧ ∃ cp hp : ℤ, 0 < hp ∧
    |(c.1 : ℚ) / (TT : ℚ) - (cp : ℚ) / (847288609443 : ℚ)| + (c.2.1 : ℚ) / (TT : ℚ) ≤ (hp : ℚ) / (847288609443 : ℚ) ∧
    tabGet lwTab c.1 ≤ lowTI cp hp 847288609443 wDu DuD0 := by
  intro b hb
  simp only [blocksP, List.mem_cons, List.mem_nil_iff, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact PB004_lw
  · exact PB005_lw
  · exact PB006_lw
  · exact PB007_lw
  · exact PB008_lw
  · exact PB009_lw
  · exact PB010_lw
  · exact PB011_lw
  · exact PB012_lw
  · exact PB013_lw
  · exact PB014_lw
  · exact PB015_lw
  · exact PB016_lw
  · exact PB017_lw
  · exact PB018_lw
  · exact PB019_lw
  · exact PB020_lw
  · exact PB021_lw

theorem cover_PL : coverFrom (-401/2500) (qfloor ((-9636/10000 : ℚ) * (TT : ℚ))) (blocksCells (blocksP.take 8)) = true := by
  decide +kernel
  -- kcost: 0.3 s measured 7 Nov (RN005 profile)
theorem cover_PR : coverFrom (99942/100000) (qfloor ((401/2500 : ℚ) * (TT : ℚ))) (blocksCells (blocksP.drop 8)) = true := by
  decide +kernel

/-- one side of the pair cover, for a general cap family -/
  -- kcost: 0.3 s measured 7 Nov (RN005 profile)
theorem pair_side (capC : TCell → ℚ) (res t : ℚ) (ht : 0 ≤ t)
    (hcap : ∀ c : TCell, capC c + (tabGet ddTab c.1 - t * tabGet lwTab c.1) ≤ res)
    (hbs : ∀ b ∈ blocksP, blockOKc (resSpecW (53/58 : ℚ) Pc P) D_R.toD 5 65 MGL_R capC b = true)
    (dh : ℝ → ℝ)
    (hdh : ∀ b ∈ blocksP, ∀ c ∈ b.cells, ∀ y : ℝ, |y - (c.1 : ℝ) / TT| ≤ (c.2.1 : ℝ) / TT →
      dh (2 * y / (1 + y ^ 2)) / 58 ≤ (tabGet ddTab c.1 : ℝ))
    (bs : List Block) (hsub : ∀ b ∈ bs, b ∈ blocksP) (L0 : ℤ) (ghi : ℚ)
    (hcov : coverFrom ghi L0 (blocksCells bs) = true) (x : ℝ)
    (hL : (L0 : ℝ) / TT ≤ x) (hx : x ≤ (ghi : ℝ))
    (hxp : ∀ c : TCell, ∀ pr, (resSpecW (53/58 : ℚ) Pc P c.2.2).peel = some pr → x ≠ (pr.2 : ℝ)) :
    resFieldW (((53/58 : ℚ) : ℚ) : ℝ) (trialSeqS Pc P) x - (t : ℝ) * qSum aDuList 1 x + dh (2 * x / (1 + x ^ 2)) / 58 ≤ (res : ℝ) := by
  have key := field_add_le_of_blocks_capc (resFieldW (((53/58 : ℚ) : ℚ) : ℝ) (trialSeqS Pc P))
    (fun y => dh (2 * y / (1 + y ^ 2)) / 58 - (t : ℝ) * qSum aDuList 1 y) (resSpecW (53/58 : ℚ) Pc P) D_R.toD D_R_ok 5 65 MGL_R hMGL_R
    capC (fun c => tabGet ddTab c.1 - t * tabGet lwTab c.1) (res : ℝ) bs (fun c _ => sound_R c.2.2) L0 ghi hcov
    (fun b hb => hbs b (hsub b hb)) ?_ ?_ x hL hx (fun c _ => hxp c)
  · simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using key
  · intro c hc y hy
    obtain ⟨b, hb, hcb⟩ := List.mem_flatMap.mp hc
    have hdd := hdh b (hsub b hb) c hcb y hy
    obtain ⟨hpos, cp, hp, hhp, hcont, hlw⟩ := lw_P b (hsub b hb) c hcb
    have hcontR : |(c.1 : ℝ) / TT - (cp : ℝ) / 847288609443| + (c.2.1 : ℝ) / TT ≤ (hp : ℝ) / 847288609443 := by
      have := (Rat.cast_le (K := ℝ)).mpr hcont
      push_cast at this
      exact this
    have hy2 : |y - ((cp : ℤ) : ℝ) / ((847288609443 : ℤ) : ℝ)| ≤ ((hp : ℤ) : ℝ) / ((847288609443 : ℤ) : ℝ) := by
      have h1 : |y - (cp : ℝ) / 847288609443| ≤ |y - (c.1 : ℝ) / TT| + |(c.1 : ℝ) / TT - (cp : ℝ) / 847288609443| := by
        have := abs_add_le (y - (c.1 : ℝ) / TT) ((c.1 : ℝ) / TT - (cp : ℝ) / 847288609443)
        simpa using this
      push_cast
      linarith
    have hT := lowTI_le cp hp 847288609443 (by norm_num) hhp wDu DuD0 (by unfold DuD0 LCM40; norm_num) hy2
    have hlw' : (tabGet lwTab c.1 : ℝ) ≤ qSum aDuList 1 y := by
      rw [qSum_aDu]
      exact le_trans (by exact_mod_cast hlw) hT
    have ht' : (0 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hlw' ht']
  · intro c _
    have := hcap c
    exact_mod_cast this

theorem pair_core (capC : TCell → ℚ) (res t : ℚ) (ht : 0 ≤ t)
    (hcap : ∀ c : TCell, capC c + (tabGet ddTab c.1 - t * tabGet lwTab c.1) ≤ res)
    (hbs : ∀ b ∈ blocksP, blockOKc (resSpecW (53/58 : ℚ) Pc P) D_R.toD 5 65 MGL_R capC b = true)
    (G : ℝ → Prop) (dh : ℝ → ℝ)
    (hG : ∀ x, G x → (-9636/10000 : ℝ) ≤ x ∧ x ≤ 99942/100000 ∧ (401/2500 : ℝ) ≤ |x|)
    (hdh : ∀ b ∈ blocksP, ∀ c ∈ b.cells, ∀ y : ℝ, |y - (c.1 : ℝ) / TT| ≤ (c.2.1 : ℝ) / TT →
      dh (2 * y / (1 + y ^ 2)) / 58 ≤ (tabGet ddTab c.1 : ℝ)) :
    ∀ x ∈ Icc (-1 : ℝ) 1, G x →
      resFieldW (((53/58 : ℚ) : ℚ) : ℝ) (trialSeqS Pc P) x - (t : ℝ) * qSum aDuList 1 x + dh (2 * x / (1 + x ^ 2)) / 58 ≤ (res : ℝ) := by
  intro x hx hGx
  obtain ⟨hl, hr, hab⟩ := hG x hGx
  have hxp : ∀ c : TCell, ∀ pr, (resSpecW (53/58 : ℚ) Pc P c.2.2).peel = some pr → x ≠ (pr.2 : ℝ) := by
    intro c pr h
    simp [resSpecW] at h
  rcases le_abs'.mp hab with h | h
  · refine pair_side capC res t ht hcap hbs dh hdh (blocksP.take 8) (fun b hb => List.mem_of_mem_take hb)
      (qfloor ((-9636/10000 : ℚ) * (TT : ℚ))) (-401/2500) cover_PL x ?_ ?_ hxp
    · exact floor_le_of_ge (-9636/10000) x (by push_cast; linarith)
    · push_cast; linarith
  · refine pair_side capC res t ht hcap hbs dh hdh (blocksP.drop 8) (fun b hb => List.mem_of_mem_drop hb)
      (qfloor ((401/2500 : ℚ) * (TT : ℚ))) (99942/100000) cover_PR x ?_ ?_ hxp
    · exact floor_le_of_ge (401/2500) x (by push_cast; linarith)
    · push_cast; linarith

theorem residual_pair0 (G : ℝ → Prop) (dh : ℝ → ℝ)
    (hG : ∀ x, G x → (-9636/10000 : ℝ) ≤ x ∧ x ≤ 99942/100000 ∧ (401/2500 : ℝ) ≤ |x|)
    (hdh : ∀ b ∈ blocksP, ∀ c ∈ b.cells, ∀ y : ℝ, |y - (c.1 : ℝ) / TT| ≤ (c.2.1 : ℝ) / TT →
      dh (2 * y / (1 + y ^ 2)) / 58 ≤ (tabGet ddTab c.1 : ℝ)) :
    ∀ x ∈ Icc (-1 : ℝ) 1, G x →
      resFieldW (((53/58 : ℚ) : ℚ) : ℝ) (trialSeqS Pc P) x + dh (2 * x / (1 + x ^ 2)) / 58 ≤ (7 / 1000 : ℝ) := by
  intro x hx hGx
  have := pair_core capC0 (7/1000) 0 le_rfl (fun c => by unfold capC0; ring_nf; exact le_rfl) blocksP_ok0 G dh hG hdh x hx hGx
  simpa using this

theorem residual_pair1 (G : ℝ → Prop) (dh : ℝ → ℝ)
    (hG : ∀ x, G x → (-9636/10000 : ℝ) ≤ x ∧ x ≤ 99942/100000 ∧ (401/2500 : ℝ) ≤ |x|)
    (hdh : ∀ b ∈ blocksP, ∀ c ∈ b.cells, ∀ y : ℝ, |y - (c.1 : ℝ) / TT| ≤ (c.2.1 : ℝ) / TT →
      dh (2 * y / (1 + y ^ 2)) / 58 ≤ (tabGet ddTab c.1 : ℝ)) :
    ∀ x ∈ Icc (-1 : ℝ) 1, G x →
      resFieldW (((53/58 : ℚ) : ℚ) : ℝ) (trialSeqS Pc P) x - 2 * qSum aDuList 1 x + dh (2 * x / (1 + x ^ 2)) / 58 ≤ (-268 / 10000 : ℝ) := by
  intro x hx hGx
  have := pair_core capC1 (-268/10000) 2 (by norm_num) (fun c => by unfold capC1; ring_nf; exact le_rfl) blocksP_ok1 G dh hG hdh x hx hGx
  simpa using this

/-- the pair statement, `τ ∈ {0, 1}` -/
theorem residual_pair (G : ℝ → Prop) (dh : ℝ → ℝ)
    (hG : ∀ x, G x → (-9636/10000 : ℝ) ≤ x ∧ x ≤ 99942/100000 ∧ (401/2500 : ℝ) ≤ |x|)
    (hdh : ∀ b ∈ blocksP, ∀ c ∈ b.cells, ∀ y : ℝ, |y - (c.1 : ℝ) / TT| ≤ (c.2.1 : ℝ) / TT →
      dh (2 * y / (1 + y ^ 2)) / 58 ≤ (tabGet ddTab c.1 : ℝ)) (τ : Fin 2) :
    ∀ x ∈ Icc (-1 : ℝ) 1, G x →
      resFieldW (((53/58 : ℚ) : ℚ) : ℝ) (trialSeqS Pc P) x - 2 * (τ.val : ℝ) * qSum aDuList 1 x +
        dh (2 * x / (1 + x ^ 2)) / 58 ≤ (if τ.val = 0 then (7 / 1000 : ℝ) else (-268 / 10000 : ℝ)) := by
  fin_cases τ
  · intro x hx hGx
    simpa using residual_pair0 G dh hG hdh x hx hGx
  · intro x hx hGx
    simpa using residual_pair1 G dh hG hdh x hx hGx

end CatalanMeasure.GenD.D58.Cert590
#print axioms CatalanMeasure.GenD.D58.Cert590.residual_pair
