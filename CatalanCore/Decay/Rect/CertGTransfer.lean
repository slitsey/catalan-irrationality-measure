module

public import CatalanCore.Decay.Rect.CertG

@[expose] public section

/-!
# Transfer of a `CertCoreG` under pointwise domination (P6DECAY, G1)

If `g' ≥ F.g` on the region where the certificate reads `g` (the real segment `(-∞, 1]` and the
half plane `Re ≤ -r0 + W`), then every lower-bound field of `F` is also a lower-bound field of `g'`.
Only the energy field `I_ok` (the measure `(c', m')` and the bound `I`) is new, so a hybrid
certificate `g_h = g_sq + h` with `h ≥ 0` reuses a square certificate verbatim.
Ray boxes are clipped to `ylo ≥ 0` and line cells to `x ≤ 1` (the domination is only needed there).
-/

open Finset
open CatalanLambda.Decay (Irho)

namespace CatalanCore.Cert

variable {sl : ℝ} {K K' : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {m : Fin K → ℝ}

/-- **Transfer.**  `F.g ≤ g'` on `{Im = 0, Re ≤ 1} ∪ {Re ≤ -r0 + W}` gives a certificate for `g'`
with the same data and the new energy bound `I`. -/
noncomputable def CertCoreGs.ofLe (F : CertCoreGs sl K ρ ε c m) {c' : Fin K' → ℂ} {m' : Fin K' → ℝ}
    (g' : ℂ → ℝ)
    (hle : ∀ s : ℂ, ((s.im = 0 ∧ s.re ≤ 1) ∨ s.re ≤ -(F.r0 : ℝ) + F.W) → F.g s ≤ g' s)
    (humax : (0 : ℝ) ≤ F.umax) (hseg : ∀ i, (F.segB i : ℝ) ≤ 1)
    (hconj : ∀ s, g' ((starRingEnd ℂ) s) = g' s) (hm : ∑ k, m' k = 1)
    (I : ℚ) (hI : Irho ρ c' m' ≤ I) (hs : 0 ≤ sl := by norm_num) :
    CertCoreGs sl K' ρ ε c' m' where
  g := g'
  r0 := F.r0
  W := F.W
  umax := F.umax
  mprime := F.mprime
  gmin := F.gmin
  Sbase := F.Sbase
  Ibound := I
  ccert := F.ccert
  r0_pos := F.r0_pos
  W_pos := F.W_pos
  hρ := F.hρ
  hε0 := F.hε0
  hε1 := F.hε1
  hm := hm
  g_conj := hconj
  rayBoxes := F.rayBoxes.map (fun p => (max p.1 0, p.2))
  ray_box_ok := by
    intro p hp x y hx1 hx2 hy1 hy2
    simp only [List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    simp only [Rat.cast_max, Rat.cast_zero] at hx1 hx2 hy1 hy2
    have hq0 : (q.1 : ℝ) ≤ max (q.1 : ℝ) 0 := le_max_left _ _
    have h00 : (0 : ℝ) ≤ max (q.1 : ℝ) 0 := le_max_right _ _
    refine (F.ray_box_ok q hq x y hx1 (by linarith) ((mul_le_mul_of_nonneg_left hq0 hs).trans hy1) hy2).trans (hle _ (Or.inr ?_))
    show x ≤ -(F.r0 : ℝ) + F.W
    linarith
  ray_cover := by
    intro u hu0 hu1
    obtain ⟨q, hq, h1, h2⟩ := F.ray_cover u hu0 hu1
    exact ⟨_, List.mem_map.2 ⟨q, hq, rfl⟩, by simp [h1, hu0], h2⟩
  ray_tail := by
    intro u δ hu hδ
    refine (F.ray_tail u δ hu hδ).trans (hle _ (Or.inr ?_))
    show -(F.r0 : ℝ) + δ - u ≤ -(F.r0 : ℝ) + F.W
    have := abs_le.1 hδ
    linarith
  nSeg := F.nSeg
  segA := F.segA
  segB := F.segB
  segG := F.segG
  seg_ab := F.seg_ab
  seg_ok := fun i x h1 h2 =>
    (F.seg_ok i x h1 h2).trans (hle _ (Or.inl ⟨rfl, h2.trans (hseg i)⟩))
  seg_cover := F.seg_cover
  Sbase_le := F.Sbase_le
  lineCells := F.lineCells.map (fun p => (p.1, min p.2 1))
  line_ok := by
    intro p hp x h1 h2
    simp only [List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    simp only [Rat.cast_min, Rat.cast_one, le_min_iff] at h2
    exact (F.line_ok q hq x h1 h2.1).trans (hle _ (Or.inl ⟨rfl, h2.2⟩))
  line_cover := by
    intro x h0 h1
    obtain ⟨q, hq, a, b⟩ := F.line_cover x h0 h1
    exact ⟨_, List.mem_map.2 ⟨q, hq, rfl⟩, a, by simp [b, h1]⟩
  I_ok := hI
  ccert_ge := F.ccert_ge

section simp
variable (F : CertCoreGs sl K ρ ε c m) (hs : 0 ≤ sl) {c' : Fin K' → ℂ} {m' : Fin K' → ℝ} (g' : ℂ → ℝ)
  (hle : ∀ s : ℂ, ((s.im = 0 ∧ s.re ≤ 1) ∨ s.re ≤ -(F.r0 : ℝ) + F.W) → F.g s ≤ g' s)
  (humax : (0 : ℝ) ≤ F.umax) (hseg : ∀ i, (F.segB i : ℝ) ≤ 1)
  (hconj : ∀ s, g' ((starRingEnd ℂ) s) = g' s) (hm : ∑ k, m' k = 1)
  (I : ℚ) (hI : Irho ρ c' m' ≤ I)

@[simp] theorem CertCoreGs.ofLe_g : (F.ofLe g' hle humax hseg hconj hm I hI hs).g = g' := rfl
@[simp] theorem CertCoreGs.ofLe_r0 : (F.ofLe g' hle humax hseg hconj hm I hI hs).r0 = F.r0 := rfl
@[simp] theorem CertCoreGs.ofLe_W : (F.ofLe g' hle humax hseg hconj hm I hI hs).W = F.W := rfl
@[simp] theorem CertCoreGs.ofLe_mprime :
    (F.ofLe g' hle humax hseg hconj hm I hI hs).mprime = F.mprime := rfl
@[simp] theorem CertCoreGs.ofLe_gmin : (F.ofLe g' hle humax hseg hconj hm I hI hs).gmin = F.gmin := rfl
@[simp] theorem CertCoreGs.ofLe_Sbase :
    (F.ofLe g' hle humax hseg hconj hm I hI hs).Sbase = F.Sbase := rfl
@[simp] theorem CertCoreGs.ofLe_ccert :
    (F.ofLe g' hle humax hseg hconj hm I hI hs).ccert = F.ccert := rfl
@[simp] theorem CertCoreGs.ofLe_Ibound : (F.ofLe g' hle humax hseg hconj hm I hI hs).Ibound = I := rfl

theorem CertCoreGs.ofLe_Dof (d : ℕ) (α Inu : ℚ) :
    (F.ofLe g' hle humax hseg hconj hm I hI hs).Dof d α Inu
      = 2 * ((1 + α) * F.mprime + d * F.Sbase) - (1 + α) ^ 2 * I + Inu := rfl

end simp

section slope3
variable (F : CertCoreG K ρ ε c m) {c' : Fin K' → ℂ} {m' : Fin K' → ℝ} (g' : ℂ → ℝ)
  (hle : ∀ s : ℂ, ((s.im = 0 ∧ s.re ≤ 1) ∨ s.re ≤ -(F.r0 : ℝ) + F.W) → F.g s ≤ g' s)
  (humax : (0 : ℝ) ≤ F.umax) (hseg : ∀ i, (F.segB i : ℝ) ≤ 1)
  (hconj : ∀ s, g' ((starRingEnd ℂ) s) = g' s) (hm : ∑ k, m' k = 1)
  (I : ℚ) (hI : Irho ρ c' m' ≤ I)

/-- Slope-`3` name of `CertCoreGs.ofLe_Dof`. -/
theorem CertCoreG.ofLe_Dof (d : ℕ) (α Inu : ℚ) :
    (F.ofLe g' hle humax hseg hconj hm I hI).Dof d α Inu
      = 2 * ((1 + α) * F.mprime + d * F.Sbase) - (1 + α) ^ 2 * I + Inu := rfl

end slope3

end CatalanCore.Cert
