module

public import CatalanCore.Cert.SigmaHybS.HDefs
public import CatalanCore.Cert.SigmaHyb.HMacro

@[expose] public section

/-!
# Hybrid macro checks on the SigmaHybS engine (`rho = 1/4096`)

`gHR L = gfun L - UexR`: with the masses of `L` summing to `1 + alpha = 9/8`, this is the hybrid
function `g_h = (1+alpha) U^sigma - U^tau - U^ex + field` (`Bridge`).
* `gMacroOK L mp M P j` : `mp ≤ gHR L` on every cell box of ray macro `j` (cells `xlo xhi ylo yhi`, stride `4+4M`).
* `realMacroOKH L mode G M P j` : real-axis cells `[xlo,xhi]` (stride `4+3M`, cells `xlo xhi γ`);
  `γ/2^32` (segment mode) or `G` (line mode) `≤ gfun L x 0 - UexR x 0`.
-/

open Real

namespace CatalanCore.Cert.SigmaHybS

open CatalanCore.Cert.SigmaHyb (UexR uexR_le uexAxis_le)

set_option maxRecDepth 100000

theorem UbUp_eq : UbUp = CatalanCore.Cert.SigmaHyb.UbUp := rfl
theorem UexUp_eq : UexUp = CatalanCore.Cert.SigmaHyb.UexUp := rfl
theorem UexAxisUp_eq : UexAxisUp = CatalanCore.Cert.SigmaHyb.UexAxisUp := rfl
theorem sideLine_eq : sideLine = CatalanCore.Cert.SigmaHyb.sideLine := rfl

theorem uexR_le' (xlo xhi ylo yhi : ℤ) (hxhi : xhi < 2 ^ 40) (hxlohi : xlo ≤ xhi) (hylo : 0 ≤ ylo)
    (x y : ℝ) (hx1 : (xlo : ℝ) / 2 ^ 40 ≤ x) (hx2 : x ≤ (xhi : ℝ) / 2 ^ 40)
    (hy1 : (ylo : ℝ) / 2 ^ 40 ≤ y) (hy2 : y ≤ (yhi : ℝ) / 2 ^ 40) :
    UexR x y ≤ ((UexUp xlo xhi ylo yhi : ℚ) : ℝ) := by
  rw [UexUp_eq]; exact uexR_le xlo xhi ylo yhi hxhi hxlohi hylo x y hx1 hx2 hy1 hy2

theorem uexAxis_le' (xlo xhi : ℤ) (hs : sideLine xlo xhi) (x : ℝ)
    (hx1 : (xlo : ℝ) / 2 ^ 40 ≤ x) (hx2 : x ≤ (xhi : ℝ) / 2 ^ 40) :
    UexR x 0 ≤ ((UexAxisUp xlo xhi : ℚ) : ℝ) := by
  rw [UexAxisUp_eq]; exact uexAxis_le xlo xhi (by rw [sideLine_eq] at hs; exact hs) x hx1 hx2

noncomputable def gHR (pts : List Pt) (x y : ℝ) : ℝ := gfun pts x y - UexR x y

theorem box_sound_H (pts : List Pt) (Ls mp : ℚ) (xlo xhi ylo yhi : ℤ)
    (hxhi : xhi < 0) (hxlohi : xlo ≤ xhi) (hylo : 0 ≤ ylo)
    (hchk : mp ≤ boxLBH Ls xlo xhi ylo yhi) (x y : ℝ)
    (hx1 : (xlo : ℝ) / 2 ^ 40 ≤ x) (hx2 : x ≤ (xhi : ℝ) / 2 ^ 40)
    (hy1 : (ylo : ℝ) / 2 ^ 40 ≤ y) (hy2 : y ≤ (yhi : ℝ) / 2 ^ 40)
    (hS : (Ls : ℝ) ≤ Usig pts x y) :
    (mp : ℝ) ≤ gHR pts x y := by
  have h1 := box_sound_g pts Ls (mp + UexUp xlo xhi ylo yhi) xlo xhi ylo yhi hxhi hxlohi hylo
    (by unfold boxLBH at hchk; linarith) x y hx1 hx2 hy1 hy2 hS
  have h2 := uexR_le' xlo xhi ylo yhi (by omega) hxlohi hylo x y hx1 hx2 hy1 hy2
  unfold gHR
  push_cast at h1
  linarith

theorem gMacro_sound (L : List Pt) (mp : ℚ) (M P j : ℕ) (h : gMacroOK L mp M P j = true) :
    ∀ c < M, ∀ x y : ℝ,
      ((cellBox M P j c).1 : ℝ) / 2 ^ 40 ≤ x → x ≤ ((cellBox M P j c).2.1 : ℝ) / 2 ^ 40 →
      ((cellBox M P j c).2.2.1 : ℝ) / 2 ^ 40 ≤ y → y ≤ ((cellBox M P j c).2.2.2 : ℝ) / 2 ^ 40 →
      (mp : ℝ) ≤ gHR L x y := by
  intro c hc x y h1 h2 h3 h4
  simp only [gMacroOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨hi, hall⟩ := h
  have hcell := hall c hc
  try simp only [Bool.and_eq_true, decide_eq_true_eq] at hcell
  obtain ⟨⟨hs1, hs2, hs3⟩, hmp⟩ := hcell
  simp only [cellBox] at h1 h2 h3 h4 ⊢
  have hsplit := split_eq L _ _ hi
  have hS := sigTL_sound (slot P (j * (4 + 4 * M))) (slot P (j * (4 + 4 * M) + 1))
    (L.take (slot P (j * (4 + 4 * M) + 2)).toNat)
    ((L.drop (slot P (j * (4 + 4 * M) + 2)).toNat).take
      ((slot P (j * (4 + 4 * M) + 3)).toNat - (slot P (j * (4 + 4 * M) + 2)).toNat))
    (L.drop (slot P (j * (4 + 4 * M) + 3)).toNat)
    _ _ _ _ x y h1 h2 h3 h4
  rw [hsplit] at hS
  exact box_sound_H L _ _ _ _ _ _ hs1 hs2 hs3 hmp x y h1 h2 h3 h4 hS

/-- Soundness of a whole module of `n` macros. -/
theorem gMod_sound (L : List Pt) (mp : ℚ) (M P n : ℕ) (h : ∀ j < n, gMacroOK L mp M P j = true) :
    ∀ j < n, ∀ c < M, ∀ x y : ℝ,
      ((cellBox M P j c).1 : ℝ) / 2 ^ 40 ≤ x → x ≤ ((cellBox M P j c).2.1 : ℝ) / 2 ^ 40 →
      ((cellBox M P j c).2.2.1 : ℝ) / 2 ^ 40 ≤ y → y ≤ ((cellBox M P j c).2.2.2 : ℝ) / 2 ^ 40 →
      (mp : ℝ) ≤ gHR L x y :=
  fun j hj => gMacro_sound L mp M P j (h j hj)

/-! ### real axis -/

theorem realLBH_sound (x0 y0 : ℤ) (pre mid suf : List Pt) (xlo xhi : ℤ) (hside : sideReal xlo xhi)
    (x : ℝ) (h1 : (xlo : ℝ) / 2 ^ 40 ≤ x) (h2 : x ≤ (xhi : ℝ) / 2 ^ 40) :
    ((realLBH x0 y0 (farSum x0 y0 (pre ++ suf)) mid xlo xhi : ℚ) : ℝ) ≤ gHR (pre ++ mid ++ suf) x 0 := by
  have hS := sigTL_sound x0 y0 pre mid suf xlo xhi 0 0 x 0 h1 h2 (by simp) (by simp)
  obtain ⟨hle, hcases, hex⟩ := hside
  have hU : Utau x 0 ≤ ((if xhi ≤ 0 then utA xlo xhi else utB xlo xhi : ℚ) : ℝ) := by
    split_ifs with hx
    · exact utA_sound _ _ hx (by rcases hcases with ⟨_, h⟩ | ⟨h, h'⟩ <;> omega) hle x h1 h2
    · exact utB_sound _ _ (by rcases hcases with ⟨h, _⟩ | ⟨h, h'⟩ <;> omega) hle
        (by rcases hcases with ⟨h, _⟩ | ⟨h, h'⟩ <;> omega) x h1 h2
  have hE : UexR x 0 ≤ ((UexAx xlo xhi : ℚ) : ℝ) := by
    unfold UexAx
    split_ifs with hx
    · exact uexR_le' xlo xhi 0 0 (by omega) hle le_rfl x 0 h1 h2 (by simp) (by simp)
    · exact uexAxis_le' xlo xhi (hex.resolve_left hx) x h1 h2
  unfold realLBH gHR gfun
  push_cast
  simp only [mul_zero, add_zero]
  push_cast at hS hU hE
  linarith

theorem realMacroH_sound (L : List Pt) (mode : Bool) (G : ℚ) (M P j : ℕ)
    (h : realMacroOKH L mode G M P j = true) :
    ∀ c < M, ∀ x : ℝ,
      ((realCell M P j c).1 : ℝ) / 2 ^ 40 ≤ x → x ≤ ((realCell M P j c).2.1 : ℝ) / 2 ^ 40 →
      ((realThr mode G M P j c : ℚ) : ℝ) ≤ gHR L x 0 := by
  intro c hc x h1 h2
  simp only [realMacroOKH, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨hi, hall⟩ := h
  have hcell := hall c hc
  try simp only [Bool.and_eq_true, decide_eq_true_eq] at hcell
  obtain ⟨hside, hthr⟩ := hcell
  have hsplit := split_eq L _ _ hi
  have key := realLBH_sound (slot P (j * (4 + 3 * M))) (slot P (j * (4 + 3 * M) + 1))
    (L.take (slot P (j * (4 + 3 * M) + 2)).toNat)
    ((L.drop (slot P (j * (4 + 3 * M) + 2)).toNat).take
      ((slot P (j * (4 + 3 * M) + 3)).toNat - (slot P (j * (4 + 3 * M) + 2)).toNat))
    (L.drop (slot P (j * (4 + 3 * M) + 3)).toNat)
    (slot P (j * (4 + 3 * M) + 4 + 3 * c)) (slot P (j * (4 + 3 * M) + 4 + 3 * c + 1)) hside x h1 h2
  rw [hsplit] at key
  have hthr' : realThr mode G M P j c ≤ realLBH (slot P (j * (4 + 3 * M))) (slot P (j * (4 + 3 * M) + 1))
      (farSum (slot P (j * (4 + 3 * M))) (slot P (j * (4 + 3 * M) + 1))
        (L.take (slot P (j * (4 + 3 * M) + 2)).toNat ++ L.drop (slot P (j * (4 + 3 * M) + 3)).toNat))
      ((L.drop (slot P (j * (4 + 3 * M) + 2)).toNat).take
        ((slot P (j * (4 + 3 * M) + 3)).toNat - (slot P (j * (4 + 3 * M) + 2)).toNat))
      (slot P (j * (4 + 3 * M) + 4 + 3 * c)) (slot P (j * (4 + 3 * M) + 4 + 3 * c + 1)) := by
    simpa [realThr, realCell] using hthr
  exact le_trans (by exact_mod_cast hthr') key

end CatalanCore.Cert.SigmaHybS
