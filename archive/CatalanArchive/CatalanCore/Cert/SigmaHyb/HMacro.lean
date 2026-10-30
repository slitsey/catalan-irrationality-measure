module

public import CatalanCore.Cert.SigmaHyb.HBox
public import CatalanLambda.Cert.RayTaylor
public import CatalanLambda.Cert.SegLine
public import CatalanLambda.Cert.RealCells

@[expose] public section

/-!
# Macros of cells for the hybrid checks (Taylor far-field as in the legacy `RayTaylor`)

Packed data (64-bit slots biased by `2^62`, `slot` from the legacy `RayTaylor`): macro `j` occupies
`j*(4+5M) ...`: `x0, y0, i0, i1`, then `M` cells `xlo xhi ylo yhi γ` (units `2^-40`, γ in `2^-32`).
* `hMacroOK L`  : `γ/2^32 ≤ Usig L - UexR` on each cell box (the correction `h`).
* `gMacroOK L mp` : `mp ≤ gfun L - UexR` on each cell box (the full hybrid, list form).
* `lMacroOK L G` : real-axis cells on `[0,1]` (cells `xlo xhi γ`, stride `4+3M`), `G ≤ gfun L x 0 - UexR x 0`.
-/

open Real

namespace CatalanCore.Cert.SigmaHyb

open CatalanLambda.Cert

set_option maxRecDepth 100000

def hCellBox (M P j c : ℕ) : ℤ × ℤ × ℤ × ℤ :=
  let a := j * (4 + 5 * M) + 4 + 5 * c
  (slot P a, slot P (a + 1), slot P (a + 2), slot P (a + 3))

def hCellGam (M P j c : ℕ) : ℤ := slot P (j * (4 + 5 * M) + 4 + 5 * c + 4)

def hMacroOK (L : List Pt) (M P j : ℕ) : Bool :=
  let b := j * (4 + 5 * M)
  let x0 := slot P b
  let y0 := slot P (b + 1)
  let i0 := (slot P (b + 2)).toNat
  let i1 := (slot P (b + 3)).toNat
  let fd := farSum x0 y0 (L.take i0 ++ L.drop i1)
  let mid := (L.drop i0).take (i1 - i0)
  decide (i0 ≤ i1) && (List.range M).all (fun c =>
    let a := b + 4 + 5 * c
    let xlo := slot P a
    let xhi := slot P (a + 1)
    let ylo := slot P (a + 2)
    let yhi := slot P (a + 3)
    let gam := slot P (a + 4)
    decide (xhi < 2 ^ 40 ∧ xlo ≤ xhi ∧ 0 ≤ ylo) &&
      decide ((gam : ℚ) / 2 ^ 32 ≤
        sigTL x0 y0 fd xlo xhi ylo yhi (sigSum xlo xhi ylo yhi mid) - UexUp xlo xhi ylo yhi))

def gMacroOK (L : List Pt) (mp : ℚ) (M P j : ℕ) : Bool :=
  let b := j * (4 + 5 * M)
  let x0 := slot P b
  let y0 := slot P (b + 1)
  let i0 := (slot P (b + 2)).toNat
  let i1 := (slot P (b + 3)).toNat
  let fd := farSum x0 y0 (L.take i0 ++ L.drop i1)
  let mid := (L.drop i0).take (i1 - i0)
  decide (i0 ≤ i1) && (List.range M).all (fun c =>
    let a := b + 4 + 5 * c
    let xlo := slot P a
    let xhi := slot P (a + 1)
    let ylo := slot P (a + 2)
    let yhi := slot P (a + 3)
    decide (xhi < 0 ∧ xlo ≤ xhi ∧ 0 ≤ ylo) &&
      decide (mp ≤ boxLBH (sigTL x0 y0 fd xlo xhi ylo yhi (sigSum xlo xhi ylo yhi mid)) xlo xhi ylo yhi))

theorem hMacro_sound (L : List Pt) (M P j : ℕ) (h : hMacroOK L M P j = true) :
    ∀ c < M, ∀ x y : ℝ,
      ((hCellBox M P j c).1 : ℝ) / 2 ^ 40 ≤ x → x ≤ ((hCellBox M P j c).2.1 : ℝ) / 2 ^ 40 →
      ((hCellBox M P j c).2.2.1 : ℝ) / 2 ^ 40 ≤ y → y ≤ ((hCellBox M P j c).2.2.2 : ℝ) / 2 ^ 40 →
      ((((hCellGam M P j c : ℤ) : ℚ) / 2 ^ 32 : ℚ) : ℝ) ≤ Usig L x y - UexR x y := by
  intro c hc x y h1 h2 h3 h4
  simp only [hMacroOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨hi, hall⟩ := h
  have hcell := hall c hc
  try simp only [Bool.and_eq_true, decide_eq_true_eq] at hcell
  obtain ⟨⟨hs1, hs2, hs3⟩, hmp⟩ := hcell
  simp only [hCellBox, hCellGam] at h1 h2 h3 h4 ⊢
  have hsplit := split_eq L _ _ hi
  have hS := sigTL_sound (slot P (j * (4 + 5 * M))) (slot P (j * (4 + 5 * M) + 1))
    (L.take (slot P (j * (4 + 5 * M) + 2)).toNat)
    ((L.drop (slot P (j * (4 + 5 * M) + 2)).toNat).take
      ((slot P (j * (4 + 5 * M) + 3)).toNat - (slot P (j * (4 + 5 * M) + 2)).toNat))
    (L.drop (slot P (j * (4 + 5 * M) + 3)).toNat)
    _ _ _ _ x y h1 h2 h3 h4
  rw [hsplit] at hS
  exact hbox_sound L _ _ _ _ _ _ hs1 hs2 hs3 hmp x y h1 h2 h3 h4 hS

theorem gMacro_sound (L : List Pt) (mp : ℚ) (M P j : ℕ) (h : gMacroOK L mp M P j = true) :
    ∀ c < M, ∀ x y : ℝ,
      ((hCellBox M P j c).1 : ℝ) / 2 ^ 40 ≤ x → x ≤ ((hCellBox M P j c).2.1 : ℝ) / 2 ^ 40 →
      ((hCellBox M P j c).2.2.1 : ℝ) / 2 ^ 40 ≤ y → y ≤ ((hCellBox M P j c).2.2.2 : ℝ) / 2 ^ 40 →
      (mp : ℝ) ≤ gHR L x y := by
  intro c hc x y h1 h2 h3 h4
  simp only [gMacroOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨hi, hall⟩ := h
  have hcell := hall c hc
  try simp only [Bool.and_eq_true, decide_eq_true_eq] at hcell
  obtain ⟨⟨hs1, hs2, hs3⟩, hmp⟩ := hcell
  simp only [hCellBox] at h1 h2 h3 h4 ⊢
  have hsplit := split_eq L _ _ hi
  have hS := sigTL_sound (slot P (j * (4 + 5 * M))) (slot P (j * (4 + 5 * M) + 1))
    (L.take (slot P (j * (4 + 5 * M) + 2)).toNat)
    ((L.drop (slot P (j * (4 + 5 * M) + 2)).toNat).take
      ((slot P (j * (4 + 5 * M) + 3)).toNat - (slot P (j * (4 + 5 * M) + 2)).toNat))
    (L.drop (slot P (j * (4 + 5 * M) + 3)).toNat)
    _ _ _ _ x y h1 h2 h3 h4
  rw [hsplit] at hS
  exact box_sound_H L _ _ _ _ _ _ hs1 hs2 hs3 hmp x y h1 h2 h3 h4 hS

theorem hMod_sound (L : List Pt) (M P n : ℕ) (h : ∀ j < n, hMacroOK L M P j = true) :
    ∀ j < n, ∀ c < M, ∀ x y : ℝ,
      ((hCellBox M P j c).1 : ℝ) / 2 ^ 40 ≤ x → x ≤ ((hCellBox M P j c).2.1 : ℝ) / 2 ^ 40 →
      ((hCellBox M P j c).2.2.1 : ℝ) / 2 ^ 40 ≤ y → y ≤ ((hCellBox M P j c).2.2.2 : ℝ) / 2 ^ 40 →
      ((((hCellGam M P j c : ℤ) : ℚ) / 2 ^ 32 : ℚ) : ℝ) ≤ Usig L x y - UexR x y :=
  fun j hj => hMacro_sound L M P j (h j hj)

theorem gMod_sound (L : List Pt) (mp : ℚ) (M P n : ℕ) (h : ∀ j < n, gMacroOK L mp M P j = true) :
    ∀ j < n, ∀ c < M, ∀ x y : ℝ,
      ((hCellBox M P j c).1 : ℝ) / 2 ^ 40 ≤ x → x ≤ ((hCellBox M P j c).2.1 : ℝ) / 2 ^ 40 →
      ((hCellBox M P j c).2.2.1 : ℝ) / 2 ^ 40 ≤ y → y ≤ ((hCellBox M P j c).2.2.2 : ℝ) / 2 ^ 40 →
      (mp : ℝ) ≤ gHR L x y :=
  fun j hj => gMacro_sound L mp M P j (h j hj)

/-! ### real axis (line `[0,1]`) -/

def UexAxisUp (xlo xhi : ℤ) : ℚ :=
  (1 / 8) * (if xhi = 2 ^ 40 then utA (4 * xlo - 2 ^ 42) 0
    else UbUp (4 * xlo - 2 ^ 42) (4 * xhi - 2 ^ 42) 0 0) + L2UP / 4

def sideLine (xlo xhi : ℤ) : Prop :=
  0 ≤ xlo ∧ xlo ≤ xhi ∧ xhi ≤ 2 ^ 40 ∧ (xhi = 2 ^ 40 → 3 * 2 ^ 38 ≤ xlo)

instance (xlo xhi : ℤ) : Decidable (sideLine xlo xhi) := by unfold sideLine; infer_instance

def lLB (x0 y0 : ℤ) (fd : FD) (mid : List Pt) (xlo xhi : ℤ) : ℚ :=
  sigTL x0 y0 fd xlo xhi 0 0 (sigSum xlo xhi 0 0 mid) - utB xlo xhi - UexAxisUp xlo xhi

def lMacroOK (L : List Pt) (G : ℚ) (M P j : ℕ) : Bool :=
  let b := j * (4 + 3 * M)
  let x0 := slot P b
  let y0 := slot P (b + 1)
  let i0 := (slot P (b + 2)).toNat
  let i1 := (slot P (b + 3)).toNat
  let fd := farSum x0 y0 (L.take i0 ++ L.drop i1)
  let mid := (L.drop i0).take (i1 - i0)
  decide (i0 ≤ i1) && (List.range M).all (fun c =>
    let a := b + 4 + 3 * c
    let xlo := slot P a
    let xhi := slot P (a + 1)
    decide (sideLine xlo xhi) && decide (G ≤ lLB x0 y0 fd mid xlo xhi))

theorem uexAxis_le (xlo xhi : ℤ) (hs : sideLine xlo xhi) (x : ℝ)
    (hx1 : (xlo : ℝ) / 2 ^ 40 ≤ x) (hx2 : x ≤ (xhi : ℝ) / 2 ^ 40) :
    UexR x 0 ≤ ((UexAxisUp xlo xhi : ℚ) : ℝ) := by
  obtain ⟨h0, h1, h2, h3⟩ := hs
  have h40 : (2 : ℝ) ^ 40 = 1099511627776 := by norm_num
  have hx1' : (xlo : ℝ) ≤ x * 1099511627776 := by
    have := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ 40)).1 hx1; rw [h40] at this; exact this
  have hx2' : x * 1099511627776 ≤ xhi := by
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ 40)).1 hx2; rw [h40] at this; exact this
  have hz : (4 : ℝ) * 0 = 0 := by norm_num
  unfold UexR UexAxisUp
  have hl := log2_le
  by_cases he : xhi = 2 ^ 40
  · rw [if_pos he]
    have hxl : (3 : ℤ) * 2 ^ 38 ≤ xlo := h3 he
    have hxh : (xhi : ℝ) = 1099511627776 := by rw [he]; push_cast; norm_num
    have hx1le : x ≤ 1 := by
      have : x * 1099511627776 ≤ 1099511627776 := by rw [hxh] at hx2'; exact hx2'
      linarith
    have key := utA_sound (4 * xlo - 2 ^ 42) 0 (by omega) (by omega) (by omega) (4 * x - 4)
      (by push_cast; rw [h40, div_le_iff₀ (by norm_num)]; linarith)
      (by push_cast; linarith)
    rw [hz]
    push_cast at key ⊢
    nlinarith [key, hl]
  · have hlt : xhi < 2 ^ 40 := lt_of_le_of_ne h2 he
    simp only [he, ite_false]
    have key := utau_box_le (4 * xlo - 2 ^ 42) (4 * xhi - 2 ^ 42) 0 0
      (by omega) (by omega) (le_refl _) (4 * x - 4) 0
      (by push_cast; rw [h40, div_le_iff₀ (by norm_num)]; linarith)
      (by push_cast; rw [h40, le_div_iff₀ (by norm_num)]; linarith)
      (by simp) (by simp)
    rw [hz]
    push_cast at key ⊢
    nlinarith [key, hl]

theorem lMacro_sound (L : List Pt) (G : ℚ) (M P j : ℕ) (h : lMacroOK L G M P j = true) :
    ∀ c < M, ∀ x : ℝ,
      ((realCell M P j c).1 : ℝ) / 2 ^ 40 ≤ x → x ≤ ((realCell M P j c).2.1 : ℝ) / 2 ^ 40 →
      (G : ℝ) ≤ gfun L x 0 - UexR x 0 := by
  intro c hc x h1 h2
  simp only [lMacroOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨hi, hall⟩ := h
  have hcell := hall c hc
  try simp only [Bool.and_eq_true, decide_eq_true_eq] at hcell
  obtain ⟨hside, hthr⟩ := hcell
  simp only [realCell] at h1 h2
  have hsplit := split_eq L _ _ hi
  have hS := sigTL_sound (slot P (j * (4 + 3 * M))) (slot P (j * (4 + 3 * M) + 1))
    (L.take (slot P (j * (4 + 3 * M) + 2)).toNat)
    ((L.drop (slot P (j * (4 + 3 * M) + 2)).toNat).take
      ((slot P (j * (4 + 3 * M) + 3)).toNat - (slot P (j * (4 + 3 * M) + 2)).toNat))
    (L.drop (slot P (j * (4 + 3 * M) + 3)).toNat)
    (slot P (j * (4 + 3 * M) + 4 + 3 * c)) (slot P (j * (4 + 3 * M) + 4 + 3 * c + 1)) 0 0 x 0
    h1 h2 (by simp) (by simp)
  rw [hsplit] at hS
  have hU : Utau x 0 ≤ ((utB (slot P (j * (4 + 3 * M) + 4 + 3 * c))
      (slot P (j * (4 + 3 * M) + 4 + 3 * c + 1)) : ℚ) : ℝ) :=
    utB_sound _ _ hside.1 hside.2.1 hside.2.2.1 x h1 h2
  have hE := uexAxis_le _ _ hside x h1 h2
  have hthr' : G ≤ lLB (slot P (j * (4 + 3 * M))) (slot P (j * (4 + 3 * M) + 1))
      (farSum (slot P (j * (4 + 3 * M))) (slot P (j * (4 + 3 * M) + 1))
        (L.take (slot P (j * (4 + 3 * M) + 2)).toNat ++ L.drop (slot P (j * (4 + 3 * M) + 3)).toNat))
      ((L.drop (slot P (j * (4 + 3 * M) + 2)).toNat).take
        ((slot P (j * (4 + 3 * M) + 3)).toNat - (slot P (j * (4 + 3 * M) + 2)).toNat))
      (slot P (j * (4 + 3 * M) + 4 + 3 * c)) (slot P (j * (4 + 3 * M) + 4 + 3 * c + 1)) := hthr
  have hG := (Rat.cast_le (K := ℝ)).2 hthr'
  unfold lLB at hG
  push_cast at hG
  unfold gfun
  simp only [mul_zero, add_zero]
  push_cast at hS hU hE
  linarith

end CatalanCore.Cert.SigmaHyb
