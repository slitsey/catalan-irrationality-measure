module

public import CatalanCore.Cert.SigmaP6.Taylor
public import CatalanCore.Cert.SigmaP6.Sigma

@[expose] public section

/-!
# Ray macros: the Taylor far-field check for blocks of `M` consecutive ray cells

Data format (`P` a packed `Nat`, 64-bit slots biased by `2^62`): macro `j` occupies slots
`j*(4+4M) ...`: `x0, y0, i0, i1` (centre and near window `[i0,i1)` of the sorted sigma list), then
`M` cells `xlo xhi ylo yhi` (units `2^-40`).
-/

namespace CatalanCore.Cert.SigmaP6

open CatalanLambda.Cert

def slot (P i : ℕ) : ℤ := (((P >>> (64 * i)) % 2 ^ 64 : ℕ) : ℤ) - 2 ^ 62

def cellBox (M P j c : ℕ) : ℤ × ℤ × ℤ × ℤ :=
  let a := j * (4 + 4 * M) + 4 + 4 * c
  (slot P a, slot P (a + 1), slot P (a + 2), slot P (a + 3))

def rayMacroOK (mp : ℚ) (M P j : ℕ) : Bool :=
  let b := j * (4 + 4 * M)
  let x0 := slot P b
  let y0 := slot P (b + 1)
  let i0 := (slot P (b + 2)).toNat
  let i1 := (slot P (b + 3)).toNat
  let fd := farSum x0 y0 (sigD.take i0 ++ sigD.drop i1)
  let mid := (sigD.drop i0).take (i1 - i0)
  decide (i0 ≤ i1) && (List.range M).all (fun c =>
    let a := b + 4 + 4 * c
    let xlo := slot P a
    let xhi := slot P (a + 1)
    let ylo := slot P (a + 2)
    let yhi := slot P (a + 3)
    decide (xhi < 0 ∧ xlo ≤ xhi ∧ 0 ≤ ylo) &&
      decide (mp ≤ boxLBg (sigTL x0 y0 fd xlo xhi ylo yhi (sigSum xlo xhi ylo yhi mid)) xlo xhi ylo yhi))

lemma split_eq {α : Type _} (l : List α) (i0 i1 : ℕ) (h : i0 ≤ i1) :
    l.take i0 ++ (l.drop i0).take (i1 - i0) ++ l.drop i1 = l := by
  have h1 : (l.drop i0).take (i1 - i0) ++ (l.drop i0).drop (i1 - i0) = l.drop i0 := List.take_append_drop _ _
  have h2 : (l.drop i0).drop (i1 - i0) = l.drop i1 := by
    rw [List.drop_drop]; congr 1; omega
  rw [h2] at h1
  rw [List.append_assoc, h1, List.take_append_drop]

theorem rayMacro_sound (mp : ℚ) (M P j : ℕ) (h : rayMacroOK mp M P j = true) :
    ∀ c < M, ∀ x y : ℝ,
      ((cellBox M P j c).1 : ℝ) / 2 ^ 40 ≤ x → x ≤ ((cellBox M P j c).2.1 : ℝ) / 2 ^ 40 →
      ((cellBox M P j c).2.2.1 : ℝ) / 2 ^ 40 ≤ y → y ≤ ((cellBox M P j c).2.2.2 : ℝ) / 2 ^ 40 →
      (mp : ℝ) ≤ gfun sigD x y := by
  intro c hc x y h1 h2 h3 h4
  simp only [rayMacroOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨hi, hall⟩ := h
  have hcell := hall c hc
  try simp only [Bool.and_eq_true, decide_eq_true_eq] at hcell
  obtain ⟨⟨hs1, hs2, hs3⟩, hmp⟩ := hcell
  simp only [cellBox] at h1 h2 h3 h4 ⊢
  have hsplit := split_eq sigD _ _ hi
  have hS := sigTL_sound (slot P (j * (4 + 4 * M))) (slot P (j * (4 + 4 * M) + 1))
    (sigD.take (slot P (j * (4 + 4 * M) + 2)).toNat)
    ((sigD.drop (slot P (j * (4 + 4 * M) + 2)).toNat).take
      ((slot P (j * (4 + 4 * M) + 3)).toNat - (slot P (j * (4 + 4 * M) + 2)).toNat))
    (sigD.drop (slot P (j * (4 + 4 * M) + 3)).toNat)
    _ _ _ _ x y h1 h2 h3 h4
  rw [hsplit] at hS
  exact box_sound_g sigD _ mp _ _ _ _ hs1 hs2 hs3 hmp x y h1 h2 h3 h4 hS

def MPRAY : ℚ := 1883395 / 1000000

/-- assemble chunked theorems `∀ k < ch, ∀ j<4, ok (4k+j)` into `∀ j < 4*ch, ok j`. -/
theorem chunks_all (f : ℕ → Bool) (ch : ℕ)
    (hc : ∀ k < ch, (List.range 4).all (fun j => f (4 * k + j)) = true) :
    ∀ j < 4 * ch, f j = true := by
  intro j hj
  have h := hc (j / 4) (by omega)
  have := List.all_eq_true.mp h (j % 4) (List.mem_range.mpr (by omega))
  have e : 4 * (j / 4) + j % 4 = j := by omega
  rwa [e] at this

/-- Soundness of a whole module of `n` macros. -/
theorem rayMod_sound (mp : ℚ) (M P n : ℕ) (h : ∀ j < n, rayMacroOK mp M P j = true) :
    ∀ j < n, ∀ c < M, ∀ x y : ℝ,
      ((cellBox M P j c).1 : ℝ) / 2 ^ 40 ≤ x → x ≤ ((cellBox M P j c).2.1 : ℝ) / 2 ^ 40 →
      ((cellBox M P j c).2.2.1 : ℝ) / 2 ^ 40 ≤ y → y ≤ ((cellBox M P j c).2.2.2 : ℝ) / 2 ^ 40 →
      (mp : ℝ) ≤ gfun sigD x y :=
  fun j hj => rayMacro_sound mp M P j (h j hj)

end CatalanCore.Cert.SigmaP6
