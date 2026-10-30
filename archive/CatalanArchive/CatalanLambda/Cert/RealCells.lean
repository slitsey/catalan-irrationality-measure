module

public import CatalanLambda.Cert.SegLine

@[expose] public section

/-!
# Real-axis macros: blocks of `M` consecutive cells `[xlo,xhi]/2^40` on the real line.

Data format (packed 64-bit slots biased by `2^62`): macro `j` occupies `j*(4+3M) ...`:
`x0, y0, i0, i1`, then `M` cells `xlo xhi γ` (γ in units `2^-32`, used only in segment mode).
-/

namespace CatalanLambda.Cert

def realLB (x0 y0 : ℤ) (fd : FD) (mid : List Pt) (xlo xhi : ℤ) : ℚ :=
  sigTL x0 y0 fd xlo xhi 0 0 (sigSum xlo xhi 0 0 mid) - (if xhi ≤ 0 then utA xlo xhi else utB xlo xhi)

def sideReal (xlo xhi : ℤ) : Prop :=
  xlo ≤ xhi ∧ ((xhi ≤ 0 ∧ -(2 ^ 40 : ℤ) ≤ xlo) ∨ (0 ≤ xlo ∧ xhi ≤ 2 ^ 40))

instance (xlo xhi : ℤ) : Decidable (sideReal xlo xhi) := by unfold sideReal; infer_instance

def realCell (M P j c : ℕ) : ℤ × ℤ × ℤ :=
  let a := j * (4 + 3 * M) + 4 + 3 * c
  (slot P a, slot P (a + 1), slot P (a + 2))

/-- threshold of cell `c` of macro `j`: `γ/2^32` in segment mode, the constant `G` otherwise. -/
def realThr (mode : Bool) (G : ℚ) (M P j c : ℕ) : ℚ :=
  if mode then ((realCell M P j c).2.2 : ℚ) / 2 ^ 32 else G

def realMacroOK (mode : Bool) (G : ℚ) (M P j : ℕ) : Bool :=
  let b := j * (4 + 3 * M)
  let x0 := slot P b
  let y0 := slot P (b + 1)
  let i0 := (slot P (b + 2)).toNat
  let i1 := (slot P (b + 3)).toNat
  let fd := farSum x0 y0 (sigmaS.take i0 ++ sigmaS.drop i1)
  let mid := (sigmaS.drop i0).take (i1 - i0)
  decide (i0 ≤ i1) && (List.range M).all (fun c =>
    let a := b + 4 + 3 * c
    let xlo := slot P a
    let xhi := slot P (a + 1)
    let gam := slot P (a + 2)
    decide (sideReal xlo xhi) &&
      decide ((if mode then (gam : ℚ) / 2 ^ 32 else G) ≤ realLB x0 y0 fd mid xlo xhi))

theorem realLB_sound (x0 y0 : ℤ) (pre mid suf : List Pt) (xlo xhi : ℤ) (hside : sideReal xlo xhi)
    (x : ℝ) (h1 : (xlo : ℝ) / 2 ^ 40 ≤ x) (h2 : x ≤ (xhi : ℝ) / 2 ^ 40) :
    ((realLB x0 y0 (farSum x0 y0 (pre ++ suf)) mid xlo xhi : ℚ) : ℝ) ≤ gfun (pre ++ mid ++ suf) x 0 := by
  have hS := sigTL_sound x0 y0 pre mid suf xlo xhi 0 0 x 0 h1 h2 (by simp) (by simp)
  obtain ⟨hle, hcases⟩ := hside
  have hU : Utau x 0 ≤ ((if xhi ≤ 0 then utA xlo xhi else utB xlo xhi : ℚ) : ℝ) := by
    split_ifs with hx
    · exact utA_sound _ _ hx (by rcases hcases with ⟨_, h⟩ | ⟨h, h'⟩ <;> omega) hle x h1 h2
    · exact utB_sound _ _ (by rcases hcases with ⟨h, _⟩ | ⟨h, h'⟩ <;> omega) hle
        (by rcases hcases with ⟨h, _⟩ | ⟨h, h'⟩ <;> omega) x h1 h2
  unfold realLB gfun
  push_cast
  simp only [mul_zero, add_zero]
  push_cast at hS
  linarith

theorem realMacro_sound (mode : Bool) (G : ℚ) (M P j : ℕ) (h : realMacroOK mode G M P j = true) :
    ∀ c < M, ∀ x : ℝ,
      ((realCell M P j c).1 : ℝ) / 2 ^ 40 ≤ x → x ≤ ((realCell M P j c).2.1 : ℝ) / 2 ^ 40 →
      ((realThr mode G M P j c : ℚ) : ℝ) ≤ gfun sigmaS x 0 := by
  intro c hc x h1 h2
  simp only [realMacroOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨hi, hall⟩ := h
  have hcell := hall c hc
  try simp only [Bool.and_eq_true, decide_eq_true_eq] at hcell
  obtain ⟨hside, hthr⟩ := hcell
  have hsplit := split_eq sigmaS _ _ hi
  have key := realLB_sound (slot P (j * (4 + 3 * M))) (slot P (j * (4 + 3 * M) + 1))
    (sigmaS.take (slot P (j * (4 + 3 * M) + 2)).toNat)
    ((sigmaS.drop (slot P (j * (4 + 3 * M) + 2)).toNat).take
      ((slot P (j * (4 + 3 * M) + 3)).toNat - (slot P (j * (4 + 3 * M) + 2)).toNat))
    (sigmaS.drop (slot P (j * (4 + 3 * M) + 3)).toNat)
    (slot P (j * (4 + 3 * M) + 4 + 3 * c)) (slot P (j * (4 + 3 * M) + 4 + 3 * c + 1)) hside x h1 h2
  rw [hsplit] at key
  have hthr' : realThr mode G M P j c ≤ realLB (slot P (j * (4 + 3 * M))) (slot P (j * (4 + 3 * M) + 1))
      (farSum (slot P (j * (4 + 3 * M))) (slot P (j * (4 + 3 * M) + 1))
        (sigmaS.take (slot P (j * (4 + 3 * M) + 2)).toNat ++ sigmaS.drop (slot P (j * (4 + 3 * M) + 3)).toNat))
      ((sigmaS.drop (slot P (j * (4 + 3 * M) + 2)).toNat).take
        ((slot P (j * (4 + 3 * M) + 3)).toNat - (slot P (j * (4 + 3 * M) + 2)).toNat))
      (slot P (j * (4 + 3 * M) + 4 + 3 * c)) (slot P (j * (4 + 3 * M) + 4 + 3 * c + 1)) := by
    simpa [realThr, realCell] using hthr
  exact le_trans (by exact_mod_cast hthr') key

end CatalanLambda.Cert
