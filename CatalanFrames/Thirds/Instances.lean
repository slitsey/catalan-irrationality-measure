module

public import CatalanFrames.Thirds.CharZero

@[expose] public section

/-! # The two thirds frames, `s = 1/3` and `s = 2/3`, normalisation `9/2`

Contour data `xs = 1/2`, `δ0 = 1/6` (distance from `1/2` to `1/3`, `2/3`, `1` mod 1) and
`n0off = 0` are provisional placeholders for M1's contour work; nothing here uses them.
-/

open Polynomial CatalanCore CatalanCore.Rect CatalanCore.Rect.CharZeroNV

namespace CatalanFrames.Thirds

/-- `ψ(z+1) - ψ(z+1/3)`, norm `9/2`. -/
def thirdsA : Frame :=
  thirdsFrame (1 / 3) (9 / 2) (1 / 2) (1 / 6) 0 (by norm_num) (by norm_num) (by norm_num)

/-- `ψ(z+1) - ψ(z+2/3)`, norm `9/2`. -/
def thirdsB : Frame :=
  thirdsFrame (2 / 3) (9 / 2) (1 / 2) (1 / 6) 0 (by norm_num) (by norm_num) (by norm_num)

theorem thirdsA_mu : thirdsA.μ = ![1 / 3, 1] := rfl
theorem thirdsB_mu : thirdsB.μ = ![2 / 3, 1] := rfl
theorem thirdsA_w : thirdsA.w = ![-1, 1] := rfl
theorem thirdsA_norm : thirdsA.norm = 9 / 2 := rfl
theorem thirdsB_norm : thirdsB.norm = 9 / 2 := rfl

theorem thirdsA_Delta (k : ℕ) : thirdsA.Delta k = 1 / (k : ℚ) - 1 / ((k : ℚ) - 1 + 1 / 3) :=
  Delta_eq _ _ _ _ _ _ _ _ k

theorem thirdsA_Dsq (k : ℕ) :
    thirdsA.Dsq k = 1 / (k : ℚ) ^ 2 - 1 / ((k : ℚ) - 1 + 1 / 3) ^ 2 :=
  Dsq_eq _ _ _ _ _ _ _ _ k

theorem thirdsB_Delta (k : ℕ) : thirdsB.Delta k = 1 / (k : ℚ) - 1 / ((k : ℚ) - 1 + 2 / 3) :=
  Delta_eq _ _ _ _ _ _ _ _ k

theorem thirdsB_Dsq (k : ℕ) :
    thirdsB.Dsq k = 1 / (k : ℚ) ^ 2 - 1 / ((k : ℚ) - 1 + 2 / 3) ^ 2 :=
  Dsq_eq _ _ _ _ _ _ _ _ k

theorem exists_common_deletion_fullN_A (U : ℚ) (r m : ℕ) (hr : 1 ≤ r) :
    ∃ t : Finset (Fin r), t.card ≤ 1 ∧
      (FullN thirdsA (fun i : {i // i ∉ t} => i.val.val)
        (fun i : Fin m => r + 2 * i.val) (fun i : Fin m => r + 2 * i.val + 1) U).det ≠ 0 :=
  exists_common_deletion_fullN_thirds _ _ _ _ 1 _ _ _ _ one_ne_zero U r m hr

theorem exists_common_deletion_fullN_B (U : ℚ) (r m : ℕ) (hr : 1 ≤ r) :
    ∃ t : Finset (Fin r), t.card ≤ 1 ∧
      (FullN thirdsB (fun i : {i // i ∉ t} => i.val.val)
        (fun i : Fin m => r + 2 * i.val) (fun i : Fin m => r + 2 * i.val + 1) U).det ≠ 0 :=
  exists_common_deletion_fullN_thirds _ _ _ _ 1 _ _ _ _ one_ne_zero U r m hr

theorem thirdsA_hasNVPinC (Adm : ℕ → ℕ → Prop) (hAdm : ∀ r, 1 ≤ r → ∃ m, Adm r m)
    (Cls : ℕ → Prop) (Bad : ℕ → ℕ → Prop) (α β : ℝ) :
    CatalanCore.HasNVPinC (commonMinorFam thirdsA Adm 1) Cls Bad α β :=
  thirds_hasNVPinC _ _ _ _ _ _ _ _ Adm hAdm Cls Bad α β

theorem thirdsB_hasNVPinC (Adm : ℕ → ℕ → Prop) (hAdm : ∀ r, 1 ≤ r → ∃ m, Adm r m)
    (Cls : ℕ → Prop) (Bad : ℕ → ℕ → Prop) (α β : ℝ) :
    CatalanCore.HasNVPinC (commonMinorFam thirdsB Adm 1) Cls Bad α β :=
  thirds_hasNVPinC _ _ _ _ _ _ _ _ Adm hAdm Cls Bad α β

#print axioms Delta_eq
#print axioms Dsq_eq
#print axioms exists_common_deletion_fullN_A
#print axioms exists_common_deletion_fullN_B
#print axioms thirdsA_hasNVPinC
#print axioms thirdsB_hasNVPinC

end CatalanFrames.Thirds
