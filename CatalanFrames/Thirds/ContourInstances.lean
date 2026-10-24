module

public import CatalanFrames.Thirds.ContourGeneric
public import CatalanFrames.Thirds.CharZero

@[expose] public section

/-! # The two thirds frames with real contour data (supersedes `Instances.lean`)

`thirdsAc` (`s = 1/3`): `xs = 2/3`, `δ0 = 1/3`, `n0off = 1`.
`thirdsBc` (`s = 2/3`): `xs = 1/3`, `δ0 = 1/3`, `n0off = 0`.
Norm `9` for both.  `DecayOKs' sl` holds for every slope `sl ≥ 1`; in particular `sl = 5/2`
(the certificate `certS`) and `sl = 3`.
-/

open Polynomial CatalanCore CatalanCore.Rect CatalanCore.Rect.CharZeroNV

namespace CatalanFrames.Thirds

/-- `ψ(z+1) - ψ(z+1/3)`, norm `9`, contour `xs = 2/3`. -/
def thirdsAc : Frame :=
  thirdsFrame (1 / 3) 9 (2 / 3) (1 / 3) 1 (by norm_num) (by norm_num) (by norm_num)

/-- `ψ(z+1) - ψ(z+2/3)`, norm `9`, contour `xs = 1/3`. -/
def thirdsBc : Frame :=
  thirdsFrame (2 / 3) 9 (1 / 3) (1 / 3) 0 (by norm_num) (by norm_num) (by norm_num)

theorem thirdsAc_decayOKs' (sl : ℝ) (hsl : 1 ≤ sl) : thirdsAc.DecayOKs' sl :=
  thirds_decayOKs' _ _ _ _ _ _ _ _ (by norm_num) (by norm_num) 1 0 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) sl hsl
    (by push_cast; nlinarith)
    (by
      have : ⌊(2 / 3 : ℚ) - 1 / 3⌋ = 0 := by
        rw [Int.floor_eq_iff]; norm_num
      rw [this]; norm_num)
    (by
      have : ⌊(2 / 3 : ℚ) - 1⌋ = -1 := by
        rw [Int.floor_eq_iff]; norm_num
      rw [this]; norm_num)
    (by norm_num)

theorem thirdsBc_decayOKs' (sl : ℝ) (hsl : 1 ≤ sl) : thirdsBc.DecayOKs' sl :=
  thirds_decayOKs' _ _ _ _ _ _ _ _ (by norm_num) (by norm_num) 0 0 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) sl hsl
    (by push_cast; nlinarith)
    (by
      have : ⌊(1 / 3 : ℚ) - 2 / 3⌋ = -1 := by
        rw [Int.floor_eq_iff]; norm_num
      rw [this]; norm_num)
    (by
      have : ⌊(1 / 3 : ℚ) - 1⌋ = -1 := by
        rw [Int.floor_eq_iff]; norm_num
      rw [this]; norm_num)
    (by norm_num)

theorem thirdsAc_decayOKs'_52 : thirdsAc.DecayOKs' (5 / 2 : ℝ) :=
  thirdsAc_decayOKs' _ (by norm_num)

theorem thirdsBc_decayOKs'_52 : thirdsBc.DecayOKs' (5 / 2 : ℝ) :=
  thirdsBc_decayOKs' _ (by norm_num)

theorem thirdsAc_contourOK : thirdsAc.ContourOK := (thirdsAc_decayOKs'_52).contour
theorem thirdsBc_contourOK : thirdsBc.ContourOK := (thirdsBc_decayOKs'_52).contour

theorem thirdsAc_d : thirdsAc.d = 2 := rfl
theorem thirdsBc_d : thirdsBc.d = 2 := rfl
theorem thirdsAc_mu : thirdsAc.μ = ![1 / 3, 1] := rfl
theorem thirdsBc_mu : thirdsBc.μ = ![2 / 3, 1] := rfl
theorem thirdsAc_norm : thirdsAc.norm = 9 := rfl
theorem thirdsBc_norm : thirdsBc.norm = 9 := rfl

theorem thirdsAc_Delta (k : ℕ) : thirdsAc.Delta k = 1 / (k : ℚ) - 1 / ((k : ℚ) - 1 + 1 / 3) :=
  Delta_eq _ _ _ _ _ _ _ _ k

theorem thirdsAc_Dsq (k : ℕ) :
    thirdsAc.Dsq k = 1 / (k : ℚ) ^ 2 - 1 / ((k : ℚ) - 1 + 1 / 3) ^ 2 :=
  Dsq_eq _ _ _ _ _ _ _ _ k

theorem thirdsBc_Delta (k : ℕ) : thirdsBc.Delta k = 1 / (k : ℚ) - 1 / ((k : ℚ) - 1 + 2 / 3) :=
  Delta_eq _ _ _ _ _ _ _ _ k

theorem thirdsBc_Dsq (k : ℕ) :
    thirdsBc.Dsq k = 1 / (k : ℚ) ^ 2 - 1 / ((k : ℚ) - 1 + 2 / 3) ^ 2 :=
  Dsq_eq _ _ _ _ _ _ _ _ k

theorem exists_common_deletion_fullN_Ac (U : ℚ) (r m : ℕ) (hr : 1 ≤ r) :
    ∃ t : Finset (Fin r), t.card ≤ 1 ∧
      (FullN thirdsAc (fun i : {i // i ∉ t} => i.val.val)
        (fun i : Fin m => r + 2 * i.val) (fun i : Fin m => r + 2 * i.val + 1) U).det ≠ 0 :=
  exists_common_deletion_fullN_thirds _ _ _ _ 1 _ _ _ _ one_ne_zero U r m hr

theorem exists_common_deletion_fullN_Bc (U : ℚ) (r m : ℕ) (hr : 1 ≤ r) :
    ∃ t : Finset (Fin r), t.card ≤ 1 ∧
      (FullN thirdsBc (fun i : {i // i ∉ t} => i.val.val)
        (fun i : Fin m => r + 2 * i.val) (fun i : Fin m => r + 2 * i.val + 1) U).det ≠ 0 :=
  exists_common_deletion_fullN_thirds _ _ _ _ 1 _ _ _ _ one_ne_zero U r m hr

theorem thirdsAc_hasNVPinC (Adm : ℕ → ℕ → Prop) (hAdm : ∀ r, 1 ≤ r → ∃ m, Adm r m)
    (Cls : ℕ → Prop) (Bad : ℕ → ℕ → Prop) (α β : ℝ) :
    CatalanCore.HasNVPinC (commonMinorFam thirdsAc Adm 1) Cls Bad α β :=
  thirds_hasNVPinC _ _ _ _ _ _ _ _ Adm hAdm Cls Bad α β

theorem thirdsBc_hasNVPinC (Adm : ℕ → ℕ → Prop) (hAdm : ∀ r, 1 ≤ r → ∃ m, Adm r m)
    (Cls : ℕ → Prop) (Bad : ℕ → ℕ → Prop) (α β : ℝ) :
    CatalanCore.HasNVPinC (commonMinorFam thirdsBc Adm 1) Cls Bad α β :=
  thirds_hasNVPinC _ _ _ _ _ _ _ _ Adm hAdm Cls Bad α β

#print axioms thirdsAc_decayOKs'
#print axioms thirdsBc_decayOKs'
#print axioms thirdsAc_contourOK
#print axioms thirdsBc_contourOK
#print axioms exists_common_deletion_fullN_Ac
#print axioms exists_common_deletion_fullN_Bc
#print axioms thirdsAc_hasNVPinC
#print axioms thirdsBc_hasNVPinC

end CatalanFrames.Thirds
