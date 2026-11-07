module

public import CatalanCore.Uniform.Content.BankShared.KTerm.Bundle
public import CatalanCore.Uniform.Content.BankShared.TwoTerm.Trop
public import CatalanCore.Arith.Hybrid.D1Exact

@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 1600000

/-! # The tropical bridge over a pole bundle (wave H1)

For a `KBundle B` (a frame with poles on `p ∣ k`, `p ∣ 3k - ρ`, `p ∣ 2k - 1`, `L = 3`), at a prime `p ≥ 5` with
`3 N < p²` every member of the alternating family is `p ^ tropVal (HW lev p r m)`-integral for the instance
`B.inst r m` of the scale (`gle_trop`; the instance depends on `(r, m)`, so the uniform bridge `T_gle` of
`TwoTerm.Trop` does not apply), `p ^ tropExp`-integral (`gle_tropExp`), and then the level-free prices `2 (r + m)`
(`gle_D1`) and `2 r + 2 m - dist (m, p ℤ)` (`gle_D1x`).  These are the generic bodies of the `chi_{-3}` lemmas
`p6_gle_trop`, `p6_gle_tropExp` and the branches `D1`, `D1x`. -/

namespace CatalanCore.Uniform.Content.BankShared.KTerm
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.BankShared
  CatalanCore.Uniform.Content.BankShared.TwoTerm CatalanCore.Uniform.Content.BankShared.Check
  CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanFrames.HybCommon CatalanFrames.HybGen CatalanCore.Rect

namespace KBundle

/-- **The tropical exponent bridge at `B.inst r m`.** -/
theorem gle_tropExp (B : KBundle) (c : ℚ) (hc : 0 < c) (depth : ℕ)
    (i : ((altGeom c hc).family B.Fr depth).ι) (hr : i.1 % 2 = 0) (p : ℕ) [Fact p.Prime] :
    GLE p (tropExp (B.inst i.1 ((altGeom c hc).borderSize i.1)) i.1 ((altGeom c hc).borderSize i.1) p)
      (((altGeom c hc).family B.Fr depth).Q i) := by
  obtain ⟨r, S⟩ := i
  haveI := B.diagOK r ((altGeom c hc).borderSize r)
  have hQ := altGeom_member_commonMinor c hc B.Fr depth hr S
  have hG0 := commonMinorPoly_gle (B.inst r ((altGeom c hc).borderSize r)) p r ((altGeom c hc).borderSize r)
    (retainedFin (altGeom_hybShape c hc hr) S)
  exact hQ ▸ hG0

/-- **The tropical bridge at the instance `B.inst r m`.** -/
theorem gle_trop (B : KBundle) (c : ℚ) (hc : 0 < c) (depth : ℕ)
    (i : ((altGeom c hc).family B.Fr depth).ι)
    (hr : i.1 % 2 = 0) (hr1 : 1 ≤ i.1) (p : ℕ) [hp : Fact p.Prime] (h5 : 5 ≤ p)
    (hsq : 3 * (i.1 + 2 * (altGeom c hc).borderSize i.1) < p * p) :
    GLE p (tropVal (HW (B.inst i.1 ((altGeom c hc).borderSize i.1)).lev p i.1
      ((altGeom c hc).borderSize i.1))) (((altGeom c hc).family B.Fr depth).Q i) := by
  obtain ⟨r, S⟩ := i
  set m := (altGeom c hc).borderSize r with hm
  haveI := B.diagOK r m
  have hQ := altGeom_member_commonMinor c hc B.Fr depth hr S
  have hG0 := commonMinorPoly_gle (B.inst r m) p r m (retainedFin (altGeom_hybShape c hc hr) S)
  have hG : GLE p (tropExp (B.inst r m) r m p) (((altGeom c hc).family B.Fr depth).Q ⟨r, S⟩) := hQ ▸ hG0
  have hbad : p ∉ (B.inst r m).cd.bad := by
    intro hb
    have := (B.badInfo r m).bad_le p hb
    omega
  have hcnt : cntG (B.inst r m) r m p = 0 := by
    apply cntG_zero _ _ _ _ hp.out
    rw [(B.badInfo r m).L_eq, pow_two]
    exact hsq
  have hle := tropExp_le_good (B.inst r m) r m p hr1 hp.out hbad
  rw [hcnt] at hle
  simp only [Nat.cast_zero, mul_zero, zero_add] at hle
  have hle' : tropExp (B.inst r m) r m p ≤ tropVal (HW (B.inst r m).lev p r m) := by
    exact_mod_cast hle
  exact hG.mono hle'

/-- **`D1`**: the level-free price `2 (r + m)`. -/
theorem gle_D1 (B : KBundle) (c : ℚ) (hc : 0 < c) (depth : ℕ)
    (i : ((altGeom c hc).family B.Fr depth).ι)
    (hr : i.1 % 2 = 0) (hr1 : 1 ≤ i.1) (p : ℕ) [hp : Fact p.Prime] (h5 : 5 ≤ p)
    (hsq : 3 * (i.1 + 2 * (altGeom c hc).borderSize i.1) < p * p) :
    GLE p (2 * (i.1 + (altGeom c hc).borderSize i.1)) (((altGeom c hc).family B.Fr depth).Q i) :=
  (B.gle_trop c hc depth i hr hr1 p h5 hsq).mono (XGm_D1 _ _ _ _)

/-- **`D1x`**: the exact price `2 r + 2 m - dist (m, p ℤ)` at an odd prime. -/
theorem gle_D1x (B : KBundle) (c : ℚ) (hc : 0 < c) (depth : ℕ)
    (i : ((altGeom c hc).family B.Fr depth).ι)
    (hr : i.1 % 2 = 0) (hr1 : 1 ≤ i.1) (p : ℕ) [hp : Fact p.Prime] (h5 : 5 ≤ p)
    (hsq : 3 * (i.1 + 2 * (altGeom c hc).borderSize i.1) < p * p) (hp2 : p % 2 = 1) :
    GLE p (2 * i.1 + 2 * (altGeom c hc).borderSize i.1 -
        min ((altGeom c hc).borderSize i.1 % p) (p - (altGeom c hc).borderSize i.1 % p))
      (((altGeom c hc).family B.Fr depth).Q i) :=
  (B.gle_trop c hc depth i hr hr1 p h5 hsq).mono
    (val_D1x (lev := (B.inst i.1 ((altGeom c hc).borderSize i.1)).lev) p i.1 hp2 hp.out.pos _)

end KBundle

end CatalanCore.Uniform.Content.BankShared.KTerm
