module

public import CatalanFrames.LambdaMirrorHybrid.MirEntries
public import CatalanFrames.LambdaHybrid.NV.LamData

/-!
# The thin mirror layer: `ModData mirFrame ℓ K` for `ℓ ≡ 1 (mod 4)`, `4K = ℓ + 3`

`t = 1/4`, `d = 1`, `κ = -1/16`, `h = cc ℓ K`, `A = -(δ·cc + G)/16`.
-/

@[expose] public section

open Finset Matrix CatalanCore CatalanFrames.LambdaMirror CatalanFrames.LambdaHybrid.NV

namespace CatalanFrames.LambdaMirrorHybrid

variable {ℓ K : ℕ} [Fact ℓ.Prime]

lemma mlh_val (u v : ZMod ℓ) : 1 / (4 * (v - u)) = -((1 / 4 : ZMod ℓ) * (1 / (u - v))) := by
  simp only [one_div]
  rw [show u - v = -(v - u) by ring, inv_neg, _root_.mul_inv]
  ring

/-- **Mirror data.** -/
noncomputable def mirData (hlK : ℓ + 3 = 4 * K) : ModData mirFrame ℓ K where
  t := 1 / 4
  d := 1
  κ := -(1 / 16)
  h := CatalanLambda.cc ℓ K
  A := Matrix.of fun a b => (-((if (a : ℕ) = b then CatalanLambda.cc ℓ K else 0) +
    CatalanLambda.G ℓ K a b)) / 16
  ht := by
    have h4 := CatalanLambda.Mirror.four_ne (ℓ := ℓ) hlK
    simpa using h4
  hd := by simp
  hκ := by
    have h4 := CatalanLambda.Mirror.four_ne (ℓ := ℓ) hlK
    have h16 : (16 : ZMod ℓ) ≠ 0 := by
      have : (16 : ZMod ℓ) = 4 * 4 := by norm_num
      rw [this]; exact mul_ne_zero h4 h4
    simpa using h16
  htk := by
    show (1 / 4 : ZMod ℓ) * (1 / 4) = -1 * -(1 / 16)
    rw [div_mul_div_comm]
    norm_num
  low := fun a a' {e} {eb} he => by
    have := mnode_ll hlK a.2 a'.2 he
    simp only [Mn_eq]
    exact this
  lh := fun p q hp hq hql => by
    have := mnode_lh hlK hp hq hql
    simp only [Mn_eq]
    exact this.congr (mlh_val (p : ZMod ℓ) (q : ZMod ℓ))
  hl := fun p q hp hpl hq => by
    have := mnode_hl hlK hp hpl hq
    simp only [Mn_eq]
    exact this.congr (mlh_val (q : ZMod ℓ) (p : ZMod ℓ))
  hhOff := fun p q hp hpl hq hql hpq => by
    simp only [Mn_eq]
    exact mnode_hh_off hlK hp hpl hq hql hpq
  hhDiag := fun p hp hpl {e} {eb} he => by
    simp only [Mn_eq]
    have := mnode_hh_diag hlK hp hpl he
    exact this.congr (by simp)
  harm := fun a a' => by
    have hKl : K ≤ ℓ := by omega
    simp only [Matrix.of_apply, Gleg_eq_sum hKl, Fin.ext_iff]
    split_ifs <;> ring

end CatalanFrames.LambdaMirrorHybrid
