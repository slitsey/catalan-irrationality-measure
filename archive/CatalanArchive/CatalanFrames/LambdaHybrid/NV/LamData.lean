module

public import CatalanArchive.CatalanFrames.LambdaHybrid.NV.Instance
public import CatalanArchive.CatalanFrames.LambdaHybrid.NV.Entries

/-!
# The thin λ layer: `ModData lamFrame ℓ K` for `ℓ ≡ 3 (mod 4)`, `4K = ℓ + 1`

Everything specific to λ (and to the prime class `ℓ ≡ 3 mod 4`, `K = (ℓ+1)/4`, the shifts
`μ = (3/4, 1)`) is here and in `NV/Entries.lean`, which wraps the legacy `CatalanLambda` entry
lemmas:
* `t = -1/4`, `d = -1`, `κ = 1/16`, `h = cc = -G 0 0`,
* the only `ℓ`-singular node index is `K` (`4K - 1 = ℓ`).
For λ′ (`ℓ ≡ 1 mod 4`, `K = (ℓ+3)/4`) and P6 one supplies another `ModData`.
-/

@[expose] public section

open Finset Matrix CatalanCore CatalanCore.Rect CatalanFrames.Lambda

namespace CatalanArchive.CatalanFrames.LambdaHybrid.NV

variable {ℓ K : ℕ} [Fact ℓ.Prime]

/-- the legacy `G` as a sum over all high nodes of products of Cauchy columns -/
lemma Gleg_eq_sum (hKl : K ≤ ℓ) (a a' : ℕ) :
    CatalanLambda.G ℓ K a a' = ∑ n ∈ Ico K ℓ,
      (1 / ((a : ZMod ℓ) - n)) * (1 / ((a' : ZMod ℓ) - n)) := by
  rw [Finset.sum_Ico_eq_sum_range, ← Finset.sum_range_reflect]
  unfold CatalanLambda.G
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht' := Finset.mem_range.1 ht
  have key : ((K + (ℓ - K - 1 - t) : ℕ) : ZMod ℓ) = -1 - t := by
    have h : (K + (ℓ - K - 1 - t)) + 1 + t = ℓ := by omega
    have := congrArg (Nat.cast : ℕ → ZMod ℓ) h
    push_cast at this ⊢
    rw [ZMod.natCast_self] at this
    linear_combination this
  rw [key, one_div_mul_one_div]
  congr 1
  ring

lemma lh_val (u v : ZMod ℓ) : -(1 / (4 * (v - u))) = -(-(1 / 4 : ZMod ℓ) * (1 / (u - v))) := by
  simp only [one_div]
  rw [show u - v = -(v - u) by ring, inv_neg, _root_.mul_inv]
  ring

/-- **λ data.** -/
noncomputable def lamData (hlK : ℓ + 1 = 4 * K) : ModData lamFrame ℓ K where
  t := -(1 / 4)
  d := -1
  κ := 1 / 16
  h := CatalanLambda.cc ℓ K
  A := Matrix.of fun a b => ((if (a : ℕ) = b then CatalanLambda.cc ℓ K else 0) +
    CatalanLambda.G ℓ K a b) / 16
  ht := by
    have h4 := CatalanLambda.four_ne (ℓ := ℓ) hlK
    simpa using h4
  hd := by simp
  hκ := by
    have h4 := CatalanLambda.four_ne (ℓ := ℓ) hlK
    have h16 : (16 : ZMod ℓ) ≠ 0 := by
      have : (16 : ZMod ℓ) = 4 * 4 := by norm_num
      rw [this]; exact mul_ne_zero h4 h4
    simpa using h16
  htk := by
    have h4 := CatalanLambda.four_ne (ℓ := ℓ) hlK
    show (-(1 / 4 : ZMod ℓ)) * (-(1 / 4)) = -(-1) * (1 / 16)
    rw [neg_mul_neg, neg_neg, one_mul, div_mul_div_comm]
    norm_num
  low := fun a a' {e} {eb} he => by
    have := node_ll hlK a.2 a'.2 he
    simp only [Mn_eq]
    exact this
  lh := fun p q hp hq hql => by
    have := node_lh hlK hp hq hql
    simp only [Mn_eq]
    exact this.congr (lh_val (p : ZMod ℓ) (q : ZMod ℓ))
  hl := fun p q hp hpl hq => by
    have := node_hl hlK hp hpl hq
    simp only [Mn_eq]
    exact this.congr (lh_val (q : ZMod ℓ) (p : ZMod ℓ))
  hhOff := fun p q hp hpl hq hql hpq => by
    simp only [Mn_eq]
    exact node_hh_off hlK hp hpl hq hql hpq
  hhDiag := fun p hp hpl {e} {eb} he => by
    simp only [Mn_eq]
    have := node_hh_diag hlK hp hpl he
    exact this.congr (by simp)
  harm := fun a a' => by
    have hKl : K ≤ ℓ := by omega
    simp only [Matrix.of_apply, Gleg_eq_sum hKl, Fin.ext_iff]
    split_ifs <;> ring

end CatalanArchive.CatalanFrames.LambdaHybrid.NV
