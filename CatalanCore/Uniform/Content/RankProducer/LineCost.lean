import CatalanCore.Uniform.Content.RankProducer.FibreCounts
import CatalanCore.Uniform.Content.RankProducer.Member
set_option Elab.async false
namespace CatalanCore.Uniform.Content.RankProducer
open Finset Module CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.Hybrid
open CatalanCore.Uniform.Content.Member
open scoped Classical
namespace RankMember
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable {Fr : Frame} {u q : Fin Fr.d → ℕ} {common : ι → ℕ} {xs ys : κ → ℕ}
    {T : Finset ι} {p : ℕ} [Fact p.Prime]

noncomputable def colScore (M : RankMember Fr u q common xs ys T p) : ℕ :=
  ∑ x ∈ colFib ((frameDigamma Fr u q).poleSplit M.B M.hcoef M.hpq M.hp3 M.hbd) (memberRows common xs T) (memberCols common ys T) (digitHyp_of_lt M.ha M.hb M.hB) M.hia M.hib M.cert M.hOk M.hInt M.hReal M.hcard, M.mc x

noncomputable def rowScore (M : RankMember Fr u q common xs ys T p) : ℕ :=
  ∑ x ∈ rowFib ((frameDigamma Fr u q).poleSplit M.B M.hcoef M.hpq M.hp3 M.hbd) (memberRows common xs T) (memberCols common ys T) (digitHyp_of_lt M.ha M.hb M.hB) M.hia M.hib M.cert M.hOk M.hInt M.hReal M.hcard, M.mr x

noncomputable def killCount (M : RankMember Fr u q common xs ys T p) : ℕ :=
  (killRows (p := p) (memberRows common xs T) M.cert).card

/-- The actual producer price obeys the zero/line envelope with balanced single kills. -/
theorem price_line_bound (M : RankMember Fr u q common xs ys T p)
    (hdim : finrank (RatFunc (ZMod p)) M.Vs = 1)
    (hrsmall : ∀ x, (M.cert x).kr.card ≤ 1) (hcsmall : ∀ x, (M.cert x).kc.card ≤ 1) :
    M.price + max M.killCount (M.colScore + M.rowScore) ≤ 2 * Fintype.card (T ⊕ κ) := by
  let PS := ((frameDigamma Fr u q).poleSplit M.B M.hcoef M.hpq M.hp3 M.hbd)
  let a := (memberRows common xs T)
  let b := (memberCols common ys T)
  let hd := digitHyp_of_lt M.ha M.hb M.hB
  let BK := BKc PS a b hd M.hia M.hib M.cert M.hOk M.hInt M.hReal M.hcard
  let CF := colFib PS a b hd M.hia M.hib M.cert M.hOk M.hInt M.hReal M.hcard
  let RF := rowFib PS a b hd M.hia M.hib M.cert M.hOk M.hInt M.hReal M.hcard
  let H := Fintype.card (T ⊕ κ)
  let K := M.killCount
  let C := M.colScore
  let RM := M.rowScore
  let D := ∑ x ∈ RF, (finrank (RatFunc (ZMod p)) M.Vs - M.mr x)
  have hs : BK.s.card = K := by
    have he : BK.s = killRows (p := p) a M.cert := by
      ext i
      simp only [BK, BKc, blockKernelOfCerts, BlockKernel.s, killRows,
        Finset.mem_filter, Finset.mem_univ, true_and] <;> rfl
    exact congrArg Finset.card he
  have hK : K ≤ H := Finset.card_le_univ _
  have hCF : CF.card = K := by
    have hc := colFib_card_eq_kills PS a b hd M.hia M.hib M.cert M.hOk M.hInt M.hReal M.hcard hcsmall
    exact hc.trans M.hcard.symm
  have hRF : RF.card = K :=
    rowFib_card_eq_kills PS a b hd M.hia M.hib M.cert M.hOk M.hInt M.hReal M.hcard hrsmall
  have hmc (x : ZMod p) : M.mc x ≤ 1 := by simpa only [hdim] using M.hmc2 x
  have hmr (x : ZMod p) : M.mr x ≤ 1 := by simpa only [hdim] using M.hmr2 x
  have hC : C ≤ K := by
    calc C ≤ ∑ _x ∈ CF, 1 := Finset.sum_le_sum (fun x _ => hmc x)
         _ = K := by simp only [Finset.sum_const, smul_eq_mul, mul_one, hCF]
  have hRM : RM ≤ K := by
    calc RM ≤ ∑ _x ∈ RF, 1 := Finset.sum_le_sum (fun x _ => hmr x)
         _ = K := by simp only [Finset.sum_const, smul_eq_mul, mul_one, hRF]
  have hD : D + RM = K := by
    change (∑ x ∈ RF, (finrank (RatFunc (ZMod p)) M.Vs - M.mr x)) +
      (∑ x ∈ RF, M.mr x) = K
    rw [hdim, ← Finset.sum_add_distrib]
    calc _ = ∑ _x ∈ RF, 1 := Finset.sum_congr rfl (fun x _ => Nat.sub_add_cancel (hmr x))
         _ = K := by simp only [Finset.sum_const, smul_eq_mul, mul_one, hRF]
  have hp : M.price ≤ H + (H - K) - (C - D) := by
    unfold price
    change H + (H - BK.s.card) - (_ + (C - D)) ≤ _
    rw [hs]
    exact Nat.sub_le_sub_left (Nat.le_add_left _ _) _
  change M.price + max K (C + RM) ≤ 2 * H
  omega

/-- The natural first-stage charge remains available before any line gain. -/
theorem price_le_raw (M : RankMember Fr u q common xs ys T p) :
    M.price ≤ Fintype.card (T ⊕ κ) + (Fintype.card (T ⊕ κ) - M.killCount) := by
  let PS := (frameDigamma Fr u q).poleSplit M.B M.hcoef M.hpq M.hp3 M.hbd
  let a := memberRows common xs T
  let b := memberCols common ys T
  let hd := digitHyp_of_lt M.ha M.hb M.hB
  let BK := BKc PS a b hd M.hia M.hib M.cert M.hOk M.hInt M.hReal M.hcard
  have hs : BK.s.card = M.killCount := by
    have he : BK.s = killRows (p := p) a M.cert := by
      ext i
      simp only [BK, BKc, blockKernelOfCerts, BlockKernel.s, killRows,
        Finset.mem_filter, Finset.mem_univ, true_and] <;> rfl
    exact congrArg Finset.card he
  unfold price
  change Fintype.card (T ⊕ κ) + (Fintype.card (T ⊕ κ) - BK.s.card) - _ ≤ _
  rw [hs]
  exact Nat.sub_le _ _

#print axioms price_line_bound
#print axioms price_le_raw
end RankMember
end CatalanCore.Uniform.Content.RankProducer
