import CatalanCore.Uniform.Content.RankProducer.Counts
import CatalanCore.Uniform.Content.RankProducer.Price
set_option Elab.async false
namespace CatalanCore.Uniform.Content.RankProducer
open Finset CatalanCore.Uniform.Content.Hybrid
open scoped Classical
variable {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem residue_injective_on_killRows (a : ι → ℕ) (ha : Function.Injective a)
    (cert : ZMod p → FibreCert) (hsmall : ∀ x, (cert x).kr.card ≤ 1) :
    Function.Injective (fun i : {i // i ∈ killRows (p := p) a cert} => (a i.1 : ZMod p)) := by
  intro i j h
  have hi := (Finset.mem_filter.1 i.2).2
  have hj := (Finset.mem_filter.1 j.2).2
  have hj' : a j.1 / p ∈ (cert (a i.1 : ZMod p)).kr := by simpa only [h] using hj
  have hd := (Finset.card_le_one.1 (hsmall (a i.1 : ZMod p))) _ hi _ hj'
  exact Subtype.ext (ha (node_eq_of_digit h hd))

theorem residue_injective_on_killCols (b : ι → ℕ) (hb : Function.Injective b)
    (cert : ZMod p → FibreCert) (hsmall : ∀ x, (cert x).kc.card ≤ 1) :
    Function.Injective (fun i : {i // i ∈ killCols (p := p) b cert} => (b i.1 : ZMod p)) := by
  intro i j h
  have hi := (Finset.mem_filter.1 i.2).2
  have hj := (Finset.mem_filter.1 j.2).2
  have hj' : b j.1 / p ∈ (cert (b i.1 : ZMod p)).kc := by simpa only [h] using hj
  have hd := (Finset.card_le_one.1 (hsmall (b i.1 : ZMod p))) _ hi _ hj'
  exact Subtype.ext (hb (node_eq_of_digit h hd))

variable {B : ℕ} {f e : ℕ → ℚ}
variable (PS : PoleSplit p B f e) (a b : ι → ℕ) (hd : DigitHyp p B a b)
    (ha : Function.Injective a) (hb : Function.Injective b) (cert : ZMod p → FibreCert)
    (hOk : ∀ x, (cert x).Ok) (hInt : ∀ x, (cert x).Integral p)
    (hReal : ∀ x, Realizes PS a b x (cert x))
    (hcard : (killRows (p := p) a cert).card = (killCols (p := p) b cert).card)

theorem rowFib_card_eq_kills (hsmall : ∀ x, (cert x).kr.card ≤ 1) :
    (rowFib PS a b hd ha hb cert hOk hInt hReal hcard).card =
      (killRows (p := p) a cert).card := by
  let BK := BKc PS a b hd ha hb cert hOk hInt hReal hcard
  have hs : BK.s = killRows (p := p) a cert := by
    ext i
    simp only [BK, BKc, blockKernelOfCerts, BlockKernel.s, killRows,
      Finset.mem_filter, Finset.mem_univ, true_and] <;> rfl
  change ((Finset.univ : Finset BK.s).image (fun i => (erOf a p i.1).1)).card = _
  have hinj : Function.Injective (fun i : BK.s => (erOf a p i.1).1) := by
    intro i j h
    have hri := residue_injective_on_killRows a ha cert hsmall
    have hij := @hri ⟨i.1, by rw [← hs]; exact i.2⟩
      ⟨j.1, by rw [← hs]; exact j.2⟩
      (show (a i.1 : ZMod p) = (a j.1 : ZMod p) from h)
    exact Subtype.ext (congrArg (fun z : {i // i ∈ killRows (p := p) a cert} => z.1) hij)
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_coe, hs]

theorem colFib_card_eq_kills (hsmall : ∀ x, (cert x).kc.card ≤ 1) :
    (colFib PS a b hd ha hb cert hOk hInt hReal hcard).card =
      (killCols (p := p) b cert).card := by
  let BK := BKc PS a b hd ha hb cert hOk hInt hReal hcard
  have hs : BK.s = killRows (p := p) a cert := by
    ext i
    simp only [BK, BKc, blockKernelOfCerts, BlockKernel.s, killRows,
      Finset.mem_filter, Finset.mem_univ, true_and] <;> rfl
  have hc : BK.sc = killCols (p := p) b cert := by
    ext i
    simp only [BK, BKc, blockKernelOfCerts, BlockKernel.sc, killCols,
      Finset.mem_filter, Finset.mem_univ, true_and] <;> rfl
  change ((Finset.univ : Finset BK.s).image (fun i => (erOf b p (BK.perm i.1)).1)).card = _
  have hmem (i : BK.s) : BK.perm i.1 ∈ killCols (p := p) b cert := by
    rw [← hc]
    exact (BK.perm_mem i.1).2 i.2
  have hinj : Function.Injective (fun i : BK.s => (erOf b p (BK.perm i.1)).1) := by
    intro i j h
    have hri := residue_injective_on_killCols b hb cert hsmall
    have hij := @hri ⟨BK.perm i.1, hmem i⟩ ⟨BK.perm j.1, hmem j⟩
      (show (b (BK.perm i.1) : ZMod p) = (b (BK.perm j.1) : ZMod p) from h)
    exact Subtype.ext (BK.perm.injective (congrArg (fun z : {j // j ∈ killCols (p := p) b cert} => z.1) hij))
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_coe, hs, hcard]

#print axioms rowFib_card_eq_kills
#print axioms colFib_card_eq_kills
end CatalanCore.Uniform.Content.RankProducer
