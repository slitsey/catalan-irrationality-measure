module

public import CatalanCore.Uniform.Content.RankProducer.FibreCounts

@[expose] public section
set_option Elab.async false
namespace CatalanCore.Uniform.Content.RankProducer
open Finset CatalanCore.Uniform.Content.Hybrid
open scoped Classical
variable {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {B : ℕ} {f e : ℕ → ℚ}
variable (PS : PoleSplit p B f e) (a b : ι → ℕ) (hd : DigitHyp p B a b)
    (ha : Function.Injective a) (hb : Function.Injective b) (cert : ZMod p → FibreCert)
    (hOk : ∀ x, (cert x).Ok) (hInt : ∀ x, (cert x).Integral p)
    (hReal : ∀ x, Realizes PS a b x (cert x))
    (hcard : (killRows (p := p) a cert).card = (killCols (p := p) b cert).card)

/-- Active row residues are the image of actual killed row coordinates. -/
theorem rowFib_eq_image : rowFib PS a b hd ha hb cert hOk hInt hReal hcard =
    (killRows (p := p) a cert).image (fun i => (a i : ZMod p)) := by
  let BK := BKc PS a b hd ha hb cert hOk hInt hReal hcard
  have hs : BK.s = killRows (p := p) a cert := by
    ext i
    simp only [BK, BKc, blockKernelOfCerts, BlockKernel.s, killRows,
      Finset.mem_filter, Finset.mem_univ, true_and] <;> rfl
  change (Finset.univ : Finset BK.s).image (fun i => (erOf a p i.1).1) = _
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi, hix⟩ := Finset.mem_image.1 hx
    refine Finset.mem_image.2 ⟨i.1, ?_, hix⟩
    rw [← hs]
    exact i.2
  · intro hx
    obtain ⟨i, hi, hix⟩ := Finset.mem_image.1 hx
    have hsi : i ∈ BK.s := by rw [hs]; exact hi
    exact Finset.mem_image.2 ⟨⟨i, hsi⟩, Finset.mem_univ _, hix⟩

/-- Matching the killed columns by a permutation does not change their residue image. -/
theorem colFib_eq_image : colFib PS a b hd ha hb cert hOk hInt hReal hcard =
    (killCols (p := p) b cert).image (fun i => (b i : ZMod p)) := by
  let BK := BKc PS a b hd ha hb cert hOk hInt hReal hcard
  have hc : BK.sc = killCols (p := p) b cert := by
    ext i
    simp only [BK, BKc, blockKernelOfCerts, BlockKernel.sc, killCols,
      Finset.mem_filter, Finset.mem_univ, true_and] <;> rfl
  change (Finset.univ : Finset BK.s).image (fun i => (erOf b p (BK.perm i.1)).1) = _
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi, hix⟩ := Finset.mem_image.1 hx
    refine Finset.mem_image.2 ⟨BK.perm i.1, ?_, hix⟩
    rw [← hc]
    exact (BK.perm_mem i.1).2 i.2
  · intro hx
    obtain ⟨j, hj, hjx⟩ := Finset.mem_image.1 hx
    let i := BK.perm.symm j
    have hij : BK.perm i = j := Equiv.apply_symm_apply _ _
    have hi : i ∈ BK.s := (BK.perm_mem i).1 (by rw [hij, hc]; exact hj)
    refine Finset.mem_image.2 ⟨⟨i, hi⟩, Finset.mem_univ _, ?_⟩
    simpa only [erOf_fst, hij] using hjx

#print axioms rowFib_eq_image
#print axioms colFib_eq_image
end CatalanCore.Uniform.Content.RankProducer
