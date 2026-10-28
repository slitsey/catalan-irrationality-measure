module

public import CatalanCore.Uniform.Content.RankProducer.Kernel

@[expose] public section

/-!
# The block kernel of a certificate assignment (lane H15)
-/

open Polynomial Finset Module Matrix CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Uniform.Content.Hybrid

namespace CatalanCore.Uniform.Content.RankProducer

variable {p : ℕ} [hp : Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {B : ℕ} {f e : ℕ → ℚ}

/-- Killed rows of a certificate assignment, as indices. -/
def killRows (a : ι → ℕ) (cert : ZMod p → FibreCert) : Finset ι :=
  Finset.univ.filter fun i => a i / p ∈ (cert (a i : ZMod p)).kr

def killCols (b : ι → ℕ) (cert : ZMod p → FibreCert) : Finset ι :=
  Finset.univ.filter fun j => b j / p ∈ (cert (b j : ZMod p)).kc

/-- **Block kernel from certificates.** -/
noncomputable def blockKernelOfCerts (PS : PoleSplit p B f e) (a b : ι → ℕ)
    (hd : DigitHyp p B a b) (ha : Function.Injective a) (hb : Function.Injective b)
    (cert : ZMod p → FibreCert) (hOk : ∀ x, (cert x).Ok) (hInt : ∀ x, (cert x).Integral p)
    (hReal : ∀ x, Realizes PS a b x (cert x))
    (hcard : (killRows (p := p) a cert).card = (killCols (p := p) b cert).card) :
    BlockKernel p (erOf a p) (erOf b p) (PS.K a b) where
  Lx x := locMat (p := p) (dig a p (x := x)) (cert x).Lq
  Lx' x := locMat (p := p) (dig a p (x := x)) (cert x).Lq'
  Px x := locMat (p := p) (dig b p (x := x)) (cert x).Pq
  Px' x := locMat (p := p) (dig b p (x := x)) (cert x).Pq'
  hLx x := locMat_mul_inv _ (cert x).R (dig_inj ha x)
    (fun d => ⟨fun hd' => by
      obtain ⟨i, hi, hid⟩ := (hReal x).r_cov d hd'
      exact ⟨⟨i, hi⟩, hid⟩, fun ⟨l, hl⟩ => by rw [← hl]; exact (hReal x).r_mem l.1 l.2⟩)
    _ _ (fun d hd e he => ((hInt x).lq d hd e he).1) (fun d hd e he => ((hInt x).lq d hd e he).2)
    (hOk x).hLL
  hPx x := locMat_mul_inv _ (cert x).C (dig_inj hb x)
    (fun d => ⟨fun hd' => by
      obtain ⟨i, hi, hid⟩ := (hReal x).c_cov d hd'
      exact ⟨⟨i, hi⟩, hid⟩, fun ⟨l, hl⟩ => by rw [← hl]; exact (hReal x).c_mem l.1 l.2⟩)
    _ _ (fun d hd e he => ((hInt x).pq d hd e he).1) (fun d hd e he => ((hInt x).pq d hd e he).2)
    (hOk x).hPP
  kr x := Finset.univ.filter fun t => dig a p t ∈ (cert x).kr
  kc x := Finset.univ.filter fun t => dig b p t ∈ (cert x).kc
  hrow x t u ht := by
    rw [triple_entry hd ha hb (hReal x) (hInt x) t u]
    have := (hOk x).hrow (dig a p t) (Finset.mem_filter.1 ht).2 (dig b p u)
      ((hReal x).c_mem u.1 u.2)
    rw [this, liftQ_zero]
  hcol x t u hu := by
    rw [triple_entry hd ha hb (hReal x) (hInt x) t u]
    have := (hOk x).hcol (dig a p t) ((hReal x).r_mem t.1 t.2) (dig b p u)
      (Finset.mem_filter.1 hu).2
    rw [this, liftQ_zero]
  hcross i j h := PS.hK_cross i j (by simpa [erOf_fst] using h)
  hcard := by
    refine Eq.trans (congrArg Finset.card ?_) (hcard.trans (congrArg Finset.card ?_))
    · ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, killRows]
      exact Iff.rfl
    · ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, killCols]
      exact Iff.rfl

end CatalanCore.Uniform.Content.RankProducer
