module

public import CatalanCore.Uniform.Content.RankProducer.Loads

@[expose] public section

/-!
# Loads of the killed columns (lane H15)
-/

open Polynomial Finset Module Matrix CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Uniform.Content.Hybrid

namespace CatalanCore.Uniform.Content.RankProducer

variable {p : ℕ} [hp : Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {B : ℕ} {f e : ℕ → ℚ}
variable (PS : PoleSplit p B f e) (a b : ι → ℕ) (hd : DigitHyp p B a b)
  (ha : Function.Injective a) (hb : Function.Injective b)
  (cert : ZMod p → FibreCert) (hOk : ∀ x, (cert x).Ok) (hInt : ∀ x, (cert x).Integral p)
  (hReal : ∀ x, Realizes PS a b x (cert x))
  (hcard : (killRows (p := p) a cert).card = (killCols (p := p) b cert).card)

include hd ha hb hOk hInt hReal in
/-- Load of the column `l'` of the block matrix `blockdiag Px`. -/
theorem colLoad_block (l' : ι) :
    mapPair (rfH p) (load (fun l => PS.lf (b l))
      (fun l => redQ p ((blockMat (erOf b p) (erOf b p)
        (blockKernelOfCerts PS a b hd ha hb cert hOk hInt hReal hcard).Px) l l'))) =
    castV p ((cert (b l' : ZMod p)).cload (b l' / p)) := by
  obtain ⟨⟨y, u⟩, rfl⟩ := (erOf b p).symm.surjective l'
  obtain ⟨l0, rfl⟩ := u
  have hLf : ∀ t : TrOf b p (b l0 : ZMod p), PS.lf (b t.1) =
      red p ((cert (b l0 : ZMod p)).lf (dig b p t)) := by
    intro t
    rw [← (PS.hLf (b t.1) (hd.2.1 t.1)).eq, (hReal _).lf_c t.1 t.2]; rfl
  have hLfS : ∀ t : TrOf b p (b l0 : ZMod p), (cert (b l0 : ZMod p)).lf (dig b p t) ∈ S p := by
    intro t
    show (cert _).lf (b t.1 / p) ∈ S p
    rw [← (hReal _).lf_c t.1 t.2]; exact (PS.hLf (b t.1) (hd.2.1 t.1)).1
  have hq : ∀ t : TrOf b p (b l0 : ZMod p),
      (cert (b l0 : ZMod p)).Pq (dig b p t) (b l0 / p) ∈ S p := fun t =>
    ((hInt _).pq _ ((hReal _).c_mem t.1 t.2) _ ((hReal _).c_mem l0 rfl)).1
  have e1 : (∑ k, redQ p ((blockMat (erOf b p) (erOf b p)
        (blockKernelOfCerts PS a b hd ha hb cert hOk hInt hReal hcard).Px) k
        ((erOf b p).symm ⟨(b l0 : ZMod p), ⟨l0, rfl⟩⟩))) =
      red p (∑ g ∈ (cert (b l0 : ZMod p)).C, (cert (b l0 : ZMod p)).Pq g (b l0 / p)) := by
    have := sum_blockCol (erOf b p) (erOf b p)
      (blockKernelOfCerts PS a b hd ha hb cert hOk hInt hReal hcard).Px
      (b l0 : ZMod p) ⟨l0, rfl⟩ (fun r _ => redQ p r) (fun _ => map_zero _)
    beta_reduce at this
    rw [this]
    rw [red_sum _ _ (fun g hg => by
      obtain ⟨j, hj, hjd⟩ := (hReal _).c_cov g hg
      rw [← hjd]; exact hq ⟨j, hj⟩)]
    rw [← sum_fibre hb (b l0 : ZMod p) _ (hReal _).c_mem (hReal _).c_cov
      (fun g => red p ((cert (b l0 : ZMod p)).Pq g (b l0 / p)))]
    refine Finset.sum_congr rfl fun t _ => ?_
    show redQ p (liftQ p _) = _
    exact redQ_liftQ (good_red (hq t))
  have e2 : (∑ k, PS.lf (b k) * redQ p ((blockMat (erOf b p) (erOf b p)
        (blockKernelOfCerts PS a b hd ha hb cert hOk hInt hReal hcard).Px) k
        ((erOf b p).symm ⟨(b l0 : ZMod p), ⟨l0, rfl⟩⟩))) =
      red p (∑ g ∈ (cert (b l0 : ZMod p)).C, (cert (b l0 : ZMod p)).lf g *
        (cert (b l0 : ZMod p)).Pq g (b l0 / p)) := by
    have := sum_blockCol (erOf b p) (erOf b p)
      (blockKernelOfCerts PS a b hd ha hb cert hOk hInt hReal hcard).Px
      (b l0 : ZMod p) ⟨l0, rfl⟩ (fun r k => PS.lf (b k) * redQ p r) (fun _ => by simp)
    beta_reduce at this
    rw [this]
    rw [red_sum _ _ (fun g hg => by
      obtain ⟨j, hj, hjd⟩ := (hReal _).c_cov g hg
      rw [← hjd]; exact (S _).mul_mem (hLfS ⟨j, hj⟩) (hq ⟨j, hj⟩))]
    rw [← sum_fibre hb (b l0 : ZMod p) _ (hReal _).c_mem (hReal _).c_cov
      (fun g => red p ((cert (b l0 : ZMod p)).lf g * (cert (b l0 : ZMod p)).Pq g (b l0 / p)))]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [erOf_symm, hLf t]
    show _ * redQ p (liftQ p ((cert (b l0 : ZMod p)).Pq (dig b p t) (b l0 / p))) = _
    rw [redQ_liftQ (good_red (hq t))]
    exact (Good.mul (good_red (hLfS t)) (good_red (hq t))).eq.symm
  simp only [mapPair, load, castV, FibreCert.cload]
  rw [e1, e2]
  try rfl

end CatalanCore.Uniform.Content.RankProducer
