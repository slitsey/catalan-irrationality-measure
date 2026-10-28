module

public import CatalanCore.Uniform.Content.RankProducer.Block

@[expose] public section

/-!
# Loads of the killed rows and columns of a certificate assignment (lane H15)

The mass/pole loads of the global exact kernel vectors are the images of the rational loads
`rload`, `cload` of the fibre certificates.
-/

open Polynomial Finset Module Matrix CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Uniform.Content.Hybrid

namespace CatalanCore.Uniform.Content.RankProducer

section BlockSum

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {Fb : Type*} [Fintype Fb] [DecidableEq Fb] {Tr Tc : Fb → Type*}
  [∀ x, Fintype (Tr x)] [∀ x, DecidableEq (Tr x)] [∀ x, Fintype (Tc x)] [∀ x, DecidableEq (Tc x)]

/-- A row of a block matrix sums over its own fibre only. -/
lemma sum_blockRow (er : ι ≃ Σ x, Tr x) (ec : ι ≃ Σ x, Tc x) (M : ∀ x, Matrix (Tr x) (Tc x) R)
    (x : Fb) (t : Tr x) {A : Type*} [AddCommMonoid A] (g : R → ι → A) (hg : ∀ k, g 0 k = 0) :
    ∑ k, g (blockMat er ec M (er.symm ⟨x, t⟩) k) k = ∑ u : Tc x, g (M x t u) (ec.symm ⟨x, u⟩) := by
  rw [← Equiv.sum_comp ec.symm (fun k => g (blockMat er ec M (er.symm ⟨x, t⟩) k) k),
    Fintype.sum_sigma, Finset.sum_eq_single x]
  · refine Finset.sum_congr rfl fun u _ => ?_
    rw [blockMat_apply_sym]; simp
  · intro y _ hy
    refine Finset.sum_eq_zero fun u _ => ?_
    rw [blockMat_apply_sym, dif_neg (Ne.symm hy)]; exact hg _
  · simp

/-- A column of a block matrix sums over its own fibre only. -/
lemma sum_blockCol (er : ι ≃ Σ x, Tr x) (ec : ι ≃ Σ x, Tc x) (M : ∀ x, Matrix (Tr x) (Tc x) R)
    (y : Fb) (u : Tc y) {A : Type*} [AddCommMonoid A] (g : R → ι → A) (hg : ∀ k, g 0 k = 0) :
    ∑ k, g (blockMat er ec M k (ec.symm ⟨y, u⟩)) k = ∑ t : Tr y, g (M y t u) (er.symm ⟨y, t⟩) := by
  rw [← Equiv.sum_comp er.symm (fun k => g (blockMat er ec M k (ec.symm ⟨y, u⟩)) k),
    Fintype.sum_sigma, Finset.sum_eq_single y]
  · refine Finset.sum_congr rfl fun t _ => ?_
    rw [blockMat_apply_sym]; simp
  · intro x _ hx
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [blockMat_apply_sym, dif_neg hx]; exact hg _
  · simp

end BlockSum

variable {p : ℕ} [hp : Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {B : ℕ} {f e : ℕ → ℚ}

namespace FibreCert

/-- Rational mass/pole load of the left kernel vector with digit `d`. -/
def rload (c : FibreCert) (d : ℕ) : ℚ × ℚ :=
  (∑ f ∈ c.R, c.Lq d f, ∑ f ∈ c.R, c.lf f * c.Lq d f)

/-- Rational mass/pole load of the right kernel vector with digit `e`. -/
def cload (c : FibreCert) (e : ℕ) : ℚ × ℚ :=
  (∑ g ∈ c.C, c.Pq g e, ∑ g ∈ c.C, c.lf g * c.Pq g e)

end FibreCert

/-- Image of a rational pair in `𝔽_p(X)²`. -/
noncomputable def castV (p : ℕ) [Fact p.Prime] (v : ℚ × ℚ) :
    RatFunc (ZMod p) × RatFunc (ZMod p) := (rfH p (red p v.1), rfH p (red p v.2))

lemma red_sum {α : Type*} (s : Finset α) (f : α → ℚ) (h : ∀ a ∈ s, f a ∈ S p) :
    red p (∑ a ∈ s, f a) = ∑ a ∈ s, red p (f a) :=
  (Good.sum s f (fun a => red p (f a)) (fun a ha => good_red (h a ha))).eq

variable (PS : PoleSplit p B f e) (a b : ι → ℕ) (hd : DigitHyp p B a b)
  (ha : Function.Injective a) (hb : Function.Injective b)
  (cert : ZMod p → FibreCert) (hOk : ∀ x, (cert x).Ok) (hInt : ∀ x, (cert x).Integral p)
  (hReal : ∀ x, Realizes PS a b x (cert x))
  (hcard : (killRows (p := p) a cert).card = (killCols (p := p) b cert).card)

include hd ha hb hOk hInt hReal in
/-- Load of the row `i` of the global `L`: the cast of the certificate load. -/
theorem rowLoad_eq (i : ι) :
    mapPair (rfH p) (load (fun k => PS.lf (a k))
      (fun k => redQ p ((blockKernelOfCerts PS a b hd ha hb cert hOk hInt hReal hcard).L i k))) =
    castV p ((cert (a i : ZMod p)).rload (a i / p)) := by
  obtain ⟨⟨x, t⟩, rfl⟩ := (erOf a p).symm.surjective i
  obtain ⟨i0, rfl⟩ := t
  have hLf : ∀ u : TrOf a p (a i0 : ZMod p), PS.lf (a u.1) =
      red p ((cert (a i0 : ZMod p)).lf (dig a p u)) := by
    intro u
    rw [← (PS.hLf (a u.1) (hd.1 u.1)).eq, (hReal _).lf_r u.1 u.2]; rfl
  have hLfS : ∀ u : TrOf a p (a i0 : ZMod p), (cert (a i0 : ZMod p)).lf (dig a p u) ∈ S p := by
    intro u
    show (cert _).lf (a u.1 / p) ∈ S p
    rw [← (hReal _).lf_r u.1 u.2]; exact (PS.hLf (a u.1) (hd.1 u.1)).1
  have hq : ∀ u : TrOf a p (a i0 : ZMod p),
      (cert (a i0 : ZMod p)).Lq (a i0 / p) (dig a p u) ∈ S p := fun u =>
    ((hInt _).lq _ ((hReal _).r_mem i0 rfl) _ ((hReal _).r_mem u.1 u.2)).1
  have e1 : (∑ k, redQ p
      ((blockKernelOfCerts PS a b hd ha hb cert hOk hInt hReal hcard).L
        ((erOf a p).symm ⟨(a i0 : ZMod p), ⟨i0, rfl⟩⟩) k)) =
      red p (∑ f ∈ (cert (a i0 : ZMod p)).R, (cert (a i0 : ZMod p)).Lq (a i0 / p) f) := by
    have := sum_blockRow (erOf a p) (erOf a p)
      (blockKernelOfCerts PS a b hd ha hb cert hOk hInt hReal hcard).Lx
      (a i0 : ZMod p) ⟨i0, rfl⟩ (fun r _ => redQ p r) (fun _ => map_zero _)
    beta_reduce at this
    rw [BlockKernel.L, this]
    rw [red_sum _ _ (fun f hf => by
      obtain ⟨j, hj, hjd⟩ := (hReal _).r_cov f hf
      rw [← hjd]; exact hq ⟨j, hj⟩)]
    rw [← sum_fibre ha (a i0 : ZMod p) _ (hReal _).r_mem (hReal _).r_cov
      (fun f => red p ((cert (a i0 : ZMod p)).Lq (a i0 / p) f))]
    refine Finset.sum_congr rfl fun u _ => ?_
    show redQ p (liftQ p _) = _
    exact redQ_liftQ (good_red (hq u))
  have e2 : (∑ k, PS.lf (a k) * redQ p
      ((blockKernelOfCerts PS a b hd ha hb cert hOk hInt hReal hcard).L
        ((erOf a p).symm ⟨(a i0 : ZMod p), ⟨i0, rfl⟩⟩) k)) =
      red p (∑ f ∈ (cert (a i0 : ZMod p)).R, (cert (a i0 : ZMod p)).lf f *
        (cert (a i0 : ZMod p)).Lq (a i0 / p) f) := by
    have := sum_blockRow (erOf a p) (erOf a p)
      (blockKernelOfCerts PS a b hd ha hb cert hOk hInt hReal hcard).Lx
      (a i0 : ZMod p) ⟨i0, rfl⟩ (fun r k => PS.lf (a k) * redQ p r) (fun _ => by simp)
    beta_reduce at this
    rw [BlockKernel.L, this]
    rw [red_sum _ _ (fun f hf => by
      obtain ⟨j, hj, hjd⟩ := (hReal _).r_cov f hf
      rw [← hjd]; exact (S _).mul_mem (hLfS ⟨j, hj⟩) (hq ⟨j, hj⟩))]
    rw [← sum_fibre ha (a i0 : ZMod p) _ (hReal _).r_mem (hReal _).r_cov
      (fun f => red p ((cert (a i0 : ZMod p)).lf f * (cert (a i0 : ZMod p)).Lq (a i0 / p) f))]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [erOf_symm, hLf u]
    show _ * redQ p (liftQ p ((cert (a i0 : ZMod p)).Lq (a i0 / p) (dig a p u))) = _
    rw [redQ_liftQ (good_red (hq u))]
    exact (Good.mul (good_red (hLfS u)) (good_red (hq u))).eq.symm
  simp only [mapPair, load, castV, FibreCert.rload]
  rw [e1, e2]
  try rfl

end CatalanCore.Uniform.Content.RankProducer
