module

public import CatalanCore.Uniform.Content.UFMoments.NodeExp

@[expose] public section

/-!
# UF moments: the second-order numerator of one border node (`node_phi2`, `node_alpha_res`)

See `NodeExp`.  With `y = ℓ - d` and `x = Q⁻¹ y`:

  `(ℓ_t - σ·Q⁻¹ℓ) - d (1 - σ·Q⁻¹1) = π (G₁ - Bk + π Rem)`,
  `res Bk = B Σ_{c ≠ t̄} m(c)/(c - t̄)`,   `res (1 - σ·Q⁻¹1) = B = res (1 - Σ g)`.
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Hybrid

namespace CatalanCore.Uniform.Content.UFMoments

/-- The direction shift of a one-node moment (linear algebra). -/
theorem lin_shift {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] (M : Matrix ι ι R)
    (σ ℓ : ι → R) (d t : R) :
    (t - σ ⬝ᵥ (M *ᵥ ℓ)) - d * (1 - σ ⬝ᵥ (M *ᵥ 1)) = (t - d) - σ ⬝ᵥ (M *ᵥ fun a => ℓ a - d) := by
  have : (fun a => ℓ a - d) = ℓ - d • (1 : ι → R) := by funext a; simp
  rw [this, mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  ring

variable {p N : ℕ} [Fact p.Prime] {Fr : Frame} {ι : Type} [Fintype ι] [DecidableEq ι]

theorem isUnit_map_det (Q : Matrix ι ι (LocRing p)[X]) (hdet : phiP p Q.det ≠ 0) :
    IsUnit (Q.map (algebraMap (LocRing p)[X] (GaussLoc p))).det := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact isUnit_of_phiP_ne p hdet

/-- The fiber moment `m(c) = Σ_{c_a ≡ c} res((D⁻¹ y)_a) res(y_a)`. -/
noncomputable def fibMom (c : ι → ℕ) (Dm : Matrix ι ι (GaussLoc p)) (y : ι → GaussLoc p)
    (c' : ZMod p) : RatFunc (ZMod p) :=
  ∑ a ∈ univ.filter (fun a => colOf (p := p) c a = c'), res p ((Dm⁻¹ *ᵥ y) a) * res p (y a)

theorem node_phi2 (D : PoleData Fr p N) (c : ι → ℕ) (hc : ∀ a, c a < N)
    (Q : Matrix ι ι (LocRing p)[X])
    (hQ : ∀ a b, a ≠ b → nL p Fr * (nd p (c b) - nd p (c a)) * Q a b =
      PF p Fr (c b) - PF p Fr (c a))
    (hdet : phiP p Q.det ≠ 0) (t : ℕ) (ht : t < N) (σ : ι → (LocRing p)[X])
    (hσ : ∀ a, nL p Fr * (nd p (c a) - nd p t) * σ a = PF p Fr (c a) - PF p Fr t)
    (d G₁ : GaussLoc p)
    (hG : (ellL p Fr t - d) - (sOwn c t σ ᵥ* (Dmat c Q)⁻¹) ⬝ᵥ (fun a => ellL p Fr (c a) - d) =
      piL p * G₁) :
    ∃ Bk Rem : GaussLoc p,
      (ellL p Fr t - (fun a => algebraMap _ (GaussLoc p) (σ a)) ⬝ᵥ
          ((Q.map (algebraMap _ (GaussLoc p)))⁻¹ *ᵥ fun a => ellL p Fr (c a))) -
        d * (1 - (fun a => algebraMap _ (GaussLoc p) (σ a)) ⬝ᵥ
          ((Q.map (algebraMap _ (GaussLoc p)))⁻¹ *ᵥ 1)) =
        piL p * (G₁ - Bk + piL p * Rem) ∧
      res p Bk = res p (1 - ∑ j, (sOwn c t σ ᵥ* (Dmat c Q)⁻¹) j) *
        ∑ c' : ZMod p, if c' = ((t : ℕ) : ZMod p) then 0 else
          fibMom c (Dmat c Q) (fun a => ellL p Fr (c a) - d) c' /
            (rfH p c' - rfH p ((t : ℕ) : ZMod p)) := by
  classical
  set y : ι → GaussLoc p := fun a => ellL p Fr (c a) - d
  set Qm := Q.map (algebraMap (LocRing p)[X] (GaussLoc p))
  have hsplit := core_split D c hc Q hQ
  have hQu := isUnit_map_det Q hdet
  have hD := isUnit_Dmat_det D c hc Q hQ hdet
  set x := Qm⁻¹ *ᵥ y
  have hx : Dmat c Q *ᵥ x + piL p • (Emat p Fr c *ᵥ x) = y := by
    have h0 : Qm *ᵥ x = y := by
      show Qm *ᵥ (Qm⁻¹ *ᵥ y) = y
      rw [mulVec_mulVec, mul_nonsing_inv _ hQu, one_mulVec]
    rw [show Qm = Dmat c Q + piL p • Emat p Fr c from hsplit, add_mulVec, smul_mulVec] at h0
    exact h0
  have hDb : ∀ a b, colOf (p := p) c a ≠ colOf c b → Dmat c Q a b = 0 := by
    intro a b h; simp [Dmat, h]
  have hE0 : ∀ a b, colOf (p := p) c a = colOf c b → Emat p Fr c a b = 0 := by
    intro a b h; simp [Emat, h]
  have hE : ∀ a b, colOf (p := p) c a ≠ colOf c b → res p (Emat p Fr c a b) =
      (res p (y b) - res p (y a)) / (rfH p (colOf c b) - rfH p (colOf c a)) := by
    intro a b h
    rw [res_Emat c a b h]
    simp only [y, map_sub]
    ring
  have hs : ∀ a, colOf (p := p) c a ≠ ((t : ℕ) : ZMod p) → sOwn c t σ a = 0 := by
    intro a h; simp [sOwn, h]
  have hs'0 : ∀ a, colOf (p := p) c a = ((t : ℕ) : ZMod p) → sCross p Fr c t a = 0 := by
    intro a h; simp [sCross, h]
  have hs' : ∀ a, colOf (p := p) c a ≠ ((t : ℕ) : ZMod p) → res p (sCross p Fr c t a) =
      (res p (y a) - res p (ellL p Fr t - d)) / (rfH p (colOf c a) - rfH p ((t : ℕ) : ZMod p)) := by
    intro a h
    rw [res_sCross c t a h]
    simp only [y, map_sub]
    ring
  obtain ⟨Bk, Rem, h1, h2⟩ := phi2_expansion (piL p) (res p) (res_piL p) (rfH p) rfH_injective
    (colOf c) ((t : ℕ) : ZMod p) (Dmat c Q) (Emat p Fr c) hD hDb y (ellL p Fr t - d) hE0 hE
    (sOwn c t σ) (sCross p Fr c t) hs hs'0 hs' x hx G₁ hG
  refine ⟨Bk, Rem, ?_, h2⟩
  rw [← h1, ← node_split D c hc t ht σ hσ]
  exact lin_shift Qm⁻¹ _ _ d (ellL p Fr t)

theorem node_alpha_res (D : PoleData Fr p N) (c : ι → ℕ) (hc : ∀ a, c a < N)
    (Q : Matrix ι ι (LocRing p)[X])
    (hQ : ∀ a b, a ≠ b → nL p Fr * (nd p (c b) - nd p (c a)) * Q a b =
      PF p Fr (c b) - PF p Fr (c a))
    (hdet : phiP p Q.det ≠ 0) (t : ℕ) (ht : t < N) (σ : ι → (LocRing p)[X])
    (hσ : ∀ a, nL p Fr * (nd p (c a) - nd p t) * σ a = PF p Fr (c a) - PF p Fr t) :
    res p (1 - (fun a => algebraMap _ (GaussLoc p) (σ a)) ⬝ᵥ
        ((Q.map (algebraMap _ (GaussLoc p)))⁻¹ *ᵥ 1)) =
      res p (1 - ∑ j, (sOwn c t σ ᵥ* (Dmat c Q)⁻¹) j) := by
  set fL := algebraMap (LocRing p)[X] (GaussLoc p)
  set Qm := Q.map fL
  have hsplit := core_split D c hc Q hQ
  have hQu := isUnit_map_det Q hdet
  have hD := isUnit_Dmat_det D c hc Q hQ hdet
  set x := Qm⁻¹ *ᵥ (1 : ι → GaussLoc p)
  have hx : Dmat c Q *ᵥ x + piL p • (Emat p Fr c *ᵥ x) = 1 := by
    have h0 : Qm *ᵥ x = 1 := by
      show Qm *ᵥ (Qm⁻¹ *ᵥ 1) = 1
      rw [mulVec_mulVec, mul_nonsing_inv _ hQu, one_mulVec]
    rw [show Qm = Dmat c Q + piL p • Emat p Fr c from hsplit, add_mulVec, smul_mulVec] at h0
    exact h0
  have hmo := moment_second_order (piL p) (Dmat c Q) (Emat p Fr c) hD 1 x hx (sOwn c t σ)
    (sCross p Fr c t) 1
  rw [← node_split D c hc t ht σ hσ] at hmo
  rw [hmo]
  simp only [map_add, map_sub, map_mul, map_pow, res_piL, zero_mul, sub_zero, add_zero,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
  rw [dotProduct_mulVec, dotProduct_one]

end CatalanCore.Uniform.Content.UFMoments
