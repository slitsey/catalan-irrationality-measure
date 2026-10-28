module

public import CatalanCore.Uniform.Content.UFMoments.NodePhi

@[expose] public section

/-!
# UF moments: the second-order function `Φ` of one border node

From the adjugate moments of a node (`momA = det Q - σ adj 1`, `momB = π (det Q · pF(t) - σ adj pF)`)
and a direction `d` with own-fiber moment `G₀ = π G₁`, `node_bridge` produces `Φ ∈ GaussLoc p` with

  `momB = momA (π u d + π² Φ)`,   `res Φ = res u · (res G₁ / B - Σ_{c ≠ t̄} m(c)/(c - t̄))`,

`u = norm`, `B = res(1 - Σ g) ≠ 0`.  This is the input of `hnum_of_local`.
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Hybrid

namespace CatalanCore.Uniform.Content.UFMoments

section Generic

variable {S R : Type*} [CommRing S] [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem map_adjugate_apply (f : S →+* R) (Q : Matrix ι ι S) (i k : ι) :
    f (Q.adjugate i k) = (Q.map f).adjugate i k := by
  have h := congrFun (congrFun (RingHom.map_adjugate f Q) i) k
  rw [RingHom.mapMatrix_apply] at h
  exact h

theorem map_det' (f : S →+* R) (Q : Matrix ι ι S) : f Q.det = (Q.map f).det := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]

theorem lin_scale (M : Matrix ι ι R) (σ ℓ : ι → R) (u : R) :
    σ ⬝ᵥ (M *ᵥ fun a => u * ℓ a) = u * (σ ⬝ᵥ (M *ᵥ ℓ)) := by
  have : (fun a => u * ℓ a) = u • ℓ := by funext a; simp
  rw [this, mulVec_smul, dotProduct_smul, smul_eq_mul]

/-- Row moments, mapped and in inverse form. -/
theorem momA_map (f : S →+* R) (Q : Matrix ι ι S) (hQ : IsUnit (Q.map f).det) (σ : ι → S) :
    f (Q.det - ∑ i, σ i * ∑ k, Q.adjugate i k) =
      (Q.map f).det * (1 - (fun a => f (σ a)) ⬝ᵥ ((Q.map f)⁻¹ *ᵥ 1)) := by
  rw [← adj_moment (Q.map f) hQ _ 1 1, map_sub, map_det', map_sum]
  simp only [map_mul, map_sum, map_adjugate_apply, mul_one, Pi.one_apply]

theorem momB_map (f : S →+* R) (Q : Matrix ι ι S) (hQ : IsUnit (Q.map f).det) (σ P : ι → S)
    (Pt : S) :
    f (Q.det * Pt - ∑ i, σ i * ∑ k, Q.adjugate i k * P k) =
      (Q.map f).det * (f Pt - (fun a => f (σ a)) ⬝ᵥ ((Q.map f)⁻¹ *ᵥ fun a => f (P a))) := by
  rw [← adj_moment (Q.map f) hQ _ _ (f Pt), map_sub, map_mul, map_det', map_sum]
  simp only [map_mul, map_sum, map_adjugate_apply]

theorem momA_map_col (f : S →+* R) (Q : Matrix ι ι S) (hQ : IsUnit (Q.map f).det)
    (hsym : (Q.map f)ᵀ = Q.map f) (σ : ι → S) :
    f (Q.det - ∑ j, (∑ k, Q.adjugate k j) * σ j) =
      (Q.map f).det * (1 - (fun a => f (σ a)) ⬝ᵥ ((Q.map f)⁻¹ *ᵥ 1)) := by
  rw [← adj_moment_col (Q.map f) hQ hsym _ 1 1, map_sub, map_det', map_sum]
  simp only [map_mul, map_sum, map_adjugate_apply, one_mul, Pi.one_apply, mul_one]

theorem momB_map_col (f : S →+* R) (Q : Matrix ι ι S) (hQ : IsUnit (Q.map f).det)
    (hsym : (Q.map f)ᵀ = Q.map f) (σ P : ι → S) (Pt : S) :
    f (Q.det * Pt - ∑ j, (∑ k, P k * Q.adjugate k j) * σ j) =
      (Q.map f).det * (f Pt - (fun a => f (σ a)) ⬝ᵥ ((Q.map f)⁻¹ *ᵥ fun a => f (P a))) := by
  rw [← adj_moment_col (Q.map f) hQ hsym _ _ (f Pt), map_sub, map_mul, map_det', map_sum]
  simp only [map_mul, map_sum, map_adjugate_apply]

end Generic

variable {p N : ℕ} [Fact p.Prime] {Fr : Frame} {ι : Type} [Fintype ι] [DecidableEq ι]

theorem algebraMap_PF1 (D : PoleData Fr p N) (a : ℕ) :
    algebraMap (LocRing p)[X] (GaussLoc p) (PF1 p Fr a) =
      algebraMap (LocRing p)[X] (GaussLoc p) (nL p Fr) * ellL p Fr a := by
  unfold ellL
  rw [mul_comm, mul_assoc, Ring.inverse_mul_cancel _ (isUnit_nL D), mul_one]

/-- **The second-order function of one node.** -/
theorem node_bridge (D : PoleData Fr p N) (c : ι → ℕ) (hc : ∀ a, c a < N)
    (Q : Matrix ι ι (LocRing p)[X])
    (hQ : ∀ a b, a ≠ b → nL p Fr * (nd p (c b) - nd p (c a)) * Q a b =
      PF p Fr (c b) - PF p Fr (c a))
    (hdet : phiP p Q.det ≠ 0) (t : ℕ) (ht : t < N) (σ : ι → (LocRing p)[X])
    (hσ : ∀ a, nL p Fr * (nd p (c a) - nd p t) * σ a = PF p Fr (c a) - PF p Fr t)
    (momA momB : (LocRing p)[X])
    (hA : algebraMap _ (GaussLoc p) momA = (Q.map (algebraMap _ (GaussLoc p))).det *
      (1 - (fun a => algebraMap _ (GaussLoc p) (σ a)) ⬝ᵥ
        ((Q.map (algebraMap _ (GaussLoc p)))⁻¹ *ᵥ 1)))
    (hB : algebraMap _ (GaussLoc p) momB = piL p * ((Q.map (algebraMap _ (GaussLoc p))).det *
      (algebraMap _ (GaussLoc p) (PF1 p Fr t) - (fun a => algebraMap _ (GaussLoc p) (σ a)) ⬝ᵥ
        ((Q.map (algebraMap _ (GaussLoc p)))⁻¹ *ᵥ
          fun a => algebraMap _ (GaussLoc p) (PF1 p Fr (c a))))))
    (d G₁ : GaussLoc p)
    (hG : (ellL p Fr t - d) - (sOwn c t σ ᵥ* (Dmat c Q)⁻¹) ⬝ᵥ (fun a => ellL p Fr (c a) - d) =
      piL p * G₁)
    (hB0 : res p (1 - ∑ j, (sOwn c t σ ᵥ* (Dmat c Q)⁻¹) j) ≠ 0) :
    ∃ Φ : GaussLoc p,
      algebraMap _ (GaussLoc p) momB = algebraMap _ (GaussLoc p) momA *
        (piL p * (algebraMap _ (GaussLoc p) (nL p Fr) * d) + piL p ^ 2 * Φ) ∧
      res p Φ = res p (algebraMap _ (GaussLoc p) (nL p Fr)) *
        (res p G₁ / res p (1 - ∑ j, (sOwn c t σ ᵥ* (Dmat c Q)⁻¹) j) -
          ∑ c' : ZMod p, if c' = ((t : ℕ) : ZMod p) then 0 else
            fibMom c (Dmat c Q) (fun a => ellL p Fr (c a) - d) c' /
              (rfH p c' - rfH p ((t : ℕ) : ZMod p))) := by
  obtain ⟨Bk, Rem, h1, h2⟩ := node_phi2 D c hc Q hQ hdet t ht σ hσ d G₁ hG
  have hα := node_alpha_res D c hc Q hQ hdet t ht σ hσ
  set Qm := Q.map (algebraMap (LocRing p)[X] (GaussLoc p))
  set σm : ι → GaussLoc p := fun a => algebraMap _ (GaussLoc p) (σ a)
  set α := 1 - σm ⬝ᵥ (Qm⁻¹ *ᵥ 1)
  set u := algebraMap (LocRing p)[X] (GaussLoc p) (nL p Fr)
  set Bf := res p (1 - ∑ j, (sOwn c t σ ᵥ* (Dmat c Q)⁻¹) j)
  have hαu : IsUnit α := isUnit_of_res_ne _ (by rw [hα]; exact hB0)
  set W := G₁ - Bk + piL p * Rem
  refine ⟨u * W * Ring.inverse α, ?_, ?_⟩
  · have hP : (fun a => algebraMap _ (GaussLoc p) (PF1 p Fr (c a))) =
        fun a => u * ellL p Fr (c a) := by
      funext a; exact algebraMap_PF1 D (c a)
    have hs : σm ⬝ᵥ (Qm⁻¹ *ᵥ fun a => u * ellL p Fr (c a)) =
        u * (σm ⬝ᵥ (Qm⁻¹ *ᵥ fun a => ellL p Fr (c a))) := lin_scale _ _ _ _
    rw [hB, hA, hP, hs, algebraMap_PF1 D t]
    have hinv := Ring.mul_inverse_cancel α hαu
    have e : ellL p Fr t - σm ⬝ᵥ (Qm⁻¹ *ᵥ fun a => ellL p Fr (c a)) = d * α + piL p * W := by
      rw [← h1]; ring
    calc piL p * (Qm.det * (u * ellL p Fr t - u * (σm ⬝ᵥ (Qm⁻¹ *ᵥ fun a => ellL p Fr (c a)))))
        = piL p * Qm.det * u * (ellL p Fr t - σm ⬝ᵥ (Qm⁻¹ *ᵥ fun a => ellL p Fr (c a))) := by
          ring
      _ = piL p * Qm.det * u * (d * α + piL p * W) := by rw [e]
      _ = piL p * Qm.det * u * (d * α + piL p * W * (α * Ring.inverse α)) := by rw [hinv, mul_one]
      _ = Qm.det * α * (piL p * (u * d) + piL p ^ 2 * (u * W * Ring.inverse α)) := by ring
  · rw [map_mul, map_mul, res_inverse _ hαu, hα]
    have hW : res p W = res p G₁ - res p Bk := by
      simp only [W, map_add, map_sub, map_mul, res_piL, zero_mul, add_zero]
    rw [hW, h2]
    field_simp

end CatalanCore.Uniform.Content.UFMoments
