module

public import CatalanCore.Uniform.Content.UFMoments.NodeLoc

@[expose] public section

/-!
# UF moments: the second-order expansion of one border node of the lift

For an abstract core block `Q` (Loewner commutator off the diagonal, primitive determinant) and a
node `t` with border vector `σ` (commutator against the core), in `GaussLoc p`:

* `core_split`: `Q = D + π E` (`Dmat`: colour blocks; `Emat`: Loewner quotients across residues);
* `node_split`: `σ = s + π s'` (`sOwn`, `sCross`);
* `node_phi2`: for a direction `d` with own-fiber moment `G₀ = π G₁`,
  `(ℓ_t - σ·Q⁻¹ℓ) - d (1 - σ·Q⁻¹1) = π (G₁ - Bk + π Rem)`,
  `res Bk = B · Σ_{c ≠ t̄} m(c)/(c - t̄)`, `m(c) = Σ_{c_a ≡ c} res((D⁻¹ y)_a) res(y_a)`, `y = ℓ - d`;
* `node_alpha_res`: `res(1 - σ·Q⁻¹1) = B = res(1 - Σ g)`, `g = s D⁻¹`.
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Hybrid

namespace CatalanCore.Uniform.Content.UFMoments

variable {p N : ℕ} [Fact p.Prime] {Fr : Frame} {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The prefix value `ℓ_a = p F(a) / norm` in `GaussLoc p`. -/
noncomputable def ellL (p : ℕ) [Fact p.Prime] (Fr : Frame) (a : ℕ) : GaussLoc p :=
  algebraMap (LocRing p)[X] (GaussLoc p) (PF1 p Fr a) *
    Ring.inverse (algebraMap (LocRing p)[X] (GaussLoc p) (nL p Fr))

/-- Residue colouring of the core. -/
def colOf (c : ι → ℕ) : ι → ZMod p := fun a => ((c a : ℕ) : ZMod p)

/-- The colour-block part of the core block. -/
noncomputable def Dmat (c : ι → ℕ) (Q : Matrix ι ι (LocRing p)[X]) : Matrix ι ι (GaussLoc p) :=
  Matrix.of fun a b => if colOf (p := p) c a = colOf c b then
    algebraMap (LocRing p)[X] (GaussLoc p) (Q a b) else 0

/-- The cross-residue Loewner quotients. -/
noncomputable def Emat (p : ℕ) [Fact p.Prime] (Fr : Frame) (c : ι → ℕ) :
    Matrix ι ι (GaussLoc p) :=
  Matrix.of fun a b => if colOf (p := p) c a = colOf c b then 0 else
    (ellL p Fr (c b) - ellL p Fr (c a)) * Ring.inverse (ndL p (c b) - ndL p (c a))

/-- The own-residue part of a border vector. -/
noncomputable def sOwn (c : ι → ℕ) (t : ℕ) (σ : ι → (LocRing p)[X]) : ι → GaussLoc p :=
  fun a => if colOf (p := p) c a = ((t : ℕ) : ZMod p) then
    algebraMap (LocRing p)[X] (GaussLoc p) (σ a) else 0

/-- The cross-residue quotients of a border vector. -/
noncomputable def sCross (p : ℕ) [Fact p.Prime] (Fr : Frame) (c : ι → ℕ) (t : ℕ) :
    ι → GaussLoc p :=
  fun a => if colOf (p := p) c a = ((t : ℕ) : ZMod p) then 0 else
    (ellL p Fr (c a) - ellL p Fr t) * Ring.inverse (ndL p (c a) - ndL p t)

theorem core_split (D : PoleData Fr p N) (c : ι → ℕ) (hc : ∀ a, c a < N)
    (Q : Matrix ι ι (LocRing p)[X])
    (hQ : ∀ a b, a ≠ b → nL p Fr * (nd p (c b) - nd p (c a)) * Q a b =
      PF p Fr (c b) - PF p Fr (c a)) :
    Q.map (algebraMap (LocRing p)[X] (GaussLoc p)) = Dmat c Q + piL p • Emat p Fr c := by
  ext a b
  by_cases h : colOf (p := p) c a = colOf c b
  · simp [Dmat, Emat, h]
  · have hab : a ≠ b := fun e => h (by rw [e])
    simp only [Matrix.map_apply, Matrix.add_apply, Dmat, Emat, Matrix.of_apply, h, ↓reduceIte,
      zero_add, Matrix.smul_apply, smul_eq_mul]
    exact loewner_split D (hc a) (hc b) h (Q a b) (hQ a b hab)

theorem node_split (D : PoleData Fr p N) (c : ι → ℕ) (hc : ∀ a, c a < N) (t : ℕ) (ht : t < N)
    (σ : ι → (LocRing p)[X])
    (hσ : ∀ a, nL p Fr * (nd p (c a) - nd p t) * σ a = PF p Fr (c a) - PF p Fr t) :
    (fun a => algebraMap (LocRing p)[X] (GaussLoc p) (σ a)) =
      sOwn c t σ + piL p • sCross p Fr c t := by
  funext a
  by_cases h : colOf (p := p) c a = ((t : ℕ) : ZMod p)
  · simp [sOwn, sCross, h]
  · simp only [Pi.add_apply, Pi.smul_apply, sOwn, sCross, h, ↓reduceIte, zero_add, smul_eq_mul]
    exact loewner_split D ht (hc a) (Ne.symm h) (σ a) (hσ a)

theorem res_Emat (c : ι → ℕ) (a b : ι) (h : colOf (p := p) c a ≠ colOf c b) :
    res p (Emat p Fr c a b) = (res p (ellL p Fr (c b)) - res p (ellL p Fr (c a))) /
      (rfH p (colOf c b) - rfH p (colOf c a)) := by
  simp only [Emat, Matrix.of_apply, h, ↓reduceIte]
  rw [map_mul, res_inverse _ (isUnit_ndL_sub (Ne.symm h)), res_ndL_sub, map_sub, div_eq_mul_inv]
  rfl

theorem res_sCross (c : ι → ℕ) (t : ℕ) (a : ι) (h : colOf (p := p) c a ≠ ((t : ℕ) : ZMod p)) :
    res p (sCross p Fr c t a) = (res p (ellL p Fr (c a)) - res p (ellL p Fr t)) /
      (rfH p (colOf c a) - rfH p ((t : ℕ) : ZMod p)) := by
  simp only [sCross, h, ↓reduceIte]
  rw [map_mul, res_inverse _ (isUnit_ndL_sub h), res_ndL_sub, map_sub, div_eq_mul_inv]
  rfl

theorem isUnit_Dmat_det (D : PoleData Fr p N) (c : ι → ℕ) (hc : ∀ a, c a < N)
    (Q : Matrix ι ι (LocRing p)[X])
    (hQ : ∀ a b, a ≠ b → nL p Fr * (nd p (c b) - nd p (c a)) * Q a b =
      PF p Fr (c b) - PF p Fr (c a))
    (hdet : phiP p Q.det ≠ 0) : IsUnit (Dmat c Q).det := by
  refine isUnit_of_res_ne _ ?_
  set fL := algebraMap (LocRing p)[X] (GaussLoc p)
  have hm : (Q.map fL).map (res p) = (Dmat c Q).map (res p) := by
    rw [core_split D c hc Q hQ]
    ext a b
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add,
      map_mul, res_piL, zero_mul, add_zero]
  have h1 : res p (Q.map fL).det = phiP p Q.det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, res_algebraMap]
  have h2 : res p (Dmat c Q).det = ((Dmat c Q).map (res p)).det := by
    have := RingHom.map_det (res p) (Dmat c Q)
    rw [RingHom.mapMatrix_apply] at this
    convert this using 2
  have h3 : res p (Q.map fL).det = (((Q.map fL)).map (res p)).det := by
    have := RingHom.map_det (res p) (Q.map fL)
    rw [RingHom.mapMatrix_apply] at this
    convert this using 2
  rw [h2, ← hm, ← h3, h1]
  exact hdet

end CatalanCore.Uniform.Content.UFMoments
