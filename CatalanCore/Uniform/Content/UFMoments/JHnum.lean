module

public import CatalanCore.Uniform.Content.UFMoments.SLiftInst

@[expose] public section

/-!
# UF moments: (S7-Lean) on a joint type ⇒ the `J`-block hypothesis `hnum`

For the scaled lift `A`, a representative node (`t₀`, `σ₀`, direction `d` killing its own-fiber
moment, `B₀ ≠ 0`) and border rows `Jr`, columns `Jc` of the same joint type — each with a chain
equivalence to `t₀` along which the core, border and prefix data agree modulo `π²` up to the
prefix shift `κ = π κ₁`, and with `res κ₁ = K₀ + Σ_c W(c)(c - t̄)⁻¹` (the regular prefix, via
`step_identity`) — the second-order function of every `J` node is

  `res Φ(t) = K + Σ_c v(c) (c - t̄)⁻¹`,   `v(c) = norm · (W(c) - m(c))`,

and therefore (`hnum_jtype`) the moment hypothesis `hnum` of `JBlockCauchy.of_moments` holds with
`Ret = univ`.  `m = fibMom (ℓ - d)` is the fiber moment (`γ(c)/B²` of (S7)).
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Hybrid

namespace CatalanCore.Uniform.Content.UFMoments

variable {p N : ℕ} [Fact p.Prime] {Fr : Frame} {ι κ : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

section
variable (D : PoleData Fr p N) (hN : N < p * p) (c : ι → ℕ) (xs ys : κ → ℕ)
  (hc : ∀ a, c a < N) (hx : ∀ i, xs i < N) (hy : ∀ j, ys j < N)

theorem sLift_rowA (z : κ) :
    let A := sLift c xs ys (hint_of_poleData D hN hc hx hy)
    algebraMap _ (GaussLoc p) (rowMomA A z) =
      (A.toBlocks₁₁.map (algebraMap _ (GaussLoc p))).det *
        (1 - (fun a => algebraMap _ (GaussLoc p) (A.toBlocks₂₁ z a)) ⬝ᵥ
          ((A.toBlocks₁₁.map (algebraMap _ (GaussLoc p)))⁻¹ *ᵥ 1)) := by
  intro A
  exact momA_map _ A.toBlocks₁₁ (isUnit_map_det _ (sLift_core_det c xs ys _)) _

theorem sLift_rowB (z : κ) :
    let A := sLift c xs ys (hint_of_poleData D hN hc hx hy)
    algebraMap _ (GaussLoc p) (rowMomB A Fr c xs z) = piL p *
      ((A.toBlocks₁₁.map (algebraMap _ (GaussLoc p))).det *
        (algebraMap _ (GaussLoc p) (PF1 p Fr (xs z)) -
          (fun a => algebraMap _ (GaussLoc p) (A.toBlocks₂₁ z a)) ⬝ᵥ
            ((A.toBlocks₁₁.map (algebraMap _ (GaussLoc p)))⁻¹ *ᵥ
              fun a => algebraMap _ (GaussLoc p) (PF1 p Fr (c a))))) := by
  intro A
  rw [rowMomB_eq D A c xs hc hx z, map_mul]
  congr 1
  exact momB_map _ A.toBlocks₁₁ (isUnit_map_det _ (sLift_core_det c xs ys _)) _ _ _

theorem sLift_map_symm :
    let A := sLift c xs ys (hint_of_poleData D hN hc hx hy)
    (A.toBlocks₁₁.map (algebraMap _ (GaussLoc p)))ᵀ = A.toBlocks₁₁.map (algebraMap _ (GaussLoc p)) := by
  intro A
  rw [← Matrix.transpose_map, sLift_core_symm D hN c xs ys hc hx hy]

theorem sLift_colA (y : κ) :
    let A := sLift c xs ys (hint_of_poleData D hN hc hx hy)
    algebraMap _ (GaussLoc p) (colMomA A y) =
      (A.toBlocks₁₁.map (algebraMap _ (GaussLoc p))).det *
        (1 - (fun a => algebraMap _ (GaussLoc p) (A.toBlocks₁₂ a y)) ⬝ᵥ
          ((A.toBlocks₁₁.map (algebraMap _ (GaussLoc p)))⁻¹ *ᵥ 1)) := by
  intro A
  exact momA_map_col _ A.toBlocks₁₁ (isUnit_map_det _ (sLift_core_det c xs ys _))
    (sLift_map_symm D hN c xs ys hc hx hy) (fun a => A.toBlocks₁₂ a y)

theorem sLift_colB (y : κ) :
    let A := sLift c xs ys (hint_of_poleData D hN hc hx hy)
    algebraMap _ (GaussLoc p) (colMomB A Fr c ys y) = piL p *
      ((A.toBlocks₁₁.map (algebraMap _ (GaussLoc p))).det *
        (algebraMap _ (GaussLoc p) (PF1 p Fr (ys y)) -
          (fun a => algebraMap _ (GaussLoc p) (A.toBlocks₁₂ a y)) ⬝ᵥ
            ((A.toBlocks₁₁.map (algebraMap _ (GaussLoc p)))⁻¹ *ᵥ
              fun a => algebraMap _ (GaussLoc p) (PF1 p Fr (c a))))) := by
  intro A
  rw [colMomB_eq D A c ys hc hy y, map_mul]
  congr 1
  exact momB_map_col _ A.toBlocks₁₁ (isUnit_map_det _ (sLift_core_det c xs ys _))
    (sLift_map_symm D hN c xs ys hc hx hy) (fun a => A.toBlocks₁₂ a y) _ _

end

/-- Transport data of one node `t` (border vector `σ`) to the representative `(t₀, σ₀)`, with the
residue of the prefix shift given as a Cauchy sum. -/
def TypeData (Fr : Frame) (c : ι → ℕ) (Q : Matrix ι ι (LocRing p)[X]) (t0 : ℕ)
    (σ0 : ι → (LocRing p)[X]) (K0 : RatFunc (ZMod p)) (W : ZMod p → RatFunc (ZMod p))
    (t : ℕ) (σ : ι → (LocRing p)[X]) : Prop :=
  ∃ (e : {a // colOf (p := p) c a = ((t : ℕ) : ZMod p)} ≃
      {a // colOf (p := p) c a = ((t0 : ℕ) : ZMod p)}) (κ₁ : GaussLoc p),
    (∀ i j : {a // colOf (p := p) c a = ((t0 : ℕ) : ZMod p)}, ∃ x,
      algebraMap _ (GaussLoc p) (Q (e.symm i).1 (e.symm j).1) =
        algebraMap _ (GaussLoc p) (Q i.1 j.1) + piL p ^ 2 * x) ∧
    (∀ i : {a // colOf (p := p) c a = ((t0 : ℕ) : ZMod p)}, ∃ x,
      algebraMap _ (GaussLoc p) (σ (e.symm i).1) =
        algebraMap _ (GaussLoc p) (σ0 i.1) + piL p ^ 2 * x) ∧
    (∀ i : {a // colOf (p := p) c a = ((t0 : ℕ) : ZMod p)}, ∃ x,
      ellL p Fr (c (e.symm i).1) = ellL p Fr (c i.1) + (ellL p Fr t - ellL p Fr t0) +
        piL p ^ 2 * x) ∧
    ellL p Fr t - ellL p Fr t0 = piL p * κ₁ ∧
    res p κ₁ = K0 + ∑ c' : ZMod p, W c' * rfH p (c' - ((t : ℕ) : ZMod p))⁻¹

/-- The derived weights `v(c) = norm · (W(c) - m(c))`. -/
noncomputable def vDer (Fr : Frame) (c : ι → ℕ) (Q : Matrix ι ι (LocRing p)[X]) (d : GaussLoc p)
    (W : ZMod p → RatFunc (ZMod p)) (c' : ZMod p) : RatFunc (ZMod p) :=
  res p (algebraMap _ (GaussLoc p) (nL p Fr)) *
    (W c' - fibMom c (Dmat c Q) (fun a => ellL p Fr (c a) - d) c')

/-- One node: `res Φ = K + hDer univ v t̄`. -/
theorem jtype_node_hDer (D : PoleData Fr p N) (c : ι → ℕ) (hc : ∀ a, c a < N)
    (Q : Matrix ι ι (LocRing p)[X])
    (hQ : ∀ a b, a ≠ b → nL p Fr * (nd p (c b) - nd p (c a)) * Q a b =
      PF p Fr (c b) - PF p Fr (c a))
    (hdet : phiP p Q.det ≠ 0) (t0 : ℕ) (σ0 : ι → (LocRing p)[X]) (d : GaussLoc p)
    (hz : (ellL p Fr t0 - d) -
      (sOwn c t0 σ0 ᵥ* (Dmat c Q)⁻¹) ⬝ᵥ (fun a => ellL p Fr (c a) - d) = 0)
    (hB0 : res p (1 - ∑ j, (sOwn c t0 σ0 ᵥ* (Dmat c Q)⁻¹) j) ≠ 0)
    (K0 : RatFunc (ZMod p)) (W : ZMod p → RatFunc (ZMod p))
    (t : ℕ) (ht : t < N) (σ : ι → (LocRing p)[X])
    (hσ : ∀ a, nL p Fr * (nd p (c a) - nd p t) * σ a = PF p Fr (c a) - PF p Fr t)
    (momA momB : (LocRing p)[X])
    (hA : algebraMap _ (GaussLoc p) momA = (Q.map (algebraMap _ (GaussLoc p))).det *
      (1 - (fun a => algebraMap _ (GaussLoc p) (σ a)) ⬝ᵥ
        ((Q.map (algebraMap _ (GaussLoc p)))⁻¹ *ᵥ 1)))
    (hB : algebraMap _ (GaussLoc p) momB = piL p * ((Q.map (algebraMap _ (GaussLoc p))).det *
      (algebraMap _ (GaussLoc p) (PF1 p Fr t) - (fun a => algebraMap _ (GaussLoc p) (σ a)) ⬝ᵥ
        ((Q.map (algebraMap _ (GaussLoc p)))⁻¹ *ᵥ
          fun a => algebraMap _ (GaussLoc p) (PF1 p Fr (c a))))))
    (hT : TypeData Fr c Q t0 σ0 K0 W t σ) :
    ∃ Φ : GaussLoc p,
      algebraMap _ (GaussLoc p) momB = algebraMap _ (GaussLoc p) momA *
        (piL p * (algebraMap _ (GaussLoc p) (nL p Fr) * d) + piL p ^ 2 * Φ) ∧
      res p Φ = res p (algebraMap _ (GaussLoc p) (nL p Fr)) * K0 +
        hDer univ (vDer Fr c Q d W) ((t : ℕ) : ZMod p) := by
  obtain ⟨e, κ₁, hDD, hss, hℓ, hκ, hres⟩ := hT
  obtain ⟨Φ, h1, h2⟩ := jtype_node D c hc Q hQ hdet t0 σ0 d hz hB0 t ht σ hσ momA momB hA hB
    e hDD hss hℓ κ₁ hκ
  refine ⟨Φ, h1, ?_⟩
  rw [h2, hres, hDer]
  simp only [vDer, Finset.mul_sum, mul_add, mul_sub]
  have e2 : ∀ c' : ZMod p, res p (algebraMap _ (GaussLoc p) (nL p Fr)) * (W c' *
      rfH p (c' - ((t : ℕ) : ZMod p))⁻¹) - res p (algebraMap _ (GaussLoc p) (nL p Fr)) *
      (fibMom c (Dmat c Q) (fun a => ellL p Fr (c a) - d) c' *
        rfH p (c' - ((t : ℕ) : ZMod p))⁻¹) =
      (res p (algebraMap _ (GaussLoc p) (nL p Fr)) * W c' -
        res p (algebraMap _ (GaussLoc p) (nL p Fr)) *
          fibMom c (Dmat c Q) (fun a => ellL p Fr (c a) - d) c') *
        rfH p (c' - ((t : ℕ) : ZMod p))⁻¹ := fun c' => by ring
  rw [add_sub_assoc, ← Finset.sum_sub_distrib]
  simp_rw [e2]

/-- **(S7-Lean) ⇒ `hnum`** for the scaled lift on a joint type. -/
theorem hnum_jtype (D : PoleData Fr p N) (hN : N < p * p) (c : ι → ℕ) (xs ys : κ → ℕ)
    (hc : ∀ a, c a < N) (hx : ∀ i, xs i < N) (hy : ∀ j, ys j < N)
    (t0 : ℕ) (σ0 : ι → (LocRing p)[X]) (d : GaussLoc p)
    (hz : (ellL p Fr t0 - d) - (sOwn c t0 σ0 ᵥ*
      (Dmat c (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₁)⁻¹) ⬝ᵥ
        (fun a => ellL p Fr (c a) - d) = 0)
    (hB0 : res p (1 - ∑ j, (sOwn c t0 σ0 ᵥ*
      (Dmat c (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₁)⁻¹) j) ≠ 0)
    (K0 : RatFunc (ZMod p)) (W : ZMod p → RatFunc (ZMod p)) (Jr Jc : Finset κ)
    (hTr : ∀ z ∈ Jr, TypeData Fr c (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₁
      t0 σ0 K0 W (xs z) (fun a => (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₂₁ z a))
    (hTc : ∀ y ∈ Jc, TypeData Fr c (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₁
      t0 σ0 K0 W (ys y) (fun a => (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₂ a y)) :
    let A := sLift c xs ys (hint_of_poleData D hN hc hx hy)
    ∀ z ∈ Jr, ∀ y ∈ Jc, ∃ q : (LocRing p)[X],
      dispNum A Fr c xs ys z y = Polynomial.C ((p : ℕ) : LocRing p) ^ 2 * q ∧
      phiP p q = phiP p A.toBlocks₁₁.det *
        (phiP p (rowMomA A z) / phiP p A.toBlocks₁₁.det * phiP p (colMomA A y) *
          (hDer univ (vDer Fr c A.toBlocks₁₁ d W) ((ys y : ℕ) : ZMod p) -
            hDer univ (vDer Fr c A.toBlocks₁₁ d W) ((xs z : ℕ) : ZMod p))) := by
  intro A
  have hQ := sLift_core_rel D hN c xs ys hc hx hy
  have hdet := sLift_core_det (Fr := Fr) c xs ys (hint_of_poleData D hN hc hx hy)
  have hrow : ∀ z ∈ Jr, ∃ Φ : GaussLoc p,
      algebraMap _ (GaussLoc p) (rowMomB A Fr c xs z) = algebraMap _ (GaussLoc p) (rowMomA A z) *
        (piL p * (algebraMap _ (GaussLoc p) (nL p Fr) * d) + piL p ^ 2 * Φ) ∧
      res p Φ = res p (algebraMap _ (GaussLoc p) (nL p Fr)) * K0 +
        hDer univ (vDer Fr c A.toBlocks₁₁ d W) ((xs z : ℕ) : ZMod p) := fun z hz' =>
    jtype_node_hDer D c hc A.toBlocks₁₁ hQ hdet t0 σ0 d hz hB0 K0 W (xs z) (hx z) _
      (sLift_row_rel D hN c xs ys hc hx hy z) _ _ (sLift_rowA D hN c xs ys hc hx hy z)
      (sLift_rowB D hN c xs ys hc hx hy z) (hTr z hz')
  have hcol : ∀ y ∈ Jc, ∃ Φ : GaussLoc p,
      algebraMap _ (GaussLoc p) (colMomB A Fr c ys y) = algebraMap _ (GaussLoc p) (colMomA A y) *
        (piL p * (algebraMap _ (GaussLoc p) (nL p Fr) * d) + piL p ^ 2 * Φ) ∧
      res p Φ = res p (algebraMap _ (GaussLoc p) (nL p Fr)) * K0 +
        hDer univ (vDer Fr c A.toBlocks₁₁ d W) ((ys y : ℕ) : ZMod p) := fun y hy' =>
    jtype_node_hDer D c hc A.toBlocks₁₁ hQ hdet t0 σ0 d hz hB0 K0 W (ys y) (hy y) _
      (sLift_col_rel D hN c xs ys hc hx hy y) _ _ (sLift_colA D hN c xs ys hc hx hy y)
      (sLift_colB D hN c xs ys hc hx hy y) (hTc y hy')
  classical
  choose! Φ hΦ1 hΦ2 using hrow
  choose! Φ' hΦ'1 hΦ'2 using hcol
  exact hnum_of_local A c xs ys Jr Jc _ Φ Φ' hΦ1 hΦ'1 univ _ _ hΦ2 hΦ'2 hdet

end CatalanCore.Uniform.Content.UFMoments
