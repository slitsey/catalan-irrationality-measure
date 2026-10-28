module

public import CatalanCore.Uniform.Content.UFMember.Fiber

@[expose] public section

/-!
# UF member package: the first-order moments of the scaled lift are fiber-local

With `Q̄ = Q mod p` (block diagonal over the residue classes of the core nodes) and
`F(z)` the residue class of the border node `z`:

* `rowMomA_red`: `ᾱ_z = det Q̄_{¬F(z)} · (det Q̄_{F(z)} - S̄'_{z,F} adj(Q̄_F) 1)`;
* `rowMomB1_red`: `β̄¹_z = det Q̄_{¬F(z)} · (det Q̄_{F(z)} ℓ(x_z) - S̄'_{z,F} adj(Q̄_F) ℓ_F)`,
  `ℓ = p F mod p` the reduced pole prefix (`β_z = p β¹_z`, `rowMomB_eq`);
* `colMomA_red`, `colMomB1_red`: the same for border columns (transposed core block).

So the first-order direction of a border node is `(local α : local β)` of its OWN fiber, scaled
by the common factor `det Q̄_{¬F}`: nodes with the same fiber-local data have the same
direction (transport), and the first-order wedges of the kills are fiber-local.
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Rect CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.Hybrid

namespace CatalanCore.Uniform.Content.UFMember

variable {p N : ℕ} [Fact p.Prime] {Fr : Frame} {ι κ : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

/-- Cross-residue constant entries of the lift vanish modulo `p`. -/
theorem phiP_sConst_eq_zero (D : PoleData Fr p N) (hN : N < p * p) {c : ι → ℕ} {xs ys : κ → ℕ}
    (hc : ∀ a, c a < N) (hx : ∀ i, xs i < N) (hy : ∀ j, ys j < N) (u v : ι ⊕ κ)
    (huv : ((rowNode c xs u : ℕ) : ZMod p) ≠ ((colNode c ys v : ℕ) : ZMod p)) :
    phiP p (Polynomial.C (sConst c xs ys (hint_of_poleData D hN hc hx hy) u v)) = 0 := by
  rw [phiP_C]
  simp only [sConst, Matrix.of_apply]
  rw [redQ_sq_eq_zero (hfib_of_poleData D hc hx hy u v huv) _]
  exact rfC_zero p

/-- The reduced core block is block diagonal over residues. -/
theorem core_red_color (D : PoleData Fr p N) (hN : N < p * p) (c : ι → ℕ) (xs ys : κ → ℕ)
    (hc : ∀ a, c a < N) (hx : ∀ i, xs i < N) (hy : ∀ j, ys j < N) (a b : ι)
    (hab : ((c a : ℕ) : ZMod p) ≠ ((c b : ℕ) : ZMod p)) :
    ((sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₁.map (phiP p)) a b = 0 := by
  have hne : a ≠ b := fun h => hab (by rw [h])
  simp only [Matrix.map_apply, sLift, Matrix.toBlocks₁₁, Matrix.of_apply, Matrix.add_apply,
    Matrix.map_apply, Matrix.fromBlocks_apply₁₁, Matrix.smul_apply, Matrix.one_apply_ne hne,
    smul_zero, add_zero]
  exact phiP_sConst_eq_zero D hN hc hx hy (Sum.inl a) (Sum.inl b) hab

/-- A border row meets only its own core fiber modulo `p`. -/
theorem row_red_support (D : PoleData Fr p N) (hN : N < p * p) (c : ι → ℕ) (xs ys : κ → ℕ)
    (hc : ∀ a, c a < N) (hx : ∀ i, xs i < N) (hy : ∀ j, ys j < N) (z : κ) (a : ι)
    (ha : ((c a : ℕ) : ZMod p) ≠ ((xs z : ℕ) : ZMod p)) :
    phiP p ((sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₂₁ z a) = 0 := by
  simp only [sLift, Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.add_apply, Matrix.map_apply,
    Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, add_zero]
  exact phiP_sConst_eq_zero D hN hc hx hy (Sum.inr z) (Sum.inl a)
    (by simpa [rowNode, colNode] using Ne.symm ha)

/-- A border column meets only its own core fiber modulo `p`. -/
theorem col_red_support (D : PoleData Fr p N) (hN : N < p * p) (c : ι → ℕ) (xs ys : κ → ℕ)
    (hc : ∀ a, c a < N) (hx : ∀ i, xs i < N) (hy : ∀ j, ys j < N) (y : κ) (a : ι)
    (ha : ((c a : ℕ) : ZMod p) ≠ ((ys y : ℕ) : ZMod p)) :
    phiP p ((sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₂ a y) = 0 := by
  simp only [sLift, Matrix.toBlocks₁₂, Matrix.of_apply, Matrix.add_apply, Matrix.map_apply,
    Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, add_zero]
  exact phiP_sConst_eq_zero D hN hc hx hy (Sum.inl a) (Sum.inr y)
    (by simpa [rowNode, colNode] using ha)

/-- The reduced core block. -/
noncomputable abbrev Qred (A : Matrix (ι ⊕ κ) (ι ⊕ κ) (LocRing p)[X]) :
    Matrix ι ι (RatFunc (ZMod p)) :=
  A.toBlocks₁₁.map (phiP p)

lemma phiP_adjugate (A : Matrix (ι ⊕ κ) (ι ⊕ κ) (LocRing p)[X]) (i k : ι) :
    phiP p (A.toBlocks₁₁.adjugate i k) = (Qred A).adjugate i k := by
  have h := RingHom.map_adjugate (phiP p) A.toBlocks₁₁
  exact congrFun (congrFun h i) k

lemma phiP_det (A : Matrix (ι ⊕ κ) (ι ⊕ κ) (LocRing p)[X]) :
    phiP p A.toBlocks₁₁.det = (Qred A).det :=
  RingHom.map_det (phiP p) A.toBlocks₁₁

/-- The residue colouring of the core. -/
def coreCol (c : ι → ℕ) : ι → ZMod p := fun a => ((c a : ℕ) : ZMod p)

/-- **`ᾱ_z` is fiber-local.** -/
theorem rowMomA_red (D : PoleData Fr p N) (hN : N < p * p) (c : ι → ℕ) (xs ys : κ → ℕ)
    (hc : ∀ a, c a < N) (hx : ∀ i, xs i < N) (hy : ∀ j, ys j < N) (z : κ) :
    let A := sLift c xs ys (hint_of_poleData D hN hc hx hy)
    let k : ZMod p := ((xs z : ℕ) : ZMod p)
    phiP p (rowMomA A z) =
      ((Qred A).toSquareBlockProp fun i => ¬ coreCol (p := p) c i = k).det *
        (((Qred A).toSquareBlockProp fun i => coreCol (p := p) c i = k).det * 1 -
          ∑ i : {i // coreCol (p := p) c i = k}, phiP p (A.toBlocks₂₁ z i) *
            ∑ j : {i // coreCol (p := p) c i = k},
              ((Qred A).toSquareBlockProp fun i => coreCol (p := p) c i = k).adjugate i j * 1) := by
  intro A k
  have hdet : (Qred A).det ≠ 0 := by
    rw [← phiP_det]; exact sLift_core_det c xs ys _
  have h := bordered_local (Qred A) (coreCol (p := p) c) k
    (fun a b hab => core_red_color D hN c xs ys hc hx hy a b hab) hdet 1
    (fun i => phiP p (A.toBlocks₂₁ z i)) (fun _ => 1)
    (fun i hi => row_red_support D hN c xs ys hc hx hy z i hi)
  rw [← h]
  unfold rowMomA
  rw [map_sub, phiP_det, map_sum, mul_one]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [phiP_adjugate, mul_one]

/-- **`β̄¹_z` is fiber-local.** -/
theorem rowMomB1_red (D : PoleData Fr p N) (hN : N < p * p) (c : ι → ℕ) (xs ys : κ → ℕ)
    (hc : ∀ a, c a < N) (hx : ∀ i, xs i < N) (hy : ∀ j, ys j < N) (z : κ) :
    let A := sLift c xs ys (hint_of_poleData D hN hc hx hy)
    let k : ZMod p := ((xs z : ℕ) : ZMod p)
    phiP p (A.toBlocks₁₁.det * PF1 p Fr (xs z) -
        ∑ i, A.toBlocks₂₁ z i * ∑ j, A.toBlocks₁₁.adjugate i j * PF1 p Fr (c j)) =
      ((Qred A).toSquareBlockProp fun i => ¬ coreCol (p := p) c i = k).det *
        (((Qred A).toSquareBlockProp fun i => coreCol (p := p) c i = k).det *
            phiP p (PF1 p Fr (xs z)) -
          ∑ i : {i // coreCol (p := p) c i = k}, phiP p (A.toBlocks₂₁ z i) *
            ∑ j : {i // coreCol (p := p) c i = k},
              ((Qred A).toSquareBlockProp fun i => coreCol (p := p) c i = k).adjugate i j *
                phiP p (PF1 p Fr (c j))) := by
  intro A k
  have hdet : (Qred A).det ≠ 0 := by
    rw [← phiP_det]; exact sLift_core_det c xs ys _
  have h := bordered_local (Qred A) (coreCol (p := p) c) k
    (fun a b hab => core_red_color D hN c xs ys hc hx hy a b hab) hdet (phiP p (PF1 p Fr (xs z)))
    (fun i => phiP p (A.toBlocks₂₁ z i)) (fun j => phiP p (PF1 p Fr (c j)))
    (fun i hi => row_red_support D hN c xs ys hc hx hy z i hi)
  rw [← h]
  rw [map_sub, map_mul, phiP_det, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, phiP_adjugate]

/-- **`ᾱ'_y` is fiber-local** (transposed core block). -/
theorem colMomA_red (D : PoleData Fr p N) (hN : N < p * p) (c : ι → ℕ) (xs ys : κ → ℕ)
    (hc : ∀ a, c a < N) (hx : ∀ i, xs i < N) (hy : ∀ j, ys j < N) (y : κ) :
    let A := sLift c xs ys (hint_of_poleData D hN hc hx hy)
    let k : ZMod p := ((ys y : ℕ) : ZMod p)
    phiP p (colMomA A y) =
      ((Qred A)ᵀ.toSquareBlockProp fun i => ¬ coreCol (p := p) c i = k).det *
        (((Qred A)ᵀ.toSquareBlockProp fun i => coreCol (p := p) c i = k).det * 1 -
          ∑ i : {i // coreCol (p := p) c i = k}, phiP p (A.toBlocks₁₂ i y) *
            ∑ j : {i // coreCol (p := p) c i = k},
              ((Qred A)ᵀ.toSquareBlockProp fun i => coreCol (p := p) c i = k).adjugate i j * 1) := by
  intro A k
  have hdet : (Qred A)ᵀ.det ≠ 0 := by
    rw [Matrix.det_transpose, ← phiP_det]; exact sLift_core_det c xs ys _
  have h := bordered_local (Qred A)ᵀ (coreCol (p := p) c) k
    (fun a b hab => by
      rw [Matrix.transpose_apply]
      exact core_red_color D hN c xs ys hc hx hy b a (Ne.symm hab)) hdet 1
    (fun i => phiP p (A.toBlocks₁₂ i y)) (fun _ => 1)
    (fun i hi => col_red_support D hN c xs ys hc hx hy y i hi)
  rw [← h]
  unfold colMomA
  rw [map_sub, phiP_det, ← Matrix.det_transpose, map_sum, mul_one]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_sum, mul_comm]
  congr 1
  refine Finset.sum_congr rfl fun k' _ => ?_
  rw [phiP_adjugate, mul_one, ← Matrix.adjugate_transpose]
  rfl

/-- **`β̄'¹_y` is fiber-local** (transposed core block). -/
theorem colMomB1_red (D : PoleData Fr p N) (hN : N < p * p) (c : ι → ℕ) (xs ys : κ → ℕ)
    (hc : ∀ a, c a < N) (hx : ∀ i, xs i < N) (hy : ∀ j, ys j < N) (y : κ) :
    let A := sLift c xs ys (hint_of_poleData D hN hc hx hy)
    let k : ZMod p := ((ys y : ℕ) : ZMod p)
    phiP p (A.toBlocks₁₁.det * PF1 p Fr (ys y) -
        ∑ j, (∑ k', PF1 p Fr (c k') * A.toBlocks₁₁.adjugate k' j) * A.toBlocks₁₂ j y) =
      ((Qred A)ᵀ.toSquareBlockProp fun i => ¬ coreCol (p := p) c i = k).det *
        (((Qred A)ᵀ.toSquareBlockProp fun i => coreCol (p := p) c i = k).det *
            phiP p (PF1 p Fr (ys y)) -
          ∑ i : {i // coreCol (p := p) c i = k}, phiP p (A.toBlocks₁₂ i y) *
            ∑ j : {i // coreCol (p := p) c i = k},
              ((Qred A)ᵀ.toSquareBlockProp fun i => coreCol (p := p) c i = k).adjugate i j *
                phiP p (PF1 p Fr (c j))) := by
  intro A k
  have hdet : (Qred A)ᵀ.det ≠ 0 := by
    rw [Matrix.det_transpose, ← phiP_det]; exact sLift_core_det c xs ys _
  have h := bordered_local (Qred A)ᵀ (coreCol (p := p) c) k
    (fun a b hab => by
      rw [Matrix.transpose_apply]
      exact core_red_color D hN c xs ys hc hx hy b a (Ne.symm hab)) hdet
    (phiP p (PF1 p Fr (ys y)))
    (fun i => phiP p (A.toBlocks₁₂ i y)) (fun j => phiP p (PF1 p Fr (c j)))
    (fun i hi => col_red_support D hN c xs ys hc hx hy y i hi)
  rw [← h]
  rw [map_sub, map_mul, phiP_det, ← Matrix.det_transpose, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_sum, mul_comm]
  congr 1
  refine Finset.sum_congr rfl fun k' _ => ?_
  rw [map_mul, phiP_adjugate, ← Matrix.adjugate_transpose, mul_comm]
  rfl

end CatalanCore.Uniform.Content.UFMember
