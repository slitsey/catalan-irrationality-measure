module
public import CatalanCore.Arith.Hybrid.ShiftCross
@[expose] public section
open Finset Matrix Polynomial CatalanCore CatalanCore.Basic
namespace CatalanCore.Arith.Hybrid

/-! # The vector `V = adj(Q0) ω`, reduced on a chain

`V` solves `Q0 V = h ω`.  On the chain of a residue it reduces to `h̄ · Q̄_c⁻¹ ω̄`, with `Q̄_c` the
reduced pole model of the chain (the column analogue of `redI_Sr_chain`). -/

section SolveCol
variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

theorem solve_col (M : Matrix ι ι K) (hu : IsUnit M.det) (s b : ι → K) (c : K)
    (h : ∀ k, ∑ j, M k j * s j = c * b k) (j : ι) : s j = c * (M⁻¹ *ᵥ b) j := by
  have h1 : M *ᵥ s = c • b := funext fun k => by simpa [Matrix.mulVec, dotProduct] using h k
  have h2 : s = M⁻¹ *ᵥ (M *ᵥ s) := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
  have := congrFun h2 j
  rw [h1, Matrix.mulVec_smul] at this
  simpa using this

end SolveCol

namespace ChainModel
open LemmaE ChainClasses

variable {p r N o k : ℕ} [Fact p.Prime] {Fr : Frame} {Z : Type} [Fintype Z] [DecidableEq Z]
  {xs ys : Z → ℕ}

/-- `V = adj(Q0) · w`. -/
noncomputable def Vw (Fr : Frame) (p r : ℕ) [Fact p.Prime] (xs ys : Z → ℕ) (w : Fin r → ℚ[X]) :
    Fin r → ℚ[X] := (Q0 Fr p r xs ys).adjugate *ᵥ w

theorem Q0_mulVec_Vw (w : Fin r → ℚ[X]) :
    Q0 Fr p r xs ys *ᵥ Vw Fr p r xs ys w = h Fr p r xs ys • w := by
  unfold Vw
  rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec]
  rfl

end ChainModel

section Reduce
open ChainModel ChainClasses
variable {p r N o k : ℕ} [Fact p.Prime] {Fr : Frame} {Z : Type} [Fintype Z] [DecidableEq Z]
  {xs ys : Z → ℕ}

theorem gle0_Vw (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) (hr : r≤N)
    (w : Fin r → ℚ[X]) (hw : ∀ m, GLE p 0 (w m)) (i : Fin r) :
    GLE p 0 (Vw Fr p r xs ys w i) := by
  unfold Vw
  simp only [Matrix.mulVec, dotProduct]
  exact GLE.sum fun j _ => gle0_mul (gle0_of_int1 (LemmaE.adj_int1 (Q0_int1 hL hp hN hr) i j)) (hw j)

/-- **Chain reduction of `V`.** -/
theorem redI_Vw_chain (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) (hr : r≤N)
    (w : Fin r → ℚ[X]) (hw : ∀ m, GLE p 0 (w m)) {x : ℕ} (hxr : r ≤ x) (j : ChainIndex p r x) :
    redI p (Vw Fr p r xs ys w (chainNode j)) =
      redI p (ChainModel.h Fr p r xs ys) *
        ((poleRed Fr p o (fun j : ChainIndex p r x => (chainNode j).val))⁻¹ *ᵥ
          (fun i => redI p (w (chainNode i)))) j := by
  set a : ChainIndex p r x → ℕ := fun j => (chainNode j).val with ha
  have hM : (poleRed Fr p o a).transpose = poleRed Fr p o a := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [poleRed]
    · have hji : ¬ j = i := fun h => hij h.symm
      simp [poleRed, hij, hji, poleScaledEntry_symm (Fr := Fr) (p := p) (o := o) (a i) (a j)]
  have hV : ∀ m, GLE p 0 (Vw Fr p r xs ys w m) := gle0_Vw hL hp hN hr w hw
  refine solve_col (poleRed Fr p o a) (isUnit_det_poleRed a)
    (fun j => redI p (Vw Fr p r xs ys w (chainNode j))) (fun i => redI p (w (chainNode i)))
    (redI p (ChainModel.h Fr p r xs ys)) ?_ j
  intro q
  -- the exact identity on the chain of x
  have E := congrFun (ChainModel.Q0_mulVec_Vw (Fr := Fr) (p := p) (r := r) (xs := xs) (ys := ys) w) (chainNode q)
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at E
  rw [sum_chain (p := p) hxr (fun i => Q0 Fr p r xs ys (chainNode q) i * Vw Fr p r xs ys w i)] at E
  · have E2 : ∑ j : ChainIndex p r x, chainMatrix (p := p) Fr r x q j *
        Vw Fr p r xs ys w (chainNode j) = ChainModel.h Fr p r xs ys * w (chainNode q) := by
      rw [← E]
      apply Finset.sum_congr rfl; intro j _
      congr 1
      have := congrFun (congrFun (Q0_chain (Fr := Fr) (r := r) (z := x) (p := p) xs ys) q) j
      simpa using this.symm
    have E3 := congrArg (redI p) E2
    rw [redI_sum _ _ (fun j _ => gle0_mul (gle0_chainMatrix hL hp hN hr q j) (hV _))] at E3
    simp only [redI_mul (gle0_chainMatrix hL hp hN hr _ _) (hV _), redI_chainMatrix hL hp hN hr] at E3
    rw [redI_mul (gle0_h hL hp hN hr) (hw _)] at E3
    exact E3
  · intro m hm
    have : Q0 Fr p r xs ys (chainNode q) m = 0 :=
      ChainModel.Q0_support (Fr := Fr) (p := p) (xs := xs) (ys := ys) _ _ (by rw [chainNode_mod]; exact fun h => hm h.symm)
    rw [this, zero_mul]

end Reduce

#print axioms redI_Vw_chain
end CatalanCore.Arith.Hybrid
