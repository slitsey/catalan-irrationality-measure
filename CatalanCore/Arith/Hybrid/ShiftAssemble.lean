module
public import CatalanCore.Arith.Hybrid.ShiftOwn
@[expose] public section
open Finset Matrix Polynomial CatalanCore CatalanCore.Basic
namespace CatalanCore.Arith.Hybrid

/-! # The one-node residual, assembled

`rho_node`: for a zone row `z` and constants `a, b` whose reductions are `ḡ B`, `ḡ A`,
`h² (a pβ_z - b α_z) = g (h W(z) + p Y(z))  (mod p²)`, with the own-chain residual `W` and a
cross-chain polynomial `Y` with `redI Y = -h̄² ḡ ∑_c (16(c-x))⁻¹ c̄(c)`. -/

section Rho
open ChainModel ChainClasses LemmaE
variable {p r N o k : ℕ} [Fact p.Prime] {Fr : Frame} {Z : Type} [Fintype Z] [DecidableEq Z]
  {xs ys : Z → ℕ}

theorem rho_node (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) (hr : r≤N)
    (hk : (4:ZMod p)*k=(o:ZMod p)) (hx : ∀ z, xs z<N) {a b : ℚ[X]} (ha : Int1 p a) (hb : Int1 p b)
    (gb : RatFunc (ZMod p)) (z : Z) (hxz : r ≤ xs z)
    (hA : redI p a = gb * srcB Fr p o r (xs z)) (hB : redI p b = gb * srcA Fr p o r (xs z)) :
    ∃ Y : ℚ[X], GLE p 0 Y ∧
      redI p Y = -(redI p (ChainModel.h Fr p r xs ys))^2 * gb *
        ∑ c : ZMod p, rfC p ((16 * (c - ((xs z : ℕ) : ZMod p)))⁻¹) *
          respAt Fr p o r c (srcA Fr p o r (xs z)) (srcB Fr p o r (xs z)) ∧
      gn p (ChainModel.h Fr p r xs ys ^ 2 * (a * bR Fr p r xs ys z - b * aR Fr p r xs ys z) -
        (Q Fr p r xs ys).det * (ChainModel.h Fr p r xs ys * Wown Fr p r xs ys a b z +
          C (p : ℚ) * Y)) ≤ ((p:ℝ)⁻¹)^2 := by
  classical
  have hε : (0:ℝ) ≤ ((p:ℝ)⁻¹)^2 := by
    have : (0:ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    positivity
  have hwint : ∀ m : Fin r, Int1 p (omegaW Fr p a b m.val) := fun m =>
    (ha.mul (int1_pPf hL hp hN hr (lt_of_lt_of_le m.isLt hr))).sub hb
  obtain ⟨Y, hY1, hY2, hY3⟩ := Z_reduce (ys := ys) hL hp hN hr hx (gle0_of_int1 ha) (gle0_of_int1 hb)
    gb z hxz hA hB
  refine ⟨Y, hY1, hY3, ?_⟩
  have M2 := moment2_gamma (ys := ys) hL hp hN hr hk hx a b ha hb z
  have hsplit : ∀ m, Sr2 Fr p r xs ys z m = ChainModel.h Fr p r xs ys * Sr Fr p r xs ys z m +
      ChainModel.h Fr p r xs ys * (Cx Fr p r xs ys * (Q0 Fr p r xs ys).adjugate) z m -
      (Sr Fr p r xs ys * (Ocross Fr p r xs ys * (Q0 Fr p r xs ys).adjugate)) z m -
      ((Cx Fr p r xs ys * (Q0 Fr p r xs ys).adjugate) *
        (Ocross Fr p r xs ys * (Q0 Fr p r xs ys).adjugate)) z m := fun m => by
    have := congrFun (congrFun (Sr2_split_eq (Fr := Fr) (p := p) (r := r) (xs := xs) (ys := ys)) z) m
    simpa [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply] using this
  have herr : gn p (∑ m, ((Cx Fr p r xs ys * (Q0 Fr p r xs ys).adjugate) *
        (Ocross Fr p r xs ys * (Q0 Fr p r xs ys).adjugate)) z m * omegaW Fr p a b m.val) ≤
        ((p:ℝ)⁻¹)^2 := by
    apply LemmaE.gn_sum_le_const _ _ _ hε
    intro m _
    rw [gn_mul]
    calc gn p _ * gn p (omegaW Fr p a b m.val) ≤ ((p:ℝ)⁻¹)^2 * 1 :=
        mul_le_mul (Sr2_split_err hL hp hN hr hk hx z m) (hwint m) (gn_nonneg p _) hε
      _ = _ := mul_one _
  -- the two bilinear identities
  have E1 : ∑ m, (Cx Fr p r xs ys * (Q0 Fr p r xs ys).adjugate) z m * omegaW Fr p a b m.val =
      ∑ j, Cx Fr p r xs ys z j * Vw Fr p r xs ys (fun m => omegaW Fr p a b m.val) j := by
    have : ((Cx Fr p r xs ys * (Q0 Fr p r xs ys).adjugate) *ᵥ (fun m => omegaW Fr p a b m.val)) z =
        (Cx Fr p r xs ys *ᵥ Vw Fr p r xs ys (fun m => omegaW Fr p a b m.val)) z := by
      rw [← Matrix.mulVec_mulVec]; rfl
    simpa [Matrix.mulVec, dotProduct] using this
  have E2 : ∑ m, (Sr Fr p r xs ys * (Ocross Fr p r xs ys * (Q0 Fr p r xs ys).adjugate)) z m *
        omegaW Fr p a b m.val =
      ∑ m, Sr Fr p r xs ys z m * ∑ j, Ocross Fr p r xs ys m j *
        Vw Fr p r xs ys (fun m => omegaW Fr p a b m.val) j := by
    have : ((Sr Fr p r xs ys * (Ocross Fr p r xs ys * (Q0 Fr p r xs ys).adjugate)) *ᵥ
        (fun m => omegaW Fr p a b m.val)) z =
        (Sr Fr p r xs ys *ᵥ (Ocross Fr p r xs ys *ᵥ
          Vw Fr p r xs ys (fun m => omegaW Fr p a b m.val))) z := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]; rfl
    simpa [Matrix.mulVec, dotProduct] using this
  have hsum : ∑ m, Sr2 Fr p r xs ys z m * omegaW Fr p a b m.val =
      ChainModel.h Fr p r xs ys * ∑ m, Sr Fr p r xs ys z m * omegaW Fr p a b m.val +
      ChainModel.h Fr p r xs ys * ∑ j, Cx Fr p r xs ys z j *
        Vw Fr p r xs ys (fun m => omegaW Fr p a b m.val) j -
      ∑ m, Sr Fr p r xs ys z m * ∑ j, Ocross Fr p r xs ys m j *
        Vw Fr p r xs ys (fun m => omegaW Fr p a b m.val) j -
      ∑ m, ((Cx Fr p r xs ys * (Q0 Fr p r xs ys).adjugate) *
        (Ocross Fr p r xs ys * (Q0 Fr p r xs ys).adjugate)) z m * omegaW Fr p a b m.val := by
    rw [← E1, ← E2]
    simp only [hsplit, sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.mul_sum, mul_assoc]
  rw [hsum] at M2
  have hZ : C (p : ℚ) * Y = -(ChainModel.h Fr p r xs ys * ∑ j, Cx Fr p r xs ys z j *
            Vw Fr p r xs ys (fun m => omegaW Fr p a b m.val) j) +
        ∑ m, Sr Fr p r xs ys z m * ∑ j, Ocross Fr p r xs ys m j *
            Vw Fr p r xs ys (fun m => omegaW Fr p a b m.val) j := hY2.symm
  have hg : gn p (Q Fr p r xs ys).det ≤ 1 := by
    have := ChainModel.Q_primitive (xs := xs) (ys := ys) hL hp hN hr
    exact this.le
  have hdec : ChainModel.h Fr p r xs ys ^ 2 * (a * bR Fr p r xs ys z - b * aR Fr p r xs ys z) -
        (Q Fr p r xs ys).det * (ChainModel.h Fr p r xs ys * Wown Fr p r xs ys a b z +
          C (p : ℚ) * Y) =
      (ChainModel.h Fr p r xs ys ^ 2 * (a * bR Fr p r xs ys z - b * aR Fr p r xs ys z) -
        (Q Fr p r xs ys).det * (ChainModel.h Fr p r xs ys ^ 2 * omegaW Fr p a b (xs z) -
          (ChainModel.h Fr p r xs ys * ∑ m, Sr Fr p r xs ys z m * omegaW Fr p a b m.val +
            ChainModel.h Fr p r xs ys * ∑ j, Cx Fr p r xs ys z j *
              Vw Fr p r xs ys (fun m => omegaW Fr p a b m.val) j -
            ∑ m, Sr Fr p r xs ys z m * ∑ j, Ocross Fr p r xs ys m j *
              Vw Fr p r xs ys (fun m => omegaW Fr p a b m.val) j -
            ∑ m, ((Cx Fr p r xs ys * (Q0 Fr p r xs ys).adjugate) *
              (Ocross Fr p r xs ys * (Q0 Fr p r xs ys).adjugate)) z m * omegaW Fr p a b m.val))) +
      (Q Fr p r xs ys).det * ∑ m, ((Cx Fr p r xs ys * (Q0 Fr p r xs ys).adjugate) *
              (Ocross Fr p r xs ys * (Q0 Fr p r xs ys).adjugate)) z m * omegaW Fr p a b m.val := by
    unfold Wown
    rw [hZ]
    ring
  rw [hdec]
  refine (gn_add_le _ _).trans (max_le M2 ?_)
  rw [gn_mul]
  calc gn p (Q Fr p r xs ys).det * _ ≤ 1 * ((p:ℝ)⁻¹)^2 := mul_le_mul hg herr (gn_nonneg p _) zero_le_one
    _ = _ := one_mul _

end Rho

#print axioms CatalanCore.Arith.Hybrid.rho_node
end CatalanCore.Arith.Hybrid
