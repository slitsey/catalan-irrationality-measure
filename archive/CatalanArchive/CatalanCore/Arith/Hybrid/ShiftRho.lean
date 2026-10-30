module
public import CatalanCore.Arith.Hybrid.ShiftNeumann
@[expose] public section
open Finset Matrix Polynomial CatalanCore CatalanCore.Basic
namespace CatalanCore.Arith.Hybrid
namespace ChainModel
open LemmaE ChainClasses

/-! # The one-node residual to second order

`moment2_gamma`: for constants `a, b` and a row node `z`,
`h² (a · pβ_z - b · α_z) ≡ g · (h² ω_z - ∑_m Sr2_zm ω_m)  (mod p²)`, `ω_k = a pPf(k) - b`.
Here `Γ(z) = (a pβ_z - b α_z)/p`, so the one-node formula `GammaFormula` is a statement about the
explicit residual `ρ(z) = h² ω_z - (Sr2 ω)_z` modulo `p²`.

`Sr2_split`: `Sr2 = h Sr + h Cx adj(Q0) - Sr O adj(Q0) - Cx adj(Q0) O adj(Q0)`, with `Cx` the
cross-chain part of the row `C2`; the last term has Gauss norm `≤ p⁻²`.  So modulo `p²` only the
own-chain term `h Sr` needs second-order information; the cross-chain terms are first order. -/

variable {p r N o k : ℕ} [Fact p.Prime] {Fr : Frame} {Z : Type} [Fintype Z] [DecidableEq Z]
  {xs ys : Z → ℕ}

/-- The weights `ω_k = a · p Pf(k) - b`. -/
noncomputable def omegaW (Fr : Frame) (p : ℕ) (a b : ℚ[X]) (k : ℕ) : ℚ[X] :=
  a * C ((p : ℚ) * fullPrefix Fr k) - b

section Moment
variable (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) (hr : r≤N)
  (hk : (4:ZMod p)*k=(o:ZMod p)) (hx : ∀ z, xs z<N)
include hL hp hN hr hk hx

/-- **Second-order one-node residual.** -/
theorem moment2_gamma (a b : ℚ[X]) (ha : Int1 p a) (hb : Int1 p b) (z : Z) :
    gn p (h Fr p r xs ys ^ 2 * (a * bR Fr p r xs ys z - b * aR Fr p r xs ys z) -
      (Q Fr p r xs ys).det * (h Fr p r xs ys ^ 2 * omegaW Fr p a b (xs z) -
        ∑ m, Sr2 Fr p r xs ys z m * omegaW Fr p a b m.val)) ≤ ((p:ℝ)⁻¹)^2 := by
  have hω : ∀ m : Fin r, Int1 p (omegaW Fr p a b m.val) := fun m =>
    (ha.mul (int1_pPf hL hp hN hr (lt_of_lt_of_le m.isLt hr))).sub hb
  have H := mom_lead2 (xs := xs) (ys := ys) hL hp hN hr hk hx (fun m => omegaW Fr p a b m.val) hω z
  have e1 : ∑ i, (full Fr p r xs ys).toBlocks₂₁ z i *
        ∑ m, Nm Fr p r xs ys i m * omegaW Fr p a b m.val =
      a * (C (p : ℚ) * rowP Fr p r xs ys z) - b * rowB Fr p r xs ys z := by
    unfold rowP rowB omegaW
    simp only [map_mul, Finset.mul_sum, mul_sub, Finset.sum_sub_distrib]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => by ring
    · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => by ring
  have key : a * bR Fr p r xs ys z - b * aR Fr p r xs ys z =
      (Q Fr p r xs ys).det * omegaW Fr p a b (xs z) -
        ∑ i, (full Fr p r xs ys).toBlocks₂₁ z i * ∑ m, Nm Fr p r xs ys i m * omegaW Fr p a b m.val := by
    rw [e1]
    unfold aR bR omegaW
    simp only [map_mul]
    ring
  have e2 : h Fr p r xs ys ^ 2 * (a * bR Fr p r xs ys z - b * aR Fr p r xs ys z) -
      (Q Fr p r xs ys).det * (h Fr p r xs ys ^ 2 * omegaW Fr p a b (xs z) -
        ∑ m, Sr2 Fr p r xs ys z m * omegaW Fr p a b m.val) =
      -(h Fr p r xs ys ^ 2 * ∑ i, (full Fr p r xs ys).toBlocks₂₁ z i *
          ∑ m, Nm Fr p r xs ys i m * omegaW Fr p a b m.val -
        (Q Fr p r xs ys).det * ∑ m, Sr2 Fr p r xs ys z m * omegaW Fr p a b m.val) := by
    rw [key]; ring
  rw [e2, gn_neg]
  exact H

end Moment


section Split
variable (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) (hr : r≤N)
  (hk : (4:ZMod p)*k=(o:ZMod p)) (hx : ∀ z, xs z<N)

/-- The cross-chain part of the `C2` rows. -/
noncomputable def Cx (Fr : Frame) (p r : ℕ) [Fact p.Prime] (xs ys : Z → ℕ) : Matrix Z (Fin r) ℚ[X] :=
  C2 Fr p r xs ys - blockRect (fun z => xs z % p) (fun i : Fin r => i.val % p) (C2 Fr p r xs ys)

/-- **Exact split of the second-order row partner.** -/
theorem Sr2_split_eq :
    Sr2 Fr p r xs ys = h Fr p r xs ys • Sr Fr p r xs ys +
      h Fr p r xs ys • (Cx Fr p r xs ys * (Q0 Fr p r xs ys).adjugate) -
      Sr Fr p r xs ys * (Ocross Fr p r xs ys * (Q0 Fr p r xs ys).adjugate) -
      (Cx Fr p r xs ys * (Q0 Fr p r xs ys).adjugate) *
        (Ocross Fr p r xs ys * (Q0 Fr p r xs ys).adjugate) := by
  have hS : Sr Fr p r xs ys = (C2 Fr p r xs ys - Cx Fr p r xs ys) * (Q0 Fr p r xs ys).adjugate := by
    simp [Sr, Cx, LemmaE.modelRow]
  have hC : C2 Fr p r xs ys = (C2 Fr p r xs ys - Cx Fr p r xs ys) + Cx Fr p r xs ys := by abel
  have e : C2 Fr p r xs ys * (Q0 Fr p r xs ys).adjugate =
      Sr Fr p r xs ys + Cx Fr p r xs ys * (Q0 Fr p r xs ys).adjugate := by
    rw [hS, ← Matrix.add_mul, sub_add_cancel]
  unfold Sr2
  rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one]
  rw [e, Matrix.add_mul, smul_add]
  abel

include hL hp hN hr hk hx in
/-- The last term of the split is negligible modulo `p²`. -/
theorem Sr2_split_err (z : Z) (m : Fin r) :
    gn p (((Cx Fr p r xs ys * (Q0 Fr p r xs ys).adjugate) *
        (Ocross Fr p r xs ys * (Q0 Fr p r xs ys).adjugate)) z m) ≤ ((p:ℝ)⁻¹)^2 := by
  have hp0 : (0:ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hpi : (0:ℝ) ≤ (p:ℝ)⁻¹ := by positivity
  have hCx : ∀ z i, gn p (Cx Fr p r xs ys z i) ≤ (p:ℝ)⁻¹ := by
    intro z i
    have hD := Periodic.Model.C_project_defect (xs := xs) (ys := ys)
      (Periodic.lamPoleData hL hp hN) (by omega) hr hx z i
    have e : Cx Fr p r xs ys z i = C ((p:ℚ)^2) *
        ((full Fr p r xs ys).toBlocks₂₁ - blockRect (fun z => xs z % p) (fun i : Fin r => i.val % p)
          (full Fr p r xs ys).toBlocks₂₁) z i := by
      simp only [Cx, C2, blockRect, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      split_ifs <;> ring
    rw [e, gn_mul, show (C ((p:ℚ)^2) : ℚ[X]) = (C (p:ℚ))^2 by rw [map_pow], gn_pow, gn_C,
      padicNorm.padicNorm_p_of_prime]
    push_cast
    calc ((p:ℝ)⁻¹)^2 * gn p _ ≤ ((p:ℝ)⁻¹)^2 * p := mul_le_mul_of_nonneg_left hD (by positivity)
      _ = (p:ℝ)⁻¹ := by field_simp
  have hadj : ∀ i j, gn p ((Q0 Fr p r xs ys).adjugate i j) ≤ 1 := fun i j =>
    adj_int1 (Q0_int1 hL hp hN hr) i j
  have hO : ∀ i j, gn p (Ocross Fr p r xs ys i j) ≤ (p:ℝ)⁻¹ := gn_Ocross_le hL hp hN hr hk
  have h1 := gn_matmul_le (p := p) (Cx Fr p r xs ys) (Q0 Fr p r xs ys).adjugate _ _ hpi zero_le_one hCx hadj
  have h2 := gn_matmul_le (p := p) (Ocross Fr p r xs ys) (Q0 Fr p r xs ys).adjugate _ _ hpi zero_le_one hO hadj
  have h3 := gn_matmul_le (p := p) (Cx Fr p r xs ys * (Q0 Fr p r xs ys).adjugate)
    (Ocross Fr p r xs ys * (Q0 Fr p r xs ys).adjugate) _ _ (by positivity) (by positivity) h1 h2 z m
  refine h3.trans (le_of_eq ?_)
  ring

end Split

#print axioms moment2_gamma
#print axioms Sr2_split_eq
#print axioms Sr2_split_err
end ChainModel
end CatalanCore.Arith.Hybrid
