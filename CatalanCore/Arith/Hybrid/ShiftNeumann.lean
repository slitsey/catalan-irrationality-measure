module
public import CatalanCore.Arith.Hybrid.ShiftMoments
@[expose] public section
open Finset Matrix Polynomial CatalanCore CatalanCore.Basic
namespace CatalanCore.Arith.Hybrid
namespace ChainModel
open LemmaE

/-! # Second-order (Neumann) partners and the `gn ≤ 1` defect

`O = Q - Q0` is the cross-chain part of the scaled core, `adj Q0` the block-diagonal adjugate and
`Sr2 = C2 adj(Q0) (h - O adj(Q0))` the second-order row partner.  The residual
`h² C - Sr2 A = C adj(Q0) O adj(Q0) O` is Gauss-integral; with the cleared inverse `N` of size
`p⁻²` it yields the moment congruence `h² mom ≡ g ∑ Sr2 w` modulo `p²`. -/

variable {p r N o k : ℕ} [Fact p.Prime] {Fr : Frame} {Z : Type} [Fintype Z] [DecidableEq Z]
  {xs ys : Z → ℕ}

/-- The cross-chain part of the scaled core. -/
noncomputable def Ocross (Fr : Frame) (p r : ℕ) [Fact p.Prime] (xs ys : Z → ℕ) :
    Matrix (Fin r) (Fin r) ℚ[X] := Q Fr p r xs ys - Q0 Fr p r xs ys

/-- The second-order Neumann row partner. -/
noncomputable def Sr2 (Fr : Frame) (p r : ℕ) [Fact p.Prime] (xs ys : Z → ℕ) :
    Matrix Z (Fin r) ℚ[X] :=
  C2 Fr p r xs ys * (Q0 Fr p r xs ys).adjugate *
    (h Fr p r xs ys • (1 : Matrix (Fin r) (Fin r) ℚ[X]) -
      Ocross Fr p r xs ys * (Q0 Fr p r xs ys).adjugate)

lemma Q0_add_Ocross : Q0 Fr p r xs ys + Ocross Fr p r xs ys = Q Fr p r xs ys := by
  unfold Ocross; abel

/-- **The second-order residual identity.** -/
theorem resid2_eq :
    h Fr p r xs ys ^ 2 • (full Fr p r xs ys).toBlocks₂₁ -
        Sr2 Fr p r xs ys * (full Fr p r xs ys).toBlocks₁₁ =
      (full Fr p r xs ys).toBlocks₂₁ * (Q0 Fr p r xs ys).adjugate * Ocross Fr p r xs ys *
        (Q0 Fr p r xs ys).adjugate * Ocross Fr p r xs ys := by
  have hadj : (Q0 Fr p r xs ys).adjugate * Q0 Fr p r xs ys =
      h Fr p r xs ys • (1 : Matrix (Fin r) (Fin r) ℚ[X]) := Matrix.adjugate_mul _
  have H : h Fr p r xs ys ^ 2 • C2 Fr p r xs ys - Sr2 Fr p r xs ys * Q Fr p r xs ys =
      C2 Fr p r xs ys * (Q0 Fr p r xs ys).adjugate * Ocross Fr p r xs ys *
        (Q0 Fr p r xs ys).adjugate * Ocross Fr p r xs ys := by
    have H0 := neumann_residual_left (Q0 Fr p r xs ys) (Ocross Fr p r xs ys)
      (Q0 Fr p r xs ys).adjugate (C2 Fr p r xs ys) (h Fr p r xs ys) hadj
    rw [Q0_add_Ocross] at H0
    exact H0
  have hp0 : (C ((p:ℚ)^2) : ℚ[X]) ≠ 0 := by simp [(Fact.out : p.Prime).ne_zero]
  have hC2 : C2 Fr p r xs ys = C ((p:ℚ)^2) • (full Fr p r xs ys).toBlocks₂₁ := rfl
  have hQ : Q Fr p r xs ys = C ((p:ℚ)^2) • (full Fr p r xs ys).toBlocks₁₁ := Q_eq_smul
  have e1 : Sr2 Fr p r xs ys * Q Fr p r xs ys =
      C ((p:ℚ)^2) • (Sr2 Fr p r xs ys * (full Fr p r xs ys).toBlocks₁₁) := by
    rw [hQ, Matrix.mul_smul]
  rw [e1] at H
  have hL : C ((p:ℚ)^2) • (h Fr p r xs ys ^ 2 • (full Fr p r xs ys).toBlocks₂₁ -
        Sr2 Fr p r xs ys * (full Fr p r xs ys).toBlocks₁₁) =
      C ((p:ℚ)^2) • ((full Fr p r xs ys).toBlocks₂₁ * (Q0 Fr p r xs ys).adjugate *
        Ocross Fr p r xs ys * (Q0 Fr p r xs ys).adjugate * Ocross Fr p r xs ys) := by
    rw [smul_sub, smul_comm (C ((p:ℚ)^2)) (h Fr p r xs ys ^ 2)]
    have H2 := H
    rw [hC2] at H2
    simpa only [Matrix.smul_mul] using H2
  exact smul_right_injective _ hp0 hL


section Bounds
variable (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) (hr : r≤N)
  (hk : (4:ZMod p)*k=(o:ZMod p)) (hx : ∀ z, xs z<N)

omit hr in
lemma Ocross_apply (i j : Fin r) :
    Ocross Fr p r xs ys i j = if i.val % p = j.val % p then 0 else Q Fr p r xs ys i j := by
  unfold Ocross Q0
  simp only [Matrix.sub_apply, blockProject, blockRect]
  split_ifs <;> simp

include hL hp hN hr hk in
lemma gn_Ocross_le (i j : Fin r) : gn p (Ocross Fr p r xs ys i j) ≤ (p:ℝ)⁻¹ := by
  by_cases hij : i.val % p = j.val % p
  · rw [Ocross_apply, if_pos hij, gn_zero]; positivity
  · rw [Ocross_apply, if_neg hij]
    have hA := A_project_defect (xs := xs) (ys := ys) hL hp hN hr hk i j
    have e : (blockProject (fun i : Fin r => i.val % p) (full Fr p r xs ys).toBlocks₁₁ -
        (full Fr p r xs ys).toBlocks₁₁) i j = -((full Fr p r xs ys).toBlocks₁₁ i j) := by
      simp [blockProject, blockRect, hij]
    rw [e, gn_neg] at hA
    rw [Q_eq_smul, Matrix.smul_apply, smul_eq_mul, gn_mul,
      show (C ((p:ℚ)^2) : ℚ[X]) = (C (p:ℚ))^2 by rw [map_pow], gn_pow, gn_C,
      padicNorm.padicNorm_p_of_prime]
    have hp0 : (0:ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    push_cast
    calc ((p:ℝ)⁻¹)^2 * gn p ((full Fr p r xs ys).toBlocks₁₁ i j) ≤ ((p:ℝ)⁻¹)^2 * p :=
          mul_le_mul_of_nonneg_left hA (by positivity)
      _ = (p:ℝ)⁻¹ := by field_simp

include hL hp hN hr hk hx in
/-- **The `Q0/O` defect.**  The second-order residual `h² C - Sr2 A` is Gauss-integral. -/
theorem resid2_gn (z : Z) (i : Fin r) :
    gn p (((full Fr p r xs ys).toBlocks₂₁ * (Q0 Fr p r xs ys).adjugate * Ocross Fr p r xs ys *
        (Q0 Fr p r xs ys).adjugate * Ocross Fr p r xs ys) z i) ≤ 1 := by
  have hp0 : (0:ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hC : ∀ z i, gn p ((full Fr p r xs ys).toBlocks₂₁ z i) ≤ (p:ℝ)^2 := fun z i => by
    have := (gle_iff_gn p 2 _).1 (Periodic.Model.C_gle_two (xs := xs) (ys := ys) (Periodic.lamPoleData hL hp hN)
      (by omega) hr hx z i)
    exact this
  have hadj : ∀ i j, gn p ((Q0 Fr p r xs ys).adjugate i j) ≤ 1 := fun i j =>
    adj_int1 (Q0_int1 hL hp hN hr) i j
  have hO : ∀ i j, gn p (Ocross Fr p r xs ys i j) ≤ (p:ℝ)⁻¹ := gn_Ocross_le hL hp hN hr hk
  have h1 := gn_matmul_le (p := p) (full Fr p r xs ys).toBlocks₂₁ (Q0 Fr p r xs ys).adjugate
    ((p:ℝ)^2) 1 (by positivity) zero_le_one hC hadj
  have h2 := gn_matmul_le (p := p) ((full Fr p r xs ys).toBlocks₂₁ * (Q0 Fr p r xs ys).adjugate)
    (Ocross Fr p r xs ys) _ _ (by positivity) (by positivity) h1 hO
  have h3 := gn_matmul_le (p := p) ((full Fr p r xs ys).toBlocks₂₁ * (Q0 Fr p r xs ys).adjugate *
      Ocross Fr p r xs ys) (Q0 Fr p r xs ys).adjugate _ _ (by positivity) zero_le_one h2 hadj
  have h4 := gn_matmul_le (p := p) ((full Fr p r xs ys).toBlocks₂₁ * (Q0 Fr p r xs ys).adjugate *
      Ocross Fr p r xs ys * (Q0 Fr p r xs ys).adjugate) (Ocross Fr p r xs ys) _ _
    (by positivity) (by positivity) h3 hO
  refine (h4 z i).trans (le_of_eq ?_)
  field_simp

end Bounds


section Mom2
variable (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) (hr : r≤N)
  (hk : (4:ZMod p)*k=(o:ZMod p)) (hx : ∀ z, xs z<N)

/-- Algebra of a row partner: for any partner `S` and scalar `c`,
`c ∑_i C_zi ∑_k N_ik w_k - g ∑_m S_zm w_m = ∑_i (c C - S A)_zi ∑_k N_ik w_k`. -/
theorem mom_partner_identity (S : Matrix Z (Fin r) ℚ[X]) (c : ℚ[X]) (w : Fin r → ℚ[X]) (z : Z) :
    c * ∑ i, (full Fr p r xs ys).toBlocks₂₁ z i * ∑ k, Nm Fr p r xs ys i k * w k -
        (Q Fr p r xs ys).det * ∑ m, S z m * w m =
      ∑ i, ((c • (full Fr p r xs ys).toBlocks₂₁ - S * (full Fr p r xs ys).toBlocks₁₁) z i) *
        ∑ k, Nm Fr p r xs ys i k * w k := by
  set A := (full Fr p r xs ys).toBlocks₁₁ with hA
  have hAN : A * Nm Fr p r xs ys = (Q Fr p r xs ys).det • (1 : Matrix (Fin r) (Fin r) ℚ[X]) :=
    AN_eq p (fun _ : Fin r => 1) A
  set rs : Fin r → ℚ[X] := fun i => ∑ k, Nm Fr p r xs ys i k * w k with hrs
  have hAr : ∀ m, ∑ i, A m i * rs i = (Q Fr p r xs ys).det * w m := by
    intro m
    have hAN' : ∀ k, ∑ i, A m i * Nm Fr p r xs ys i k =
        if m = k then (Q Fr p r xs ys).det else 0 := fun k => by
      have := congrFun (congrFun hAN m) k
      simpa [Matrix.mul_apply, Matrix.one_apply, Matrix.smul_apply] using this
    calc ∑ i, A m i * rs i = ∑ i, ∑ k, A m i * Nm Fr p r xs ys i k * w k := by
          apply Finset.sum_congr rfl; intro i _
          simp only [hrs, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro k _; ring
      _ = ∑ k, (∑ i, A m i * Nm Fr p r xs ys i k) * w k := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro k _
          rw [Finset.sum_mul]
      _ = ∑ k, (if m = k then (Q Fr p r xs ys).det else 0) * w k := by
          apply Finset.sum_congr rfl; intro k _; rw [hAN']
      _ = (Q Fr p r xs ys).det * w m := by
          simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have e1 : ∑ i, ((S * A) z i) * rs i =
      (Q Fr p r xs ys).det * ∑ m, S z m * w m := by
    calc ∑ i, ((S * A) z i) * rs i
        = ∑ i, ∑ m, S z m * (A m i * rs i) := by
          apply Finset.sum_congr rfl; intro i _
          rw [Matrix.mul_apply, Finset.sum_mul]
          apply Finset.sum_congr rfl; intro m _; ring
      _ = ∑ m, S z m * ∑ i, A m i * rs i := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro m _
          rw [Finset.mul_sum]
      _ = ∑ m, S z m * ((Q Fr p r xs ys).det * w m) := by
          apply Finset.sum_congr rfl; intro m _; rw [hAr]
      _ = _ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro m _; ring
  rw [Finset.mul_sum]
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, sub_mul, Finset.sum_sub_distrib]
  rw [e1]
  apply congrArg (· - _)
  apply Finset.sum_congr rfl; intro i _; ring

include hL hp hN hr hk hx in
/-- **Second-order moment congruence.**  `h² ∑_i C_zi ∑_k N_ik w_k ≡ g ∑_m Sr2_zm w_m (mod p²)`
for integral `w` (Gauss distance `≤ p⁻²`). -/
theorem mom_lead2 (w : Fin r → ℚ[X]) (hw : ∀ k, Int1 p (w k)) (z : Z) :
    gn p (h Fr p r xs ys ^ 2 * ∑ i, (full Fr p r xs ys).toBlocks₂₁ z i *
        ∑ k, Nm Fr p r xs ys i k * w k -
      (Q Fr p r xs ys).det * ∑ m, Sr2 Fr p r xs ys z m * w m) ≤ ((p:ℝ)⁻¹)^2 := by
  rw [mom_partner_identity (ys := ys) (Sr2 Fr p r xs ys) (h Fr p r xs ys ^ 2) w z]
  have hp0 : (0:ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hb : gn p (∑ i, (((h Fr p r xs ys ^ 2) • (full Fr p r xs ys).toBlocks₂₁ -
      Sr2 Fr p r xs ys * (full Fr p r xs ys).toBlocks₁₁) z i) *
        ∑ k, Nm Fr p r xs ys i k * w k) ≤ 1 * ((p:ℝ)⁻¹)^2 := by
    apply gn_sum_le_const _ _ _ (by positivity)
    intro i _
    rw [gn_mul]
    refine mul_le_mul ?_ (gn_rowsum_le hL hp hN hr w hw i) (gn_nonneg p _) zero_le_one
    rw [resid2_eq]
    exact resid2_gn hL hp hN hr hk hx z i
  simpa using hb

end Mom2

end ChainModel

#print axioms ChainModel.mom_lead2
end CatalanCore.Arith.Hybrid
