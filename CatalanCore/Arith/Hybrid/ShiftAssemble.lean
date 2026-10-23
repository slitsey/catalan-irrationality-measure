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

section Cmp
open ChainModel ChainClasses LemmaE
variable {p r N o : ℕ} [Fact p.Prime] {Fr : Frame} {Z1 Z2 : Type} [Fintype Z1] [DecidableEq Z1]
  [Fintype Z2] [DecidableEq Z2] {xs1 ys1 : Z1 → ℕ} {xs2 ys2 : Z2 → ℕ}

lemma Rg_mem (hp : 5 ≤ p) (a : ℕ) : Rg p o a ∈ LocRing p := by
  rw [Rg_eq_regularPrefix]
  exact (good_regularPrefix (p := p) (o:ℤ) (four_ne_zmod p hp) a).mem

lemma gn_C_pRg_le (hp : 5 ≤ p) (a b : ℕ) :
    gn p (C ((p:ℚ) * (Rg p o b - Rg p o a))) ≤ 1 := by
  have hmem : Rg p o b - Rg p o a ∈ LocRing p := Subring.sub_mem _ (Rg_mem hp b) (Rg_mem hp a)
  have h1 : padicNorm p (Rg p o b - Rg p o a) ≤ 1 := (mem_locRing_iff_padicNorm (p := p)).1 hmem
  rw [map_mul, gn_mul, gn_C, gn_C, padicNorm.padicNorm_p_of_prime]
  have hp0 : (0:ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp1 : (1:ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  push_cast
  calc ((p:ℝ)⁻¹) * (padicNorm p (Rg p o b - Rg p o a) : ℝ) ≤ 1 * 1 :=
        mul_le_mul (inv_le_one_of_one_le₀ hp1) (by exact_mod_cast h1) (by exact_mod_cast padicNorm.nonneg _) zero_le_one
    _ = 1 := one_mul _

theorem sumSr_transport2 (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) (hr : r≤N)
    (hx1 : ∀ z, xs1 z<N) (hx2 : ∀ z, xs2 z<N)
    (hQ0 : Q0 Fr p r xs1 ys1 = Q0 Fr p r xs2 ys2)
    (z1 : Z1) (z2 : Z2) (hz1 : r ≤ xs1 z1) (hz2 : r ≤ xs2 z2) (hxx : xs1 z1 ≤ xs2 z2)
    (hnc : NoCut (Cut (p:ℤ) (r:ℤ) (Singular (p:ℤ) (o:ℤ))) (xs1 z1 : ℤ) (xs2 z2 : ℤ)) :
    gn p (∑ m, Sr Fr p r xs1 ys1 z1 m - ∑ m, Sr Fr p r xs2 ys2 z2 m) ≤ ((p:ℝ)⁻¹)^2 := by
  classical
  set e := chainTransport (sing := Singular (p:ℤ) (o:ℤ)) hxx hnc with he
  have hε : (0:ℝ) ≤ ((p:ℝ)⁻¹)^2 := by
    have : (0:ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    positivity
  have F1 : ∑ m, Sr Fr p r xs1 ys1 z1 m =
      ∑ q : ChainIndex p r (xs1 z1), Sr Fr p r xs1 ys1 z1 (chainNode q) := by
    rw [sum_chain (p := p) hz1 (fun m => Sr Fr p r xs1 ys1 z1 m)]
    intro m hm
    exact Sr_support hL hp hN hr z1 m (fun h => hm h.symm)
  have F2 : ∑ m, Sr Fr p r xs2 ys2 z2 m =
      ∑ q : ChainIndex p r (xs1 z1), Sr Fr p r xs2 ys2 z2 (chainNode (e q)) := by
    rw [sum_chain (p := p) hz2 (fun m => Sr Fr p r xs2 ys2 z2 m)]
    · exact (e.sum_comp (fun q' => Sr Fr p r xs2 ys2 z2 (chainNode q'))).symm
    · intro m hm
      exact Sr_support hL hp hN hr z2 m (fun h => hm h.symm)
  rw [F1, F2, ← Finset.sum_sub_distrib]
  exact LemmaE.gn_sum_le_const _ _ _ hε fun q _ =>
    Sr_transport2 hL hp hN hr hx1 hx2 hQ0 z1 z2 hz1 hz2 hxx hnc q

/-- **Own-chain comparison of two nodes of one cell, in either order.** -/
theorem Wown_cmp (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) (hr : r≤N)
    (hx1 : ∀ z, xs1 z<N) (hx2 : ∀ z, xs2 z<N)
    (hQ0 : Q0 Fr p r xs1 ys1 = Q0 Fr p r xs2 ys2)
    (z1 : Z1) (z2 : Z2) (hz1 : r ≤ xs1 z1) (hz2 : r ≤ xs2 z2)
    (hnc1 : xs1 z1 ≤ xs2 z2 →
      NoCut (Cut (p:ℤ) (r:ℤ) (Singular (p:ℤ) (o:ℤ))) (xs1 z1 : ℤ) (xs2 z2 : ℤ))
    (hnc2 : xs2 z2 ≤ xs1 z1 →
      NoCut (Cut (p:ℤ) (r:ℤ) (Singular (p:ℤ) (o:ℤ))) (xs2 z2 : ℤ) (xs1 z1 : ℤ))
    {a b : ℚ[X]} (ha : Int1 p a) (hb : Int1 p b) :
    gn p (Wown Fr p r xs1 ys1 a b z1 - Wown Fr p r xs2 ys2 a b z2 +
      a * C ((p:ℚ) * (Rg p o (xs2 z2) - Rg p o (xs1 z1))) *
        (ChainModel.h Fr p r xs1 ys1 - ∑ m, Sr Fr p r xs1 ys1 z1 m)) ≤ ((p:ℝ)⁻¹)^2 := by
  have hh : ChainModel.h Fr p r xs1 ys1 = ChainModel.h Fr p r xs2 ys2 := by
    unfold ChainModel.h; rw [hQ0]
  have hε : (0:ℝ) ≤ ((p:ℝ)⁻¹)^2 := by
    have : (0:ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    positivity
  rcases le_total (xs1 z1) (xs2 z2) with hle | hle
  · have H := Wown_transport2 hL hp hN hr hx1 hx2 hQ0 z1 z2 hz1 hz2 hle (hnc1 hle) ha hb
    have S := sumSr_transport2 hL hp hN hr hx1 hx2 hQ0 z1 z2 hz1 hz2 hle (hnc1 hle)
    have e : Wown Fr p r xs1 ys1 a b z1 - Wown Fr p r xs2 ys2 a b z2 +
        a * C ((p:ℚ) * (Rg p o (xs2 z2) - Rg p o (xs1 z1))) *
          (ChainModel.h Fr p r xs1 ys1 - ∑ m, Sr Fr p r xs1 ys1 z1 m) =
        (Wown Fr p r xs1 ys1 a b z1 - Wown Fr p r xs2 ys2 a b z2 +
          a * C ((p:ℚ) * (Rg p o (xs2 z2) - Rg p o (xs1 z1))) *
            (ChainModel.h Fr p r xs2 ys2 - ∑ m, Sr Fr p r xs2 ys2 z2 m)) +
        a * C ((p:ℚ) * (Rg p o (xs2 z2) - Rg p o (xs1 z1))) *
          (∑ m, Sr Fr p r xs2 ys2 z2 m - ∑ m, Sr Fr p r xs1 ys1 z1 m) := by
      rw [hh]; ring
    rw [e]
    refine (gn_add_le _ _).trans (max_le H ?_)
    have S' : gn p (∑ m, Sr Fr p r xs2 ys2 z2 m - ∑ m, Sr Fr p r xs1 ys1 z1 m) ≤ ((p:ℝ)⁻¹)^2 := by
      rw [← neg_sub, gn_neg]; exact S
    rw [gn_mul]
    calc gn p (a * C ((p:ℚ) * (Rg p o (xs2 z2) - Rg p o (xs1 z1)))) * _ ≤ 1 * ((p:ℝ)⁻¹)^2 := by
          refine mul_le_mul ?_ S' (gn_nonneg p _) zero_le_one
          rw [gn_mul]
          calc gn p a * gn p (C ((p:ℚ) * (Rg p o (xs2 z2) - Rg p o (xs1 z1)))) ≤ 1 * 1 :=
              mul_le_mul ha (gn_C_pRg_le hp _ _) (gn_nonneg p _) zero_le_one
            _ = 1 := one_mul _
      _ = _ := one_mul _
  · have H := Wown_transport2 hL hp hN hr hx2 hx1 hQ0.symm z2 z1 hz2 hz1 hle (hnc2 hle) ha hb
    have e : Wown Fr p r xs1 ys1 a b z1 - Wown Fr p r xs2 ys2 a b z2 +
        a * C ((p:ℚ) * (Rg p o (xs2 z2) - Rg p o (xs1 z1))) *
          (ChainModel.h Fr p r xs1 ys1 - ∑ m, Sr Fr p r xs1 ys1 z1 m) =
        -(Wown Fr p r xs2 ys2 a b z2 - Wown Fr p r xs1 ys1 a b z1 +
          a * C ((p:ℚ) * (Rg p o (xs1 z1) - Rg p o (xs2 z2))) *
            (ChainModel.h Fr p r xs2 ys2 - ∑ m, Sr Fr p r xs1 ys1 z1 m)) := by
      rw [← hh]
      have : (C ((p:ℚ) * (Rg p o (xs1 z1) - Rg p o (xs2 z2))) : ℚ[X]) =
          -(C ((p:ℚ) * (Rg p o (xs2 z2) - Rg p o (xs1 z1)))) := by
        rw [← map_neg]; congr 1; ring
      rw [this]; ring
    rw [e, gn_neg]
    exact H

end Cmp

#print axioms CatalanCore.Arith.Hybrid.rho_node
#print axioms CatalanCore.Arith.Hybrid.Wown_cmp
end CatalanCore.Arith.Hybrid
