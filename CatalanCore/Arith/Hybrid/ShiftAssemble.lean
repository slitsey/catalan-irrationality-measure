module
public import CatalanCore.Arith.Hybrid.ShiftOwn
public import CatalanCore.Arith.Hybrid.ShiftGamma
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


section GammaDiff
open ChainModel ChainClasses LemmaE
variable {p r N o k : ℕ} [Fact p.Prime] {Fr : Frame} {Z1 Z2 : Type} [Fintype Z1] [DecidableEq Z1]
  [Fintype Z2] [DecidableEq Z2] {xs1 ys1 : Z1 → ℕ} {xs2 ys2 : Z2 → ℕ}

lemma Cp_mul_gamF (a b α β : ℚ[X]) : C (p : ℚ) * gamF p a b α β = a * β - b * α := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hCC : (C (p : ℚ) : ℚ[X]) * C ((p : ℚ)⁻¹) = 1 := by rw [← map_mul]; simp [hp0]
  unfold gamF
  calc C (p : ℚ) * (C ((p : ℚ)⁻¹) * (a * β - b * α)) = (C (p : ℚ) * C ((p : ℚ)⁻¹)) * (a * β - b * α) := by ring
    _ = a * β - b * α := by rw [hCC, one_mul]

lemma gle0_gamF {a b α β : ℚ[X]} (ha : GLE p 0 a) (hb : GLE p 0 b) (hα : GLE p 0 α) (hβ : GLE p 0 β)
    (c1 : redI p α = redI p a) (c2 : redI p β = redI p b) : GLE p 0 (gamF p a b α β) := by
  obtain ⟨u, hu, e1⟩ := exists_div_of_redI_eq hα ha c1
  obtain ⟨v, hv, e2⟩ := exists_div_of_redI_eq hβ hb c2
  rw [gamF_eq e1 e2]
  exact gle0_of_int1 ((int1_of_gle0 (gle0_mul ha hv)).sub (int1_of_gle0 (gle0_mul hb hu)))

lemma redI_Rg_diff (hp : 5 ≤ p) (a b : ℕ) :
    redI p (C (Rg p o b - Rg p o a)) =
      rfC p (cyclicPrefix (fun x : ZMod p => x⁻¹ - (x - (4 : ZMod p)⁻¹ * (o : ZMod p))⁻¹) b -
        cyclicPrefix (fun x : ZMod p => x⁻¹ - (x - (4 : ZMod p)⁻¹ * (o : ZMod p))⁻¹) a) := by
  have g := (good_regularPrefix (p := p) (o:ℤ) (four_ne_zmod p hp) b).sub
    (good_regularPrefix (p := p) (o:ℤ) (four_ne_zmod p hp) a)
  rw [Rg_eq_regularPrefix, Rg_eq_regularPrefix, redI_C g.mem, g.eq]
  simp

lemma redI_h_sub_sumSr {Z : Type} [Fintype Z] [DecidableEq Z] {xs ys : Z → ℕ}
    (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) (hr : r≤N) (hx : ∀ z, xs z<N) (z : Z)
    (hxz : r ≤ xs z) :
    redI p (ChainModel.h Fr p r xs ys - ∑ m, Sr Fr p r xs ys z m) =
      redI p (ChainModel.h Fr p r xs ys) * srcB Fr p o r (xs z) := by
  have hSr : ∀ m, GLE p 0 (Sr Fr p r xs ys z m) := fun m =>
    gle0_of_int1 (Sr_int1 hL hp hN hr hx z m)
  have hh := gle0_h (xs := xs) (ys := ys) hL hp hN hr
  have hs := sum_redI_Sr_chain (ys := ys) hL hp hN hr hx z hxz (fun _ => 1)
  simp only [mul_one] at hs
  rw [redI_sub hh (GLE.sum fun m _ => hSr m), redI_sum _ _ (fun m _ => hSr m), hs]
  unfold srcB sourceB
  ring

end GammaDiff

section GammaDiff2
open ChainModel ChainClasses LemmaE
variable {p r N o k : ℕ} [Fact p.Prime] {Fr : Frame} {Z1 Z2 : Type} [Fintype Z1] [DecidableEq Z1]
  [Fintype Z2] [DecidableEq Z2] {xs1 ys1 : Z1 → ℕ} {xs2 ys2 : Z2 → ℕ}

/-- **The difference of the one-node function `Γ` between two nodes of a cell, reduced.** -/
theorem gamma_diff (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) (hr : r≤N)
    (hk : (4:ZMod p)*k=(o:ZMod p)) (hx1 : ∀ z, xs1 z<N) (hx2 : ∀ z, xs2 z<N)
    (hQ : Q Fr p r xs1 ys1 = Q Fr p r xs2 ys2)
    {a b : ℚ[X]} (ha : Int1 p a) (hb : Int1 p b) (z1 : Z1) (z2 : Z2)
    (hz1 : r ≤ xs1 z1) (hz2 : r ≤ xs2 z2)
    (hnc1 : xs1 z1 ≤ xs2 z2 →
      NoCut (Cut (p:ℤ) (r:ℤ) (Singular (p:ℤ) (o:ℤ))) (xs1 z1 : ℤ) (xs2 z2 : ℤ))
    (hnc2 : xs2 z2 ≤ xs1 z1 →
      NoCut (Cut (p:ℤ) (r:ℤ) (Singular (p:ℤ) (o:ℤ))) (xs2 z2 : ℤ) (xs1 z1 : ℤ))
    (hA1 : redI p a = redI p (Q Fr p r xs1 ys1).det * srcB Fr p o r (xs1 z1))
    (hB1 : redI p b = redI p (Q Fr p r xs1 ys1).det * srcA Fr p o r (xs1 z1))
    (hsA : srcA Fr p o r (xs2 z2) = srcA Fr p o r (xs1 z1))
    (hsB : srcB Fr p o r (xs2 z2) = srcB Fr p o r (xs1 z1))
    (hΓ1 : GLE p 0 (gamF p a b (aR Fr p r xs1 ys1 z1) (bR Fr p r xs1 ys1 z1)))
    (hΓ2 : GLE p 0 (gamF p a b (aR Fr p r xs2 ys2 z2) (bR Fr p r xs2 ys2 z2))) :
    redI p (ChainModel.h Fr p r xs1 ys1) ^ 2 *
        (redI p (gamF p a b (aR Fr p r xs1 ys1 z1) (bR Fr p r xs1 ys1 z1)) -
          redI p (gamF p a b (aR Fr p r xs2 ys2 z2) (bR Fr p r xs2 ys2 z2))) =
      redI p (Q Fr p r xs1 ys1).det *
        (-(redI p (ChainModel.h Fr p r xs1 ys1))^2 * redI p (Q Fr p r xs1 ys1).det *
            srcB Fr p o r (xs1 z1) ^ 2 *
            rfC p (cyclicPrefix (fun x : ZMod p => x⁻¹ - (x - (4 : ZMod p)⁻¹ * (o : ZMod p))⁻¹)
              (xs2 z2) -
              cyclicPrefix (fun x : ZMod p => x⁻¹ - (x - (4 : ZMod p)⁻¹ * (o : ZMod p))⁻¹)
              (xs1 z1)) -
          (redI p (ChainModel.h Fr p r xs1 ys1))^2 * redI p (Q Fr p r xs1 ys1).det *
            ∑ c : ZMod p, (rfC p ((16 * (c - ((xs1 z1 : ℕ) : ZMod p)))⁻¹) -
                rfC p ((16 * (c - ((xs2 z2 : ℕ) : ZMod p)))⁻¹)) *
              respAt Fr p o r c (srcA Fr p o r (xs1 z1)) (srcB Fr p o r (xs1 z1))) := by
  classical
  have hQ0 : Q0 Fr p r xs1 ys1 = Q0 Fr p r xs2 ys2 := by unfold Q0; rw [hQ]
  have hh : ChainModel.h Fr p r xs1 ys1 = ChainModel.h Fr p r xs2 ys2 := by
    unfold ChainModel.h; rw [hQ0]
  have hg : (Q Fr p r xs2 ys2).det = (Q Fr p r xs1 ys1).det := by rw [hQ]
  have hε : (0:ℝ) ≤ ((p:ℝ)⁻¹)^2 := by
    have : (0:ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    positivity
  set gb := redI p (Q Fr p r xs1 ys1).det with hgb
  obtain ⟨Y1, hY1g, hY1r, hY1b⟩ := rho_node (ys := ys1) hL hp hN hr hk hx1 ha hb gb z1 hz1 hA1 hB1
  have hA2 : redI p a = gb * srcB Fr p o r (xs2 z2) := by rw [hsB]; exact hA1
  have hB2 : redI p b = gb * srcA Fr p o r (xs2 z2) := by rw [hsA]; exact hB1
  obtain ⟨Y2, hY2g, hY2r, hY2b⟩ := rho_node (ys := ys2) hL hp hN hr hk hx2 ha hb gb z2 hz2 hA2 hB2
  rw [← hh, hg] at hY2b
  rw [← hh, hsA, hsB] at hY2r
  have W := Wown_cmp hL hp hN hr hx1 hx2 hQ0 z1 z2 hz1 hz2 hnc1 hnc2 ha hb
  set R : ℚ := Rg p o (xs2 z2) - Rg p o (xs1 z1) with hRdef
  set h := ChainModel.h Fr p r xs1 ys1 with hhdef
  set g := (Q Fr p r xs1 ys1).det with hgdef
  set σ := ∑ m, Sr Fr p r xs1 ys1 z1 m with hσ
  set Γ1 := gamF p a b (aR Fr p r xs1 ys1 z1) (bR Fr p r xs1 ys1 z1) with hΓ1d
  set Γ2 := gamF p a b (aR Fr p r xs2 ys2 z2) (bR Fr p r xs2 ys2 z2) with hΓ2d
  set D' : ℚ[X] := h ^ 2 * (Γ1 - Γ2) - g * (-(h * (a * C R * (h - σ))) + (Y1 - Y2)) with hD'
  -- C p * D' is small
  have hCD : C (p : ℚ) * D' =
      (h ^ 2 * (a * bR Fr p r xs1 ys1 z1 - b * aR Fr p r xs1 ys1 z1) - g * (h * Wown Fr p r xs1 ys1 a b z1 + C (p:ℚ) * Y1)) -
      (h ^ 2 * (a * bR Fr p r xs2 ys2 z2 - b * aR Fr p r xs2 ys2 z2) - g * (h * Wown Fr p r xs2 ys2 a b z2 + C (p:ℚ) * Y2)) +
      g * h * (Wown Fr p r xs1 ys1 a b z1 - Wown Fr p r xs2 ys2 a b z2 +
        a * C ((p:ℚ) * R) * (h - σ)) := by
    have e1 := Cp_mul_gamF (p := p) a b (aR Fr p r xs1 ys1 z1) (bR Fr p r xs1 ys1 z1)
    have e2 := Cp_mul_gamF (p := p) a b (aR Fr p r xs2 ys2 z2) (bR Fr p r xs2 ys2 z2)
    have e3 : (C ((p:ℚ) * R) : ℚ[X]) = C (p:ℚ) * C R := by rw [map_mul]
    rw [hD', e3]
    linear_combination (h ^ 2) * e1 - (h ^ 2) * e2
  have hgn1 : gn p g ≤ 1 := (ChainModel.Q_primitive (xs := xs1) (ys := ys1) hL hp hN hr).le
  have hhn1 : gn p h ≤ 1 := by
    have := (gle_iff_gn p 0 _).1 (gle0_h (xs := xs1) (ys := ys1) hL hp hN hr)
    simpa using this
  have hbound : gn p (C (p:ℚ) * D') ≤ ((p:ℝ)⁻¹)^2 := by
    rw [hCD]
    refine (gn_add_le _ _).trans (max_le ?_ ?_)
    · rw [sub_eq_add_neg]
      refine (gn_add_le _ _).trans (max_le hY1b ?_)
      rw [gn_neg]; exact hY2b
    · rw [gn_mul]
      calc gn p (g * h) * _ ≤ 1 * ((p:ℝ)⁻¹)^2 := by
            refine mul_le_mul ?_ W (gn_nonneg p _) zero_le_one
            rw [gn_mul]
            exact mul_le_one₀ hgn1 (gn_nonneg p _) hhn1
        _ = _ := one_mul _
  have hp0 : (0:ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp1 : (1:ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hCp : gn p (C (p:ℚ)) = (p:ℝ)⁻¹ := by
    rw [gn_C, padicNorm.padicNorm_p_of_prime]; push_cast; rfl
  have hD'le : gn p D' ≤ (p:ℝ)⁻¹ := by
    rw [gn_mul, hCp] at hbound
    have hpi : (0:ℝ) < (p:ℝ)⁻¹ := by positivity
    have : (p:ℝ)⁻¹ * gn p D' ≤ (p:ℝ)⁻¹ * (p:ℝ)⁻¹ := by nlinarith [hbound]
    exact le_of_mul_le_mul_left this hpi
  have hlt : gn p D' < 1 := lt_of_le_of_lt hD'le (inv_lt_one_of_one_lt₀ hp1)
  -- integrality of the pieces
  have h0 : GLE p 0 h := gle0_h (xs := xs1) (ys := ys1) hL hp hN hr
  have g0 : GLE p 0 g := ChainModel.gle0_det hL hp hN hr
  have a0 : GLE p 0 a := gle0_of_int1 ha
  have CR0 : GLE p 0 (C R) := by
    have hmem : R ∈ LocRing p := Subring.sub_mem _ (Rg_mem hp _) (Rg_mem hp _)
    exact GLE.C_iff.2 (by simpa using hmem)
  have hSr : ∀ m, GLE p 0 (Sr Fr p r xs1 ys1 z1 m) := fun m =>
    gle0_of_int1 (Sr_int1 hL hp hN hr hx1 z1 m)
  have σ0 : GLE p 0 σ := GLE.sum fun m _ => hSr m
  have hs0 : GLE p 0 (h - σ) := gle0_of_int1 ((int1_of_gle0 h0).sub (int1_of_gle0 σ0))
  have rhs0 : GLE p 0 (g * (-(h * (a * C R * (h - σ))) + (Y1 - Y2))) :=
    gle0_mul g0 (gle0_of_int1 (((int1_of_gle0 (gle0_mul h0 (gle0_mul (gle0_mul a0 CR0) hs0))).neg).add
      ((int1_of_gle0 hY1g).sub (int1_of_gle0 hY2g))))
  have hh2 : GLE p 0 (h ^ 2) := by rw [pow_two]; exact gle0_mul h0 h0
  have lhs0 : GLE p 0 (h ^ 2 * (Γ1 - Γ2)) :=
    gle0_mul hh2 (gle0_of_int1 ((int1_of_gle0 hΓ1).sub (int1_of_gle0 hΓ2)))
  have hcng : Cng p (h ^ 2 * (Γ1 - Γ2)) (g * (-(h * (a * C R * (h - σ))) + (Y1 - Y2))) := hlt
  have hred := redI_cng lhs0 rhs0 hcng
  rw [redI_mul hh2 (gle0_of_int1 ((int1_of_gle0 hΓ1).sub (int1_of_gle0 hΓ2))),
    redI_sub hΓ1 hΓ2, redI_mul g0 (gle0_of_int1 (((int1_of_gle0 (gle0_mul h0
      (gle0_mul (gle0_mul a0 CR0) hs0))).neg).add ((int1_of_gle0 hY1g).sub (int1_of_gle0 hY2g)))),
    redI_add (gle0_of_int1 (int1_of_gle0 (gle0_mul h0 (gle0_mul (gle0_mul a0 CR0) hs0))).neg)
      (gle0_of_int1 ((int1_of_gle0 hY1g).sub (int1_of_gle0 hY2g))),
    redI_neg (gle0_mul h0 (gle0_mul (gle0_mul a0 CR0) hs0)),
    redI_mul h0 (gle0_mul (gle0_mul a0 CR0) hs0), redI_mul (gle0_mul a0 CR0) hs0,
    redI_mul a0 CR0, redI_sub hY1g hY2g, hA1, redI_h_sub_sumSr (ys := ys1) hL hp hN hr hx1 z1 hz1,
    hY1r, hY2r] at hred
  rw [redI_Rg_diff hp] at hred
  have hpow : redI p (h ^ 2) = redI p h ^ 2 := by
    rw [pow_two, redI_mul h0 h0, pow_two]
  rw [hpow] at hred
  rw [hred]
  have hS : ∑ c : ZMod p, (rfC p ((16 * (c - ((xs1 z1 : ℕ) : ZMod p)))⁻¹) -
        rfC p ((16 * (c - ((xs2 z2 : ℕ) : ZMod p)))⁻¹)) *
      respAt Fr p o r c (srcA Fr p o r (xs1 z1)) (srcB Fr p o r (xs1 z1)) =
      (∑ c : ZMod p, rfC p ((16 * (c - ((xs1 z1 : ℕ) : ZMod p)))⁻¹) *
        respAt Fr p o r c (srcA Fr p o r (xs1 z1)) (srcB Fr p o r (xs1 z1))) -
      ∑ c : ZMod p, rfC p ((16 * (c - ((xs2 z2 : ℕ) : ZMod p)))⁻¹) *
        respAt Fr p o r c (srcA Fr p o r (xs1 z1)) (srcB Fr p o r (xs1 z1)) := by
    simp only [sub_mul, Finset.sum_sub_distrib]
  rw [hS]
  have hgb' : redI p g = gb := rfl
  have hhh : redI p (ChainModel.h Fr p r xs1 ys1) = redI p h := rfl
  simp only [hgb', hhh]
  ring

end GammaDiff2

#print axioms CatalanCore.Arith.Hybrid.gamma_diff
end CatalanCore.Arith.Hybrid
