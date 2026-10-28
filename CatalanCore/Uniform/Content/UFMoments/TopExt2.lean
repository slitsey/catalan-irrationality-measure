module

public import CatalanCore.Uniform.Content.UFMoments.TopExt

@[expose] public section

/-!
# Top extensions: `vS7` vanishes at the residue of `t₀ - δ` when `t₀ - δ` is a core node

See `TopExt`.  `fib_gamma`: a fiber moment is the H2 quadratic form `γ = uᵀ Q̄⁻¹ u` of the colour
block.  `vS7_topext`: the derived weight vanishes at top-extension residues.
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.Smith

namespace CatalanCore.Uniform.Content.UFMoments

variable {p : ℕ} [hp : Fact p.Prime]

theorem res_ne_of_unit {x : GaussLoc p} (hx : IsUnit x) : res p x ≠ 0 :=
  (hx.map (res p)).ne_zero

/-- A fiber moment is the quadratic form of its colour block. -/
theorem fib_gamma {ι : Type*} [Fintype ι] [DecidableEq ι] (D : Matrix ι ι (GaussLoc p))
    (col : ι → ZMod p) (hD : IsUnit D.det) (hb : ∀ a b, col a ≠ col b → D a b = 0) (τ : ZMod p)
    (y : ι → GaussLoc p) :
    ∑ a ∈ univ.filter (fun a => col a = τ), res p ((D⁻¹ *ᵥ y) a) * res p (y a) =
      gamma ((blk D col τ).map (res p)) (fun i => res p (y i.1)) := by
  rw [fiber_moment D col hD hb τ y (res p)]
  have hU := (inv_restrict D col hD hb τ).1
  unfold gamma
  rw [map_inv_of_unit (res p) _ hU, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RingHom.map_mulVec, mul_comm]
  rfl

theorem det_map_res {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι (GaussLoc p)) :
    (M.map (res p)).det = res p M.det := by
  have := RingHom.map_det (res p) M
  rw [RingHom.mapMatrix_apply] at this
  convert this.symm using 2

section Main

variable {Fr : Frame} {q o N : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ]

/-- Residues of shifted Loewner entries agree. -/
theorem res_entry_shift (D : PoleData Fr p N) (hR : RegRed D) (hN : N < p * p) (u v δ : ℕ)
    (huv : ((u : ℕ) : ZMod p) = ((v : ℕ) : ZMod p)) (hu : u + δ < N) (hv : v + δ < N)
    (hwu : NoSingWin D u δ) (hwv : NoSingWin D v δ) :
    res p (algebraMap _ (GaussLoc p)
        (Polynomial.C (Hybrid.liftQ p ((p : ℚ) ^ 2 * Fr.Mn (u + δ) (v + δ))))) =
      res p (algebraMap _ (GaussLoc p)
        (Polynomial.C (Hybrid.liftQ p ((p : ℚ) ^ 2 * Fr.Mn u v)))) := by
  obtain ⟨x, hx⟩ := loewner_entry_shift D hR hN u v δ huv hu hv hwu hwv
  rw [hx, map_add, map_mul, map_pow, res_piL, zero_pow two_ne_zero, zero_mul, add_zero]

/-- Residues of shifted prefixes agree. -/
theorem res_ellL_shift (D : PoleData Fr p N) (hR : RegRed D) (a t δ : ℕ)
    (hat : ((a : ℕ) : ZMod p) = ((t : ℕ) : ZMod p)) (ha : a + δ < N) (ht : t + δ < N)
    (hwa : NoSingWin D a δ) (hwt : NoSingWin D t δ) :
    res p (ellL p Fr (a + δ)) = res p (ellL p Fr a) := by
  obtain ⟨x, hx⟩ := ellL_shift D hR a t δ hat ha ht hwa hwt
  rw [hx, ellL_kappa D t δ ht hwt]
  simp only [map_add, map_mul, map_pow, res_piL, zero_mul, zero_pow two_ne_zero, add_zero]

/-- **Top extensions: the derived weight vanishes.** -/
theorem vS7_topext (T : TwoTermData Fr q o) (hNle : N ≤ p * p)
    (hsq : ∀ t, 1 ≤ t → t < N → ¬ p ^ 2 ∣ q * t - o) (hnorm : Fr.norm ∈ S p)
    (hnorm0 : red p Fr.norm ≠ 0) (hN : N < p * p) (ho : (o : ZMod p) ≠ 0)
    (hq : (q : ZMod p) ≠ 0) {r : ℕ} (C : Finset ℕ) (hC : C = Finset.range r)
    (xs ys : κ → ℕ) (hc : ∀ a : C, (a : ℕ) < N) (hx : ∀ i, xs i < N) (hy : ∀ j, ys j < N)
    (t0 δ : ℕ) (ht0N : t0 < N) (hr : r ≤ t0) (hδ : δ ≤ t0) (hlt : t0 - δ < r)
    (hr3 : r ≤ t0 - δ + p) (htp : t0 < r + p) (hq' : (t0 - δ) / p = t0 / p)
    (hw : NoSingWin (twoTermPoleData T hNle hsq hnorm hnorm0) (t0 - δ) δ) :
    vS7 p q o Fr (fun a : C => (a : ℕ)) (sLift (fun a : C => (a : ℕ)) xs ys
      (hint_of_poleData (twoTermPoleData T hNle hsq hnorm hnorm0) hN hc hx hy)).toBlocks₁₁ t0
      ((t0 - δ : ℕ) : ZMod p) = 0 := by
  classical
  set D := twoTermPoleData T hNle hsq hnorm hnorm0
  set Q := (sLift (fun a : C => (a : ℕ)) xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₁
  set σ0 := loewRow p Fr (fun a : C => (a : ℕ)) t0
  set d := dirOf Fr (fun a : C => (a : ℕ)) Q t0 σ0
  set Dm := Dmat (fun a : C => (a : ℕ)) Q
  set y : C → GaussLoc p := fun a => ellL p Fr (a : ℕ) - d
  have hR := tt_regRed (p := p) T hNle hsq hnorm hnorm0
  have hQr := sLift_core_rel D hN (fun a : C => (a : ℕ)) xs ys hc hx hy
  have hdet := sLift_core_det (Fr := Fr) (fun a : C => (a : ℕ)) xs ys (hint_of_poleData D hN hc hx hy)
  have hDu := isUnit_Dmat_det D (fun a : C => (a : ℕ)) hc Q hQr hdet
  have hb : ∀ a b, colOf (p := p) (fun a : C => (a : ℕ)) a ≠ colOf (fun a : C => (a : ℕ)) b →
      Dm a b = 0 := by
    intro a b h; simp [Dm, Dmat, h]
  have hz := own_dir_zero Fr (fun a : C => (a : ℕ)) Q t0 σ0
    (isUnit_of_res_ne _ (hB0_auto D hN (fun a : C => (a : ℕ)) xs ys hc hx hy t0 ht0N))
  have hwt0 : ((t0 - δ + δ : ℕ)) = t0 := by omega
  -- entries of `Q` on one colour
  have hQe : ∀ a b : C, Q a b = Polynomial.C (Hybrid.liftQ p ((p : ℚ) ^ 2 * Fr.Mn a b)) +
      (if a = b then (X : (LocRing p)[X]) else 0) := fun a b =>
    sLift_core_entry D hN (fun a : C => (a : ℕ)) xs ys hc hx hy a b
  set col := colOf (p := p) (fun a : C => (a : ℕ))
  set E := topEquiv (p := p) C hC t0 δ hr hδ hlt hr3 htp hq'
  have hEs : ∀ j, ((E.symm (some j)).1 : ℕ) = (j.1 : ℕ) - δ := fun j => rfl
  have hEn : ((E.symm none).1 : ℕ) = t0 - δ := rfl
  have hjd : ∀ j : {a : C // col a = ((t0 : ℕ) : ZMod p)}, δ ≤ (j.1 : ℕ) ∧
      (((j.1 : ℕ) - δ : ℕ) : ZMod p) = ((t0 - δ : ℕ) : ZMod p) ∧ (j.1 : ℕ) - δ ≠ t0 - δ :=
    fun j => te_down (Finset.mem_range.1 ((Finset.ext_iff.1 hC (j.1 : ℕ)).1 j.1.2)) hr hq' j.2
  have hwin : ∀ j : {a : C // col a = ((t0 : ℕ) : ZMod p)}, NoSingWin D ((j.1 : ℕ) - δ) δ :=
    fun j => window_periodic (x := (j.1 : ℕ) - δ) T hNle hsq hnorm hnorm0
      (by have := (hjd j).1; have := Finset.mem_range.1 ((Finset.ext_iff.1 hC (j.1 : ℕ)).1 j.1.2)
          omega) (hjd j).2.1 hw
  -- same-colour entries of `Dm`
  have hDm : ∀ a b : C, col a = col b → Dm a b = algebraMap _ (GaussLoc p) (Q a b) := by
    intro a b h; simp [Dm, Dmat, col, h]
  set B0 := blk Dm col ((t0 : ℕ) : ZMod p)
  set Bc := blk Dm col ((t0 - δ : ℕ) : ZMod p)
  set u0 : {a : C // col a = ((t0 : ℕ) : ZMod p)} → RatFunc (ZMod p) := fun i => res p (y i.1)
  set uc : {a : C // col a = ((t0 - δ : ℕ) : ZMod p)} → RatFunc (ZMod p) := fun i => res p (y i.1)
  have hU0 := (inv_restrict Dm col hDu hb ((t0 : ℕ) : ZMod p)).1
  have hUc := (inv_restrict Dm col hDu hb ((t0 - δ : ℕ) : ZMod p)).1
  set Qp := (Bc.map (res p)).submatrix E.symm E.symm
  have hsub : Qp.submatrix some some = B0.map (res p) := by
    ext j k
    simp only [Qp, B0, Bc, Matrix.submatrix_apply, Matrix.map_apply, blk]
    have hjk : col (E.symm (some j)).1 = col (E.symm (some k)).1 :=
      ((E.symm (some j)).2).trans ((E.symm (some k)).2).symm
    have hjk0 : col j.1 = col k.1 := j.2.trans k.2.symm
    rw [hDm _ _ hjk, hDm _ _ hjk0, hQe, hQe, map_add, map_add, map_add, map_add, hEs, hEs]
    have hiff : ((E.symm (some j)).1 = (E.symm (some k)).1) ↔ (j.1 = k.1) := by
      constructor
      · intro h
        have h1 : some j = some k := E.symm.injective (Subtype.ext h)
        rw [Option.some.inj h1]
      · intro h; rw [Subtype.ext h]
    have hshift := res_entry_shift D hR hN ((j.1 : ℕ) - δ) ((k.1 : ℕ) - δ) δ
      ((hjd j).2.1.trans (hjd k).2.1.symm)
      (by rw [Nat.sub_add_cancel (hjd j).1]; exact hc _)
      (by rw [Nat.sub_add_cancel (hjd k).1]; exact hc _) (hwin j) (hwin k)
    rw [Nat.sub_add_cancel (hjd j).1, Nat.sub_add_cancel (hjd k).1] at hshift
    rw [hshift]
    congr 2
    by_cases h : j.1 = k.1
    · rw [if_pos (hiff.2 h), if_pos h]
    · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h]
  have hvec : (uc ∘ E.symm) ∘ some = u0 := by
    funext j
    simp only [Function.comp, uc, u0, y, map_sub]
    congr 1
    have := res_ellL_shift (Fr := Fr) D hR ((j.1 : ℕ) - δ) (t0 - δ) δ (hjd j).2.1
      (by rw [Nat.sub_add_cancel (hjd j).1]; exact hc _) (by omega) (hwin j) hw
    rw [Nat.sub_add_cancel (hjd j).1] at this
    rw [hEs]; exact this.symm
  have hsF : ∀ j : {a : C // col a = ((t0 : ℕ) : ZMod p)},
      res p (algebraMap _ (GaussLoc p) (σ0 j.1)) = Qp none (some j) := by
    intro j
    simp only [Qp, Bc, Matrix.submatrix_apply, Matrix.map_apply, blk]
    have hcl : col (E.symm none).1 = col (E.symm (some j)).1 :=
      ((E.symm none).2).trans ((E.symm (some j)).2).symm
    have hne : (E.symm none).1 ≠ (E.symm (some j)).1 := by
      intro h
      have := congrArg Subtype.val h
      rw [hEn, hEs] at this
      exact (hjd j).2.2 this.symm
    rw [hDm _ _ hcl, hQe, if_neg hne, add_zero, hEn, hEs]
    have hshift := res_entry_shift D hR hN (t0 - δ) ((j.1 : ℕ) - δ) δ (hjd j).2.1.symm
      (by omega) (by rw [Nat.sub_add_cancel (hjd j).1]; exact hc _) hw (hwin j)
    rw [hwt0, Nat.sub_add_cancel (hjd j).1] at hshift
    rw [← hshift]
    rfl
  have hup : uc (E.symm none) = res p (ellL p Fr t0 - d) := by
    simp only [uc, y, map_sub]
    rw [hEn]
    have := res_ellL_shift (Fr := Fr) D hR (t0 - δ) (t0 - δ) δ rfl (by omega) (by omega) hw hw
    rw [hwt0] at this
    rw [this]
  have hs0 : ∀ a, col a ≠ ((t0 : ℕ) : ZMod p) → sOwn (fun a : C => (a : ℕ)) t0 σ0 a = 0 := by
    intro a h; exact if_neg h
  have hz' : res p (ellL p Fr t0 - d) =
      (fun j : {a : C // col a = ((t0 : ℕ) : ZMod p)} => res p (algebraMap _ (GaussLoc p) (σ0 j.1)))
        ⬝ᵥ ((B0.map (res p))⁻¹ *ᵥ u0) := by
    have h0 := congrArg (res p) hz
    rw [map_sub, map_zero, sub_eq_zero] at h0
    rw [h0, own_fiber_form Dm col hDu hb _ _ y hs0, map_sum, dotProduct_mulVec, dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, RingHom.map_vecMul, ← map_inv_of_unit (res p) _ hU0]
    congr 2
    funext k
    have hsk : sOwn (fun a : C => (a : ℕ)) t0 σ0 k.1 = algebraMap _ (GaussLoc p) (σ0 k.1) :=
      if_pos k.2
    exact congrArg (res p) hsk
  have htop : (fun j => Qp none (some j)) ⬝ᵥ ((Qp.submatrix some some)⁻¹ *ᵥ
      ((uc ∘ E.symm) ∘ some)) = (uc ∘ E.symm) none := by
    rw [hsub, hvec]
    show _ = uc (E.symm none)
    rw [hup, hz']
    congr 1
    funext j
    exact (hsF j).symm
  have hQd : (Qp.submatrix some some).det ≠ 0 := by
    rw [hsub, det_map_res]; exact res_ne_of_unit hU0
  have hQpd : Qp.det ≠ 0 := by
    simp only [Qp]
    rw [Matrix.det_submatrix_equiv_self, det_map_res]; exact res_ne_of_unit hUc
  have hm : fibMom (fun a : C => (a : ℕ)) Dm y ((t0 - δ : ℕ) : ZMod p) =
      fibMom (fun a : C => (a : ℕ)) Dm y ((t0 : ℕ) : ZMod p) := by
    unfold fibMom
    rw [fib_gamma Dm col hDu hb, fib_gamma Dm col hDu hb,
      ← gamma_reindex E.symm (Bc.map (res p)) uc,
      gamma_topExt Qp (uc ∘ E.symm) hQd hQpd htop, hsub, hvec]
  have hwT : wT p q o ((t0 - δ : ℕ) : ZMod p) = wT p q o ((t0 : ℕ) : ZMod p) := by
    have := wT_window T hNle hsq hnorm hnorm0 ho hq (t0 - δ) δ (by omega) hw
    rw [hwt0] at this
    exact this.symm
  have hm' : fibMom (fun a : C => (a : ℕ)) (Dmat (fun a : C => (a : ℕ)) Q)
      (fun a => ellL p Fr (a : ℕ) - d) ((t0 - δ : ℕ) : ZMod p) =
      fibMom (fun a : C => (a : ℕ)) (Dmat (fun a : C => (a : ℕ)) Q)
      (fun a => ellL p Fr (a : ℕ) - d) ((t0 : ℕ) : ZMod p) := hm
  show vDer Fr (fun a : C => (a : ℕ)) Q d (fun c' => rfH p (wT p q o c') *
      (rfH p (red p Fr.norm))⁻¹ - (rfH p (wT p q o ((t0 : ℕ) : ZMod p)) *
        (rfH p (red p Fr.norm))⁻¹ - fibMom (fun a : C => (a : ℕ)) (Dmat (fun a : C => (a : ℕ)) Q)
          (fun a => ellL p Fr (a : ℕ) - d) ((t0 : ℕ) : ZMod p))) ((t0 - δ : ℕ) : ZMod p) = 0
  simp only [vDer]
  rw [hwT, hm']
  ring

end Main

end CatalanCore.Uniform.Content.UFMoments
