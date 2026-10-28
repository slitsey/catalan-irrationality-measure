module

public import CatalanCore.Uniform.Content.UFWedge.Algebra
public import CatalanCore.Uniform.Content.UFMember.FiberMom
public import CatalanCore.Uniform.Content.UFMoments.JBlockK
public import CatalanCore.Uniform.Content.UFMoments.HB0
public import CatalanCore.Uniform.Content.UFMoments.FibTransport

@[expose] public section

/-!
# UF wedge: the kill wedge is the cross wedge of two bordered fibers (lane H9)

`wedgeC t = Z_t (A_t - ρ B_t)` and `ρ B_0 = A_0` where `ρ = res(n d)`, `d = dirOf t₀`, and
`A, B` are the bordered fiber determinants of `Algebra` (`Z_t ≠ 0` the determinant of the
complementary fibers).  Hence `wedgeC t ≠ 0` as soon as the cross wedge `B_0 A_t - A_0 B_t` of the
fibers of `t₀` and `t` is nonzero.  No unit hypothesis is needed.
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.UFMoments

namespace CatalanCore.Uniform.Content.UFWedge

variable {p N : ℕ} [Fact p.Prime] {Fr : Frame} {ι κ : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

/-- The bordered fiber of the residue `k` for a ring map `ρ` out of `ℤ_(p)[X]`. -/
noncomputable def fibOf {R : Type*} [CommRing R] (ρ : (LocRing p)[X] →+* R) (Fr : Frame) (c : ι → ℕ)
    (Q : Matrix ι ι (LocRing p)[X]) (σ : ι → (LocRing p)[X]) (z : (LocRing p)[X]) (k : ZMod p) :
    FibD R where
  n := {i // ((c i : ℕ) : ZMod p) = k}
  M := fun i j => ρ (Q i.1 j.1)
  s := fun i => ρ (σ i.1)
  u := fun j => ρ (PF1 p Fr (c j.1))
  z := ρ z

/-- Field-level local form: `det M (t - s M⁻¹ u) = Z · fibA` of the own fiber. -/
theorem local_form {K : Type*} [Field K] {n α : Type*} [Fintype n] [DecidableEq n] [DecidableEq α]
    (M : Matrix n n K) (col : n → α) (k : α) (hM : ∀ a b, col a ≠ col b → M a b = 0)
    (hdet : M.det ≠ 0) (t : K) (s u : n → K) (hs : ∀ i, col i ≠ k → s i = 0) :
    M.det * (t - s ⬝ᵥ (M⁻¹ *ᵥ u)) =
      (M.toSquareBlockProp fun i => ¬ col i = k).det *
        fibA (M.toSquareBlockProp fun i => col i = k) (fun i => s i.1) (fun i => u i.1) t := by
  have h := bordered_local M col k hM hdet t s u hs
  have hu : IsUnit M.det := isUnit_iff_ne_zero.2 hdet
  rw [← adj_moment M hu s u t, h]
  rfl

theorem local_ne {K : Type*} [Field K] {n α : Type*} [Fintype n] [DecidableEq n] [DecidableEq α]
    (M : Matrix n n K) (col : n → α) (k : α) (hM : ∀ a b, col a ≠ col b → M a b = 0)
    (hdet : M.det ≠ 0) :
    (M.toSquareBlockProp fun i => ¬ col i = k).det ≠ 0 := by
  intro h
  apply hdet
  rw [det_color_split M col k hM, h, mul_zero]

section Sl

variable (D : PoleData Fr p N) (hN : N < p * p) (c : ι → ℕ) (xs ys : κ → ℕ)
  (hc : ∀ a, c a < N) (hx : ∀ i, xs i < N) (hy : ∀ j, ys j < N)

/-- **`ρ B₀ = A₀`**: the residue of the direction of `t₀` is the ratio of its fiber `A, B`. -/
theorem dir_rel (t0 : ℕ) (ht0 : t0 < N) :
    res p (algebraMap (LocRing p)[X] (GaussLoc p) (nL p Fr) *
        dirOf Fr c (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₁ t0
          (loewRow p Fr c t0)) *
      (fibOf (phiP p) Fr c (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₁
        (loewRow p Fr c t0) (PF1 p Fr t0) ((t0 : ℕ) : ZMod p)).B =
    (fibOf (phiP p) Fr c (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₁
        (loewRow p Fr c t0) (PF1 p Fr t0) ((t0 : ℕ) : ZMod p)).A := by
  classical
  set A := sLift c xs ys (hint_of_poleData D hN hc hx hy) with hAdef
  set Q := A.toBlocks₁₁ with hQdef
  set σ0 := loewRow p Fr c t0 with hσ0
  set d := dirOf Fr c Q t0 σ0 with hd
  set n := algebraMap (LocRing p)[X] (GaussLoc p) (nL p Fr) with hn
  have hQ := sLift_core_rel D hN c xs ys hc hx hy
  have hdet := sLift_core_det (Fr := Fr) c xs ys (hint_of_poleData D hN hc hx hy)
  have hB0 := hB0_auto D hN c xs ys hc hx hy t0 ht0
  have hz := own_dir_zero Fr c Q t0 σ0 (isUnit_of_res_ne _ hB0)
  have hDu := isUnit_Dmat_det D c hc Q hQ hdet
  set g0 := sOwn c t0 σ0 ᵥ* (Dmat c Q)⁻¹ with hg0
  -- step 1: the linear relation in `GaussLoc p`
  rw [dot_sub_const g0 (fun a => ellL p Fr (c a)) d] at hz
  have h1 : algebraMap (LocRing p)[X] (GaussLoc p) (PF1 p Fr t0) -
      g0 ⬝ᵥ (fun a => algebraMap (LocRing p)[X] (GaussLoc p) (PF1 p Fr (c a))) =
      (n * d) * (1 - ∑ j, g0 j) := by
    have hP : g0 ⬝ᵥ (fun a => algebraMap (LocRing p)[X] (GaussLoc p) (PF1 p Fr (c a))) =
        n * (g0 ⬝ᵥ fun a => ellL p Fr (c a)) := by
      simp only [dotProduct, algebraMap_PF1 D, Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => by ring
    rw [hP, algebraMap_PF1 D t0, ← sub_eq_zero]
    calc n * ellL p Fr t0 - n * (g0 ⬝ᵥ fun a => ellL p Fr (c a)) - n * d * (1 - ∑ j, g0 j)
        = n * ((ellL p Fr t0 - d) - (g0 ⬝ᵥ (fun a => ellL p Fr (c a)) - d * ∑ j, g0 j)) := by ring
      _ = 0 := by rw [hz, mul_zero]
  -- step 2: residues
  have h2 := congrArg (res p) h1
  rw [map_sub, res_algebraMap, RingHom.map_dotProduct, map_mul, map_sub, map_one, map_sum] at h2
  -- step 3: residue of the own-fiber vector
  set Qb : Matrix ι ι (RatFunc (ZMod p)) := Q.map (phiP p) with hQb
  set st : ι → RatFunc (ZMod p) := fun a => res p (sOwn c t0 σ0 a) with hst
  have hres_D : (Dmat c Q).map (res p) = Qb := by
    ext a b
    simp only [Matrix.map_apply, Dmat, Matrix.of_apply, Qb, hQb]
    by_cases hab : colOf (p := p) c a = colOf c b
    · rw [if_pos hab, res_algebraMap]
    · rw [if_neg hab, map_zero]
      have := core_red_color D hN c xs ys hc hx hy a b hab
      simpa [hQdef, hAdef] using this.symm
  have hg : (fun j => res p (g0 j)) = st ᵥ* Qb⁻¹ := by
    funext j
    rw [hg0, RingHom.map_vecMul, ← hres_D, map_inv_of_unit (res p) _ hDu]
    rfl
  have hu1 : (fun a => res p (algebraMap (LocRing p)[X] (GaussLoc p) (PF1 p Fr (c a)))) =
      fun a => phiP p (PF1 p Fr (c a)) := by
    funext a; rw [res_algebraMap]
  have h3 : phiP p (PF1 p Fr t0) - (st ᵥ* Qb⁻¹) ⬝ᵥ (fun a => phiP p (PF1 p Fr (c a))) =
      res p (n * d) * (1 - (st ᵥ* Qb⁻¹) ⬝ᵥ 1) := by
    have e1 : (fun j => res p (g0 j)) ⬝ᵥ (fun a => res p (algebraMap (LocRing p)[X] (GaussLoc p)
        (PF1 p Fr (c a)))) = (st ᵥ* Qb⁻¹) ⬝ᵥ (fun a => phiP p (PF1 p Fr (c a))) := by
      rw [hg, hu1]
    have e2 : ∑ j, res p (g0 j) = (st ᵥ* Qb⁻¹) ⬝ᵥ 1 := by
      rw [← hg, dotProduct_one]
    rw [← e1, ← e2]
    exact h2
  -- step 4: clear the inverse
  have hdetb : Qb.det ≠ 0 := by
    have : Qb.det = phiP p Q.det := by
      show (Q.map (phiP p)).det = _
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rw [this]; exact hdet
  have hsupp : ∀ i, coreCol (p := p) c i ≠ ((t0 : ℕ) : ZMod p) → st i = 0 := by
    intro i hi
    have hi' : ¬ colOf (p := p) c i = ((t0 : ℕ) : ZMod p) := hi
    simp [hst, sOwn, hi']
  have hstF : ∀ i : {i // ((c i : ℕ) : ZMod p) = ((t0 : ℕ) : ZMod p)},
      st i.1 = phiP p (σ0 i.1) := by
    intro i
    have hi : colOf (p := p) c i.1 = ((t0 : ℕ) : ZMod p) := i.2
    simp [hst, sOwn, hi, res_algebraMap]
  have hbl := local_form Qb (coreCol (p := p) c) ((t0 : ℕ) : ZMod p)
    (fun a b hab => core_red_color D hN c xs ys hc hx hy a b hab) hdetb
  have hZ := local_ne Qb (coreCol (p := p) c) ((t0 : ℕ) : ZMod p)
    (fun a b hab => core_red_color D hN c xs ys hc hx hy a b hab) hdetb
  have hA := hbl (phiP p (PF1 p Fr t0)) st (fun a => phiP p (PF1 p Fr (c a))) hsupp
  have hB := hbl 1 st (fun _ => 1) hsupp
  rw [Matrix.dotProduct_mulVec] at hA hB
  set Z := (Qb.toSquareBlockProp fun i => ¬ coreCol (p := p) c i = ((t0 : ℕ) : ZMod p)).det
  set Bf := (fibOf (phiP p) Fr c Q σ0 (PF1 p Fr t0) ((t0 : ℕ) : ZMod p)).B with hBf
  set Af := (fibOf (phiP p) Fr c Q σ0 (PF1 p Fr t0) ((t0 : ℕ) : ZMod p)).A with hAf
  have hAeq : Af = fibA (Qb.toSquareBlockProp fun i => coreCol (p := p) c i = ((t0 : ℕ) : ZMod p))
      (fun i => st i.1) (fun i => phiP p (PF1 p Fr (c i.1))) (phiP p (PF1 p Fr t0)) := by
    show fibA _ _ _ _ = _
    congr 1
    funext i
    exact (hstF i).symm
  have hBeq : Bf = fibA (Qb.toSquareBlockProp fun i => coreCol (p := p) c i = ((t0 : ℕ) : ZMod p))
      (fun i => st i.1) (fun _ => 1) 1 := by
    show fibA _ _ _ _ = _
    congr 1
    funext i
    exact (hstF i).symm
  have hB' : Qb.det * (1 - (st ᵥ* Qb⁻¹) ⬝ᵥ (1 : ι → RatFunc (ZMod p))) = Z * Bf := by
    rw [hBeq]; exact hB
  have hA' : Qb.det * (phiP p (PF1 p Fr t0) - (st ᵥ* Qb⁻¹) ⬝ᵥ (fun a => phiP p (PF1 p Fr (c a)))) =
      Z * Af := by
    rw [hAeq]; exact hA
  have hfin : Z * (res p (n * d) * Bf) = Z * Af := by
    linear_combination (-(res p (n * d))) * hB' + hA' - Qb.det * h3
  exact mul_left_cancel₀ hZ hfin

end Sl


section Wedge

variable (D : PoleData Fr p N) (hN : N < p * p) (c : ι → ℕ) (xs ys : κ → ℕ)
  (hc : ∀ a, c a < N) (hx : ∀ i, xs i < N) (hy : ∀ j, ys j < N)

theorem qred_det_ne :
    (Qred (sLift c xs ys (hint_of_poleData D hN hc hx hy))).det ≠ 0 := by
  rw [← phiP_det]
  exact sLift_core_det (Fr := Fr) c xs ys (hint_of_poleData D hN hc hx hy)

theorem qred_symm :
    (Qred (sLift c xs ys (hint_of_poleData D hN hc hx hy)))ᵀ =
      Qred (sLift c xs ys (hint_of_poleData D hN hc hx hy)) := by
  unfold Qred
  rw [← Matrix.transpose_map, sLift_core_symm D hN c xs ys hc hx hy]

/-- **A column kill wedge is the cross wedge of the two fibers (W1, reduction).** -/
theorem wedgeC_ne_zero_of_cross (t0 : ℕ) (ht0 : t0 < N) (t : κ)
    (h : (fibOf (phiP p) Fr c (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₁
        (loewRow p Fr c t0) (PF1 p Fr t0) ((t0 : ℕ) : ZMod p)).cross
      (fibOf (phiP p) Fr c (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₁
        (fun a => (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₂ a t)
        (PF1 p Fr (ys t)) ((ys t : ℕ) : ZMod p)) ≠ 0) :
    wedgeC (sLift c xs ys (hint_of_poleData D hN hc hx hy)) Fr c ys
      (dirOf Fr c (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₁ t0
        (loewRow p Fr c t0)) t ≠ 0 := by
  classical
  intro hw
  set A := sLift c xs ys (hint_of_poleData D hN hc hx hy) with hAdef
  set F0 := fibOf (phiP p) Fr c A.toBlocks₁₁ (loewRow p Fr c t0) (PF1 p Fr t0)
    ((t0 : ℕ) : ZMod p) with hF0
  set Ft := fibOf (phiP p) Fr c A.toBlocks₁₁ (fun a => A.toBlocks₁₂ a t) (PF1 p Fr (ys t))
    ((ys t : ℕ) : ZMod p) with hFt
  set r := res p (algebraMap (LocRing p)[X] (GaussLoc p) (nL p Fr) *
    dirOf Fr c A.toBlocks₁₁ t0 (loewRow p Fr c t0)) with hr
  have hrel : r * F0.B = F0.A := dir_rel D hN c xs ys hc hx hy t0 ht0
  have hsym := qred_symm D hN c xs ys hc hx hy
  have hdetb := qred_det_ne D hN c xs ys hc hx hy
  have hZ := local_ne (Qred A) (coreCol (p := p) c) ((ys t : ℕ) : ZMod p)
    (fun a b hab => core_red_color D hN c xs ys hc hx hy a b hab) hdetb
  have hA1 := colMomA_red D hN c xs ys hc hx hy t
  have hB1 := colMomB1_red D hN c xs ys hc hx hy t
  dsimp only at hA1 hB1
  rw [hsym] at hA1 hB1
  set Z := ((Qred A).toSquareBlockProp fun i => ¬ coreCol (p := p) c i = ((ys t : ℕ) : ZMod p)).det
  have eA : phiP p (colMomA A t) = Z * Ft.B := hA1
  have eB : phiP p (colMomB1 A Fr c ys t) = Z * Ft.A := hB1
  unfold wedgeC at hw
  rw [eA, eB, ← hr] at hw
  have h1 : Ft.A = r * Ft.B := by
    apply mul_left_cancel₀ hZ
    linear_combination hw
  apply h
  unfold FibD.cross
  rw [h1, ← hrel]
  ring

/-- **A row kill wedge is the cross wedge of the two fibers (W1, reduction).** -/
theorem wedgeR_ne_zero_of_cross (t0 : ℕ) (ht0 : t0 < N) (t : κ)
    (h : (fibOf (phiP p) Fr c (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₁
        (loewRow p Fr c t0) (PF1 p Fr t0) ((t0 : ℕ) : ZMod p)).cross
      (fibOf (phiP p) Fr c (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₁
        (fun a => (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₂₁ t a)
        (PF1 p Fr (xs t)) ((xs t : ℕ) : ZMod p)) ≠ 0) :
    wedgeR (sLift c xs ys (hint_of_poleData D hN hc hx hy)) Fr c xs
      (dirOf Fr c (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₁ t0
        (loewRow p Fr c t0)) t ≠ 0 := by
  classical
  intro hw
  set A := sLift c xs ys (hint_of_poleData D hN hc hx hy) with hAdef
  set F0 := fibOf (phiP p) Fr c A.toBlocks₁₁ (loewRow p Fr c t0) (PF1 p Fr t0)
    ((t0 : ℕ) : ZMod p) with hF0
  set Ft := fibOf (phiP p) Fr c A.toBlocks₁₁ (fun a => A.toBlocks₂₁ t a) (PF1 p Fr (xs t))
    ((xs t : ℕ) : ZMod p) with hFt
  set r := res p (algebraMap (LocRing p)[X] (GaussLoc p) (nL p Fr) *
    dirOf Fr c A.toBlocks₁₁ t0 (loewRow p Fr c t0)) with hr
  have hrel : r * F0.B = F0.A := dir_rel D hN c xs ys hc hx hy t0 ht0
  have hdetb := qred_det_ne D hN c xs ys hc hx hy
  have hZ := local_ne (Qred A) (coreCol (p := p) c) ((xs t : ℕ) : ZMod p)
    (fun a b hab => core_red_color D hN c xs ys hc hx hy a b hab) hdetb
  have hA1 := rowMomA_red D hN c xs ys hc hx hy t
  have hB1 := rowMomB1_red D hN c xs ys hc hx hy t
  dsimp only at hA1 hB1
  set Z := ((Qred A).toSquareBlockProp fun i => ¬ coreCol (p := p) c i = ((xs t : ℕ) : ZMod p)).det
  have eA : phiP p (rowMomA A t) = Z * Ft.B := hA1
  have eB : phiP p (rowMomB1 A Fr c xs t) = Z * Ft.A := hB1
  unfold wedgeR at hw
  rw [eA, eB, ← hr] at hw
  have hd : phiP p A.toBlocks₁₁.det ≠ 0 := by
    have := qred_det_ne D hN c xs ys hc hx hy
    rwa [← phiP_det] at this
  have hw' : Z * Ft.B * r - Z * Ft.A = 0 := by
    rcases div_eq_zero_iff.1 hw with h' | h'
    · exact h'
    · exact absurd h' hd
  have h1 : Ft.A = r * Ft.B := by
    apply mul_left_cancel₀ hZ
    linear_combination -hw'
  apply h
  unfold FibD.cross
  rw [h1, ← hrel]
  ring

end Wedge

end CatalanCore.Uniform.Content.UFWedge
