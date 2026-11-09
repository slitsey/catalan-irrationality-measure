module

public import CatalanCore.Uniform.Content.Sweep.SweepForm

@[expose] public section

/-!
# The instance `R = ℤ_(p)[X]_(p)` and the bridge to the polynomial family (lane H, wave H2b; ledger P204)

* `RP p = Localization.AtPrime (ker phiP)` with `ξ = xiP p = X`: `xiP_unitProp` (`UnitProp`, from
  `IsLocalization.map_units`), `pRad_RP` (`∀ x, IsUnit (1 + p x)`, from `IsLocalRing`; the instance
  diamond of `Localization` is avoided by the generic `pRad_of_local`).
* `descent`: `p^K ∣ g` in `RP p` gives `C p ^ K ∣ g` in `ℤ_(p)[X]` (`p` is prime in `ℤ_(p)[X]`).
* `gle_member`: if the `Q`-minor on the nodes of a member (`memRow`, `memCol`; diagonal only on the common
  block) is divisible by `p^K` in `RP p`, then `GLE p (3 (|ι| + |κ|) − K)` of the determinant of the member
  `seqFullN … X`, through `RankGLE.gle_det_of_scaled_dvd` with `x = X/p³` and `GLE e P(X/p³) ⇒ GLE e P`.
-/

open Polynomial Finset Matrix CatalanCore.Basic CatalanCore.Arith.Hybrid
open CatalanCore.Uniform.Support CatalanCore CatalanCore.Rect

namespace CatalanCore.Uniform.Content.Sweep

section RInst

variable (p : ℕ) [hp : Fact p.Prime]

/-- The prime ideal `(p)` of `ℤ_(p)[X]`, as the kernel of the reduction to `𝔽_p(X)`. -/
noncomputable def Pp : Ideal (LocRing p)[X] := RingHom.ker (phiP p)

instance Pp_isPrime : (Pp p).IsPrime := RingHom.ker_isPrime _

/-- `R = ℤ_(p)[X]_(p)`. -/
abbrev RP := Localization.AtPrime (Pp p)

/-- The variable `ξ = X` of `ℤ_(p)[X]_(p)`. -/
noncomputable def xiP : RP p := algebraMap ((LocRing p)[X]) (RP p) X

theorem aeval_xiP (g : (LocRing p)[X]) :
    Polynomial.aeval (xiP p) g = algebraMap ((LocRing p)[X]) (RP p) g := by
  have h := Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom (LocRing p) ((LocRing p)[X]) (RP p)) (X : (LocRing p)[X]) g
  simp only [IsScalarTower.coe_toAlgHom'] at h
  rw [Polynomial.aeval_X_left_apply] at h
  exact h

theorem mem_Pp_iff (g : (LocRing p)[X]) : g ∈ Pp p ↔ phiP p g = 0 := RingHom.mem_ker

theorem xiP_unitProp : UnitProp p (xiP p) := by
  intro g hg
  rw [aeval_xiP]
  exact IsLocalization.map_units (RP p) (⟨g, fun h => hg ((mem_Pp_iff p g).1 h)⟩ : (Pp p).primeCompl)

theorem natCast_RP : ((p : ℕ) : RP p) = algebraMap ((LocRing p)[X]) (RP p) (C ((p : ℕ) : LocRing p)) := by
  rw [map_natCast C p, map_natCast]

theorem p_nonunit_RP : ¬ IsUnit ((p : ℕ) : RP p) := by
  rw [natCast_RP]
  intro hu
  have hmax : algebraMap ((LocRing p)[X]) (RP p) (C ((p : ℕ) : LocRing p)) ∈ IsLocalRing.maximalIdeal (RP p) := by
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff (RP p) (Pp p)]
    rw [mem_Pp_iff, phiP_eq_zero_iff]
  exact hmax hu

theorem pRad_of_local {R : Type*} [CommRing R] [IsLocalRing R] (q : R) (hq : ¬ IsUnit q) :
    ∀ x : R, IsUnit (1 + q * x) := by
  intro x
  have h1 : ¬ IsUnit (q * x) := fun h => hq (isUnit_of_mul_isUnit_left h)
  have h2 : -(q * x) ∈ nonunits R := by
    rw [mem_nonunits_iff]
    intro hu
    exact h1 (by simpa using hu.neg)
  have := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ h2
  simpa using this

noncomputable def pRad_RP := pRad_of_local (R := RP p) ((p : ℕ) : RP p) (p_nonunit_RP p)

/-- Descent from the localisation: `p^K ∣ g` in `ℤ_(p)[X]_(p)` gives `C p ^ K ∣ g` in `ℤ_(p)[X]`. -/
theorem descent {g : (LocRing p)[X]} {K : ℕ}
    (h : ((p : ℕ) : RP p) ^ K ∣ algebraMap ((LocRing p)[X]) (RP p) g) :
    C ((p : ℕ) : LocRing p) ^ K ∣ g := by
  obtain ⟨y, hy⟩ := h
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.mk'_surjective (Pp p).primeCompl y
  have hmk := IsLocalization.mk'_spec (RP p) a s
  have hs' : IsLocalization.mk' (RP p) a s = y := hs
  rw [← hs'] at hy
  have h2 : algebraMap ((LocRing p)[X]) (RP p) (g * (s : (LocRing p)[X])) =
      algebraMap ((LocRing p)[X]) (RP p) (C ((p : ℕ) : LocRing p) ^ K * a) := by
    rw [map_mul, hy, map_mul, map_pow, ← natCast_RP, ← hmk]; ring
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists (Pp p).primeCompl (RP p)).1 h2
  have hcs : (c : (LocRing p)[X]) * s ∈ (Pp p).primeCompl := (Pp p).primeCompl.mul_mem c.2 s.2
  have hprime : Prime (C ((p : ℕ) : LocRing p) : (LocRing p)[X]) :=
    Polynomial.prime_C_iff.2 (prime_p p)
  have hnd : ¬ C ((p : ℕ) : LocRing p) ∣ (c : (LocRing p)[X]) * s := by
    intro hd
    exact hcs ((mem_Pp_iff p _).2 ((phiP_eq_zero_iff p _).2 hd))
  refine hprime.pow_dvd_of_dvd_mul_left K hnd ?_
  exact ⟨c * a, by linear_combination hc⟩

end RInst

section Member

variable {p : ℕ} [hp : Fact p.Prime] (v u : ℤ) {N : ℕ}
  {ι κw : Type} [Fintype ι] [DecidableEq ι] [Fintype κw] [DecidableEq κw]
  (c : ι → ℕ) (xs ys : κw → ℕ)

/-- The nodes of the rows and columns of the member. -/
def memRow : ι ⊕ κw → ℕ := Sum.elim c xs
def memCol : ι ⊕ κw → ℕ := Sum.elim c ys

/-- The `p³`-scaled member matrix over `ℤ_(p)[X]`. -/
noncomputable def BlM : Matrix (ι ⊕ κw) (ι ⊕ κw) (LocRing p)[X] :=
  Matrix.of fun a b => (if memRow c xs a = memCol c ys b then (X : (LocRing p)[X]) else 0) +
    C (toL p ((p : ℚ) ^ 3 * Lm v u (memRow c xs a) (memCol c ys b)))

/-- The minor of `Q` over `R` with the same nodes. -/
noncomputable def QminR {R : Type*} [CommRing R] [Algebra (LocRing p) R] (ξ : R) :
    Matrix (ι ⊕ κw) (ι ⊕ κw) R :=
  Matrix.of fun a b => Qent (p := p) v u ξ (memRow c xs a) (memCol c ys b)

theorem map_BlM {R : Type*} [CommRing R] [Algebra (LocRing p) R] (ξ : R)
    (f : (LocRing p)[X] →+* R) (hX : f X = ξ) (hC : ∀ x : LocRing p, f (C x) = algebraMap (LocRing p) R x)
    (hN : 2 * N < p * p) (hr : ∀ a, memRow c xs a < N) (hc : ∀ b, memCol c ys b < N) :
    f.mapMatrix (BlM (p := p) v u c xs ys) = QminR (p := p) v u c xs ys ξ := by
  ext a b
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, BlM, QminR, Matrix.of_apply, Qent, map_add]
  congr 1
  · split_ifs <;> simp [hX]
  · rw [hC, toR_eq_algebraMap_toL]

omit [Fact p.Prime] in
theorem seqFullN_entry {R : Type*} [CommRing R] [Algebra ℚ R] (f g : ℕ → ℚ) (x : R)
    (hcinj : Function.Injective c) (h1 : ∀ i j, c i ≠ ys j) (h2 : ∀ i j, xs i ≠ c j)
    (h3 : ∀ i j, xs i ≠ ys j) (a b : ι ⊕ κw) :
    seqFullN f g c xs ys x a b =
      (if memRow c xs a = memCol c ys b then x else 0) +
        algebraMap ℚ R (lw f g (memRow c xs a) (memCol c ys b)) := by
  rcases a with a | a <;> rcases b with b | b
  · simp only [seqFullN, Rect.Blk, Matrix.fromBlocks_apply₁₁, Matrix.add_apply, Matrix.smul_apply,
      Matrix.one_apply, Matrix.of_apply, smul_eq_mul, memRow, memCol, Sum.elim_inl, hcinj.eq_iff]
    by_cases hab : a = b <;> simp [hab, add_comm]
  · simp only [seqFullN, Rect.Blk, Matrix.fromBlocks_apply₁₂, Matrix.of_apply, memRow, memCol,
      Sum.elim_inl, Sum.elim_inr, h1 a b, if_false, zero_add]
  · simp only [seqFullN, Rect.Blk, Matrix.fromBlocks_apply₂₁, Matrix.of_apply, memRow, memCol,
      Sum.elim_inl, Sum.elim_inr, h2 a b, if_false, zero_add]
  · simp only [seqFullN, Rect.Blk, Matrix.fromBlocks_apply₂₂, Matrix.of_apply, memRow, memCol,
      Sum.elim_inr, h3 a b, if_false, zero_add]

/-- **Descent of the Schur bound to a member of the family.**  If the `Q`-minor on the nodes of a member
(retained common nodes `c`, window rows `xs`, window columns `ys`, with the diagonal only on the common
block) is divisible by `p^K` in `ℤ_(p)[X]_(p)` (with `ξ = X`), then every coefficient of the determinant of the
member with `x = X/p³` has `p`-adic denominator at most `3 (|ι| + |κ|) - K`; hence the same bound for the
determinant in the variable `X`. -/
theorem gle_member (hN : 2 * N < p * p) (hr : ∀ a, memRow c xs a < N) (hcl : ∀ b, memCol c ys b < N)
    (hcinj : Function.Injective c) (h1 : ∀ i j, c i ≠ ys j) (h2 : ∀ i j, xs i ≠ c j)
    (h3 : ∀ i j, xs i ≠ ys j) {K : ℕ}
    (hdvd : ((p : ℕ) : RP p) ^ K ∣ (QminR (p := p) v u c xs ys (xiP p)).det) :
    GLE p (3 * (Fintype.card ι + Fintype.card κw) - K)
      (seqFullN (fS v u) (eS v u) c xs ys (X : ℚ[X])).det := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  -- the minor over R
  have hmap := map_BlM (p := p) v u c xs ys (xiP p) (algebraMap ((LocRing p)[X]) (RP p)) rfl
    (fun x => by
      rw [IsScalarTower.algebraMap_apply (LocRing p) ((LocRing p)[X]) (RP p) x, Polynomial.algebraMap_eq])
    hN hr hcl
  have hd1 : ((p : ℕ) : RP p) ^ K ∣ algebraMap ((LocRing p)[X]) (RP p) (BlM (p := p) v u c xs ys).det := by
    have hm := RingHom.map_det (S := RP p) (algebraMap ((LocRing p)[X]) (RP p)) (BlM (p := p) v u c xs ys)
    rw [hm, hmap]; exact hdvd
  have hd2 := descent p hd1
  -- the scaled member
  set Mt : Matrix (ι ⊕ κw) (ι ⊕ κw) ℚ[X] :=
    seqFullN (fS v u) (eS v u) c xs ys (C (((p : ℚ) ^ 3)⁻¹) * X) with hMt
  have hB : ∀ a b : ι ⊕ κw, toQ p (BlM (p := p) v u c xs ys a b) =
      C ((p : ℚ) ^ ((fun _ : ι ⊕ κw => 3) a + (fun _ : ι ⊕ κw => 0) b)) * Mt a b := by
    intro a b
    have hq := q_mem v u hN (hr a) (hcl b)
    rw [hMt, seqFullN_entry c xs ys _ _ _ hcinj h1 h2 h3]
    simp only [BlM, Matrix.of_apply, map_add, toQ]
    rw [Polynomial.coe_mapRingHom]
    simp only [Polynomial.map_C, Polynomial.map_X, Subring.subtype_apply]
    rw [toL_val hq]
    have hc3 : (p : ℚ) ^ 3 * ((p : ℚ) ^ 3)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero 3 hp0)
    have hc3' : (p : ℚ) ^ (3 + 0) * ((p : ℚ) ^ 3)⁻¹ = 1 := by simpa using hc3
    split_ifs
    · rw [Polynomial.map_X, mul_add, ← mul_assoc, ← C_mul, hc3', Polynomial.C_1, one_mul,
        Polynomial.algebraMap_eq, ← C_mul]
    · rw [Polynomial.map_zero, zero_add, zero_add, Polynomial.algebraMap_eq, ← C_mul]
  have hG := gle_det_of_scaled_dvd p Mt (BlM (p := p) v u c xs ys) (fun _ => 3) (fun _ => 0) hB K hd2
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_zero, add_zero, Fintype.card_sum] at hG
  -- Mt is the composite of the member in X with X ↦ p⁻³ X
  set MX : Matrix (ι ⊕ κw) (ι ⊕ κw) ℚ[X] :=
    seqFullN (fS v u) (eS v u) c xs ys (X : ℚ[X]) with hMX
  have hcomp : Mt = (Polynomial.compRingHom (C (((p : ℚ) ^ 3)⁻¹) * X : ℚ[X])).mapMatrix MX := by
    ext a b
    rw [hMt, hMX, seqFullN_entry c xs ys _ _ _ hcinj h1 h2 h3, RingHom.mapMatrix_apply, Matrix.map_apply,
      seqFullN_entry c xs ys _ _ _ hcinj h1 h2 h3]
    split_ifs <;> simp
  have hdet : Mt.det = MX.det.comp (C (((p : ℚ) ^ 3)⁻¹) * X) := by
    rw [hcomp, ← RingHom.map_det]; rfl
  intro i
  have hi := hG i
  rw [hdet, Polynomial.comp_C_mul_X_coeff] at hi
  have hpi : ((p : ℚ) ^ (3 * i)) ∈ LocRing p := by
    exact_mod_cast int_mem_locRing (ℓ := p) ((p : ℤ) ^ (3 * i))
  have := (LocRing p).mul_mem hi hpi
  convert this using 1
  have hp3 : ((p : ℚ) ^ 3) ^ i ≠ 0 := pow_ne_zero _ (pow_ne_zero 3 hp0)
  rw [inv_pow, pow_mul]
  field_simp
  rw [Nat.mul_comm (Fintype.card ι + Fintype.card κw) 3]
  ring

end Member


/-- Descent for any scaled sequence pencil. The supplied local matrix carries all source
integrality obligations; no injectivity or separation premise is needed by descent. -/
theorem gle_member_h
    {p : ℕ} [Fact p.Prime] (h : ℕ) (f g : ℕ → ℚ)
    {ι κw : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κw] [DecidableEq κw]
    (c : ι → ℕ) (xs ys : κw → ℕ)
    (B : Matrix (ι ⊕ κw) (ι ⊕ κw) (LocRing p)[X])
    (hB : ∀ a b,
      toQ p (B a b) = C ((p : ℚ) ^ h) *
        seqFullN f g c xs ys (C (((p : ℚ) ^ h)⁻¹) * X) a b)
    {K : ℕ}
    (hdvd : ((p : ℕ) : RP p) ^ K ∣
      algebraMap ((LocRing p)[X]) (RP p) B.det) :
    GLE p (h * (Fintype.card ι + Fintype.card κw) - K)
      (seqFullN f g c xs ys (X : ℚ[X])).det := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  let Mt := seqFullN f g c xs ys (C (((p : ℚ) ^ h)⁻¹) * X)
  have hB' : ∀ a b : ι ⊕ κw, toQ p (B a b) =
      C ((p : ℚ) ^ ((fun _ : ι ⊕ κw => h) a + (fun _ : ι ⊕ κw => 0) b)) * Mt a b := by
    intro a b
    simpa only [Nat.add_zero] using hB a b
  have hG := gle_det_of_scaled_dvd p Mt B (fun _ => h) (fun _ => 0) hB' K (descent p hdvd)
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_zero, add_zero, Fintype.card_sum] at hG
  let MX := seqFullN f g c xs ys (X : ℚ[X])
  have hcomp : Mt = (Polynomial.compRingHom (C (((p : ℚ) ^ h)⁻¹) * X : ℚ[X])).mapMatrix MX := by
    apply Matrix.ext
    intro a b
    rcases a with a | a <;> rcases b with b | b <;>
      simp [Mt, MX, seqFullN, Blk, Matrix.fromBlocks, Matrix.one_apply]
    by_cases he : a = b <;> simp [he]
  have hdet : Mt.det = MX.det.comp (C (((p : ℚ) ^ h)⁻¹) * X) := by
    rw [hcomp, ← RingHom.map_det]
    rfl
  intro i
  have hi := hG i
  rw [hdet, Polynomial.comp_C_mul_X_coeff] at hi
  have hpi : ((p : ℚ) ^ (h * i)) ∈ LocRing p := by
    exact_mod_cast int_mem_locRing (ℓ := p) ((p : ℤ) ^ (h * i))
  have hm := (LocRing p).mul_mem hi hpi
  convert hm using 1
  have hph : ((p : ℚ) ^ h) ^ i ≠ 0 := pow_ne_zero _ (pow_ne_zero h hp0)
  rw [inv_pow, pow_mul]
  field_simp <;> (rw [Nat.mul_comm (Fintype.card ι + Fintype.card κw) h] <;> ring)

end CatalanCore.Uniform.Content.Sweep

#print axioms CatalanCore.Uniform.Content.Sweep.gle_member
#print axioms CatalanCore.Uniform.Content.Sweep.descent

#print axioms CatalanCore.Uniform.Content.Sweep.gle_member_h
