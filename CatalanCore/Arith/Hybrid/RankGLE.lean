module

public import CatalanCore.Linalg.RankDvd
public import CatalanCore.Arith.Hybrid.Tropical
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.ZMod.Basic
public import CatalanCore.Frame.Spec

@[expose] public section

/-!
# The rank principle for the Gauss valuation (`GLE`)

`RankDvd.lean` applied to `R = ℤ_(p)[X]`, `ϖ = p`, `K = 𝔽_p(X)`.  Statement (`gle_det_of_rank`):
let `M` be a square matrix over `ℚ[X]` and `u, v` natural weights such that
`B_ij = p^{u_i + v_j} M_ij` has all coefficients in `ℤ_(p)`; if the reduction of `B` mod `p`
(an integral matrix over `𝔽_p[X] ⊂ 𝔽_p(X)`) has rank `≤ n - k`, then `p^{∑u + ∑v - k} det M` is
`ℤ_(p)`-integral, i.e. `GLE p (∑u + ∑v - k) (det M)`.
-/

open Polynomial CatalanCore.Basic CatalanCore.Linalg

namespace CatalanCore.Arith.Hybrid

section Red

variable (p : ℕ) [hp : Fact p.Prime]

lemma den_cast_ne_zero {x : ℚ} (hx : x ∈ LocRing p) : ((x.den : ℕ) : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]; exact hx

/-- Reduction `ℤ_(p) → 𝔽_p`. -/
noncomputable def redQ : LocRing p →+* ZMod p where
  toFun x := ((x : ℚ) : ZMod p)
  map_one' := by simp
  map_zero' := by simp
  map_add' a b := Rat.cast_add_of_ne_zero (den_cast_ne_zero p a.2) (den_cast_ne_zero p b.2)
  map_mul' a b := Rat.cast_mul_of_ne_zero (den_cast_ne_zero p a.2) (den_cast_ne_zero p b.2)

lemma redQ_apply (x : LocRing p) : redQ p x = ((x : ℚ) : ZMod p) := rfl

/-- The kernel of the reduction is `(p)`. -/
lemma redQ_eq_zero_iff (x : LocRing p) : redQ p x = 0 ↔ ((p : ℕ) : LocRing p) ∣ x := by
  constructor
  · intro h
    rw [redQ_apply, Rat.cast_def] at h
    have hd := den_cast_ne_zero p x.2
    have hn : ((x : ℚ).num : ZMod p) = 0 := by
      rcases div_eq_zero_iff.mp h with h | h
      · exact h
      · exact absurd h hd
    have hpn : (p : ℤ) ∣ (x : ℚ).num := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hn
    obtain ⟨t, ht⟩ := hpn
    have hy : ((t : ℚ) / ((x : ℚ).den : ℚ)) ∈ LocRing p := by
      rw [mem_locRing]
      have e : ((t : ℚ) / ((x : ℚ).den : ℚ)) = Rat.divInt t ((x : ℚ).den : ℤ) := by
        rw [Rat.divInt_eq_div]; push_cast; rfl
      rw [e]
      intro hdv
      have h1 := Rat.den_dvd t ((x : ℚ).den : ℤ)
      have h2 : (p : ℤ) ∣ ((x : ℚ).den : ℤ) :=
        (Int.natCast_dvd_natCast.2 hdv).trans h1
      exact x.2 (Int.natCast_dvd_natCast.1 h2)
    refine ⟨⟨_, hy⟩, ?_⟩
    apply Subtype.ext
    have hden : ((x : ℚ).den : ℚ) ≠ 0 := by exact_mod_cast (x : ℚ).den_nz
    have hnum : (x : ℚ) = ((x : ℚ).num : ℚ) / ((x : ℚ).den : ℚ) := (Rat.num_div_den _).symm
    have hnum' : ((x : ℚ).num : ℚ) = (p : ℚ) * t := by exact_mod_cast ht
    simp only [Subring.coe_mul, Subring.coe_natCast]
    calc (x : ℚ) = ((x : ℚ).num : ℚ) / ((x : ℚ).den : ℚ) := hnum
      _ = _ := by rw [hnum']; ring
  · rintro ⟨y, rfl⟩
    rw [map_mul]
    have : redQ p ((p : ℕ) : LocRing p) = 0 := by
      rw [redQ_apply]; simp
    rw [this, zero_mul]

lemma prime_p : Prime ((p : ℕ) : LocRing p) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have := congrArg (fun z : LocRing p => (z : ℚ)) h
    simp at this
    exact hp.out.ne_zero this
  · intro hu
    have := hu.map (redQ p)
    have h0 : redQ p ((p : ℕ) : LocRing p) = 0 := (redQ_eq_zero_iff p _).2 dvd_rfl
    rw [h0] at this
    exact not_isUnit_zero this
  · intro a b hab
    have : redQ p a * redQ p b = 0 := by
      rw [← map_mul]; exact (redQ_eq_zero_iff p _).2 hab
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl ((redQ_eq_zero_iff p _).1 h)
    · exact Or.inr ((redQ_eq_zero_iff p _).1 h)

/-- Reduction of integral polynomials into `𝔽_p(X)`. -/
noncomputable def phiP : (LocRing p)[X] →+* RatFunc (ZMod p) :=
  (algebraMap (ZMod p)[X] (RatFunc (ZMod p))).comp (Polynomial.mapRingHom (redQ p))

lemma phiP_eq_zero_iff (g : (LocRing p)[X]) :
    phiP p g = 0 ↔ C ((p : ℕ) : LocRing p) ∣ g := by
  rw [C_dvd_iff_dvd_coeff]
  unfold phiP
  simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom]
  rw [map_eq_zero_iff _ (RatFunc.algebraMap_injective (ZMod p)), Polynomial.ext_iff]
  simp only [coeff_map, coeff_zero, redQ_eq_zero_iff]

end Red
section Bridge

variable (p : ℕ) [hp : Fact p.Prime]

/-- Integral polynomials as polynomials over `ℚ`. -/
noncomputable def toQ : (LocRing p)[X] →+* ℚ[X] := Polynomial.mapRingHom (LocRing p).subtype

lemma toQ_coeff (g : (LocRing p)[X]) (i : ℕ) : (toQ p g).coeff i = ((g.coeff i : LocRing p) : ℚ) := by
  simp [toQ, coeff_map]

lemma toQ_C_natCast (k : ℕ) : toQ p (C ((p : ℕ) : LocRing p) ^ k) = C (p : ℚ) ^ k := by
  simp [toQ]

/-- **Rank principle for `GLE`.** -/
theorem gle_det_of_rank {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℚ[X])
    (Bl : Matrix ι ι (LocRing p)[X]) (u v : ι → ℕ)
    (hB : ∀ i j, toQ p (Bl i j) = C ((p : ℚ) ^ (u i + v j)) * M i j) (k : ℕ)
    (hrk : (Bl.map (phiP p)).rank + k ≤ Fintype.card ι) :
    GLE p (∑ i, u i + ∑ j, v j - k) M.det := by
  classical
  set e := Fintype.equivFin ι
  set Bf := Bl.submatrix e.symm e.symm with hBf
  have hrank : (Bf.map (phiP p)).rank = (Bl.map (phiP p)).rank := by
    have : Bf.map (phiP p) = (Bl.map (phiP p)).submatrix e.symm e.symm := rfl
    rw [this, Matrix.rank_submatrix]
  have hprime : Prime (C ((p : ℕ) : LocRing p) : (LocRing p)[X]) :=
    Polynomial.prime_C_iff.2 (prime_p p)
  have hdvd : C ((p : ℕ) : LocRing p) ^ k ∣ Bl.det := by
    have := dvd_det_of_rank (phiP p) hprime (phiP_eq_zero_iff p) (Fintype.card ι) k Bf
      (by rw [hrank]; exact hrk)
    rwa [hBf, Matrix.det_submatrix_equiv_self] at this
  obtain ⟨g, hg⟩ := hdvd
  have hmat : (toQ p).mapMatrix Bl = Matrix.diagonal (fun i => C ((p : ℚ) ^ u i)) * M *
      Matrix.diagonal (fun j => C ((p : ℚ) ^ v j)) := by
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [hB i j, pow_add, C_mul]; ring_nf
  have h1 : ∀ w : ι → ℕ, ∏ i, C ((p : ℚ) ^ w i) = C ((p : ℚ) ^ (∑ i, w i)) := by
    intro w; rw [← Finset.prod_pow_eq_pow_sum, map_prod]
  have hdetQ : toQ p Bl.det = C ((p : ℚ) ^ (∑ i, u i + ∑ j, v j)) * M.det := by
    rw [RingHom.map_det, hmat, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal,
      Matrix.det_diagonal, h1, h1, pow_add, C_mul]; ring
  rw [hg, map_mul, toQ_C_natCast, C_pow] at hdetQ
  have hp0 : C (p : ℚ) ≠ 0 := by
    rw [Ne, C_eq_zero]; exact_mod_cast hp.out.ne_zero
  have hpow : ∀ d : ℕ, (p : ℚ) ^ d ∈ LocRing p := fun d => by
    simpa using int_mem_locRing (ℓ := p) ((p : ℤ) ^ d)
  generalize hS : ∑ i, u i + ∑ j, v j = S at hdetQ ⊢
  intro i
  have hgi : (toQ p g).coeff i ∈ LocRing p := by rw [toQ_coeff]; exact (g.coeff i).2
  by_cases hk : k ≤ S
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hk
    have hSk : S - k = d := by omega
    rw [hd, pow_add] at hdetQ
    have e : toQ p g = C ((p : ℚ) ^ d) * M.det := by
      apply mul_left_cancel₀ (pow_ne_zero k hp0)
      rw [hdetQ, C_pow]; ring
    rw [hSk]
    have := hgi; rw [e, coeff_C_mul] at this
    exact this
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (show S ≤ k by omega)
    have hSk : S - k = 0 := by omega
    rw [hd, pow_add] at hdetQ
    have e : M.det = C ((p : ℚ) ^ d) * toQ p g := by
      apply mul_left_cancel₀ (pow_ne_zero S hp0)
      rw [← hdetQ, C_pow]; ring
    rw [hSk, pow_zero, one_mul, e, coeff_C_mul]
    exact (LocRing p).mul_mem (hpow d) hgi

/-- A `GLE` polynomial, scaled, lifts to an integral polynomial. -/
lemma exists_lift {c : ℕ} {f : ℚ[X]} (hf : GLE p c f) :
    ∃ g : (LocRing p)[X], toQ p g = C ((p : ℚ) ^ c) * f := by
  have : C ((p : ℚ) ^ c) * f ∈ Polynomial.lifts (LocRing p).subtype := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [coeff_C_mul]
    exact ⟨⟨_, hf n⟩, rfl⟩
  obtain ⟨g, hg⟩ := Polynomial.mem_lifts _ |>.1 this
  exact ⟨g, hg⟩

/-- The entry polynomials of `Full(X)` (`Frame.fullPoly` is the determinant of this matrix). -/
noncomputable def fullEntry (Fr : Frame) (r m : ℕ) (a b : Fin r ⊕ Fin m) : ℚ[X] :=
  (match a, b with
      | Sum.inl c, Sum.inl c' => if c = c' then (X : ℚ[X]) else 0
      | _, _ => 0) + C (Fr.Mn (Frame.hybRow r m a) (Frame.hybCol r m b))

lemma fullPoly_eq_det (Fr : Frame) (r m : ℕ) :
    Fr.fullPoly r m = (Matrix.of (fullEntry Fr r m)).det := rfl

/-- **Rank principle for `Full(X)`.**  If `u, v` are integral weights such that the scaled entries
`p^{u_a + v_b} Full_ab` are integral with reduction `Bbar_ab ∈ 𝔽_p(X)`, and `Bbar` has rank
`≤ r + m - k`, then `GLE p (∑u + ∑v - k) (fullPoly)`. -/
theorem gle_full_of_rank (Fr : Frame) (r m : ℕ) (u v : Fin r ⊕ Fin m → ℕ)
    (Bbar : Matrix (Fin r ⊕ Fin m) (Fin r ⊕ Fin m) (RatFunc (ZMod p)))
    (hB : ∀ a b, ∃ g : (LocRing p)[X], toQ p g = C ((p : ℚ) ^ (u a + v b)) * fullEntry Fr r m a b ∧
      phiP p g = Bbar a b) (k : ℕ) (hrk : Bbar.rank + k ≤ r + m) :
    GLE p (∑ a, u a + ∑ b, v b - k) (Fr.fullPoly r m) := by
  choose g hg1 hg2 using hB
  have hmap : (Matrix.of g).map (phiP p) = Bbar := by ext a b; simp [hg2]
  rw [fullPoly_eq_det]
  refine gle_det_of_rank p (Matrix.of (fullEntry Fr r m)) (Matrix.of g) u v
    (fun a b => hg1 a b) k ?_
  rw [hmap]; simpa using hrk

end Bridge

end CatalanCore.Arith.Hybrid
