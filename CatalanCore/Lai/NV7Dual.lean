module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs

@[expose] public section

/-! # `CatalanCore.Lai.NV7Dual`: Hankel duality, Wilson reflection, power sums over `F_l`, block determinants (ledger LN06, steps 4-5). -/

section
/-!
# Hankel duality by complementary subsets (generic) and the power sums over `𝔽_ℓ`

`det_ne_zero_of_dual`: if the weighted Hankel matrix of `ω` on `N = m + k` nodes is replaced by the
Hankel matrix of the dual weights `1 / (ω_s Π'(x_s)²)` of size `k`, nonvanishing of the dual
implies nonvanishing of the original (content/NV note §B).  No Cauchy–Binet: the block
`[V | ω⁻¹ U]` is shown to be invertible directly.
-/

open Matrix Finset Polynomial

namespace CatalanCore.Lai.NV7

section Dual

variable {F : Type*} [Field F]

theorem det_ne_zero_of_dual {m k : ℕ}
    (V : Matrix (Fin m ⊕ Fin k) (Fin m) F) (U : Matrix (Fin m ⊕ Fin k) (Fin k) F)
    (ω : Fin m ⊕ Fin k → F) (hω : ∀ s, ω s ≠ 0)
    (hUV : Uᵀ * V = 0) (hV : ∀ c, V *ᵥ c = 0 → c = 0)
    (hG : (Uᵀ * diagonal (fun s => (ω s)⁻¹) * U).det ≠ 0) :
    (Vᵀ * diagonal ω * V).det ≠ 0 := by
  classical
  have hDD : diagonal ω * diagonal (fun s => (ω s)⁻¹) = (1 : Matrix (Fin m ⊕ Fin k) (Fin m ⊕ Fin k) F) := by
    rw [diagonal_mul_diagonal]
    have : (fun s => ω s * (ω s)⁻¹) = fun _ => (1 : F) := funext fun s => mul_inv_cancel₀ (hω s)
    rw [this]; exact diagonal_one
  have hDD' : diagonal (fun s => (ω s)⁻¹) * diagonal ω = (1 : Matrix (Fin m ⊕ Fin k) (Fin m ⊕ Fin k) F) := by
    rw [diagonal_mul_diagonal]
    have : (fun s => (ω s)⁻¹ * ω s) = fun _ => (1 : F) := funext fun s => inv_mul_cancel₀ (hω s)
    rw [this]; exact diagonal_one
  set M : Matrix (Fin m ⊕ Fin k) (Fin m ⊕ Fin k) F :=
    fromCols V (diagonal (fun s => (ω s)⁻¹) * U) with hM
  have hMdet : M.det ≠ 0 := by
    intro h0
    obtain ⟨z, hz, hMz⟩ := exists_mulVec_eq_zero_iff.2 h0
    have hz' : z = Sum.elim (z ∘ Sum.inl) (z ∘ Sum.inr) := by
      ext (i | i) <;> rfl
    rw [hz', hM, fromCols_mulVec_sumElim] at hMz
    have h1 : (Uᵀ * V) *ᵥ (z ∘ Sum.inl) + (Uᵀ * diagonal (fun s => (ω s)⁻¹) * U) *ᵥ (z ∘ Sum.inr) = 0 := by
      have := congrArg (fun v => Uᵀ *ᵥ v) hMz
      simp only [mulVec_add, mulVec_mulVec, mulVec_zero, ← Matrix.mul_assoc] at this
      simpa [Matrix.mul_assoc] using this
    rw [hUV, zero_mulVec, zero_add] at h1
    have hd : z ∘ Sum.inr = 0 := eq_zero_of_mulVec_eq_zero hG h1
    rw [hd, mulVec_zero, add_zero] at hMz
    have hc : z ∘ Sum.inl = 0 := hV _ hMz
    apply hz
    rw [hz', hc, hd]
    ext (i | i) <;> rfl
  have hprod : Mᵀ * diagonal ω * M =
      fromBlocks (Vᵀ * diagonal ω * V) 0 0 (Uᵀ * diagonal (fun s => (ω s)⁻¹) * U) := by
    have e1 : diagonal ω * M = fromCols (diagonal ω * V) U := by
      rw [hM, mul_fromCols, ← Matrix.mul_assoc, hDD, Matrix.one_mul]
    have e2 : Mᵀ = fromRows Vᵀ (Uᵀ * diagonal (fun s => (ω s)⁻¹)) := by
      rw [hM, transpose_fromCols, Matrix.transpose_mul, diagonal_transpose]
    rw [Matrix.mul_assoc, e1, e2, fromRows_mul_fromCols]
    have hVU : Vᵀ * U = 0 := by
      have := congrArg Matrix.transpose hUV
      simpa [Matrix.transpose_mul] using this
    have hUV' : Uᵀ * diagonal (fun s => (ω s)⁻¹) * (diagonal ω * V) = 0 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal (fun s => (ω s)⁻¹)), hDD', Matrix.one_mul, hUV]
    rw [hVU, hUV', ← Matrix.mul_assoc]
  have hdet := congrArg Matrix.det hprod
  rw [det_mul, det_mul, det_transpose, det_fromBlocks_zero₂₁, det_diagonal] at hdet
  have hωprod : ∏ s, ω s ≠ 0 := Finset.prod_ne_zero_iff.2 fun s _ => hω s
  intro hH
  rw [hH, zero_mul] at hdet
  have : M.det * (∏ s, ω s) * M.det = 0 := hdet
  exact mul_ne_zero (mul_ne_zero hMdet hωprod) hMdet this

end Dual

end CatalanCore.Lai.NV7

end

section
open Matrix Finset Polynomial

namespace CatalanCore.Lai.NV7

section Inst

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `Π'(x_s) = ∏_{t ≠ s} (x_s - x_t)`. -/
def nw (x : ι → F) (s : ι) : F := ∏ t ∈ univ.erase s, (x s - x t)

theorem nw_ne_zero {x : ι → F} (hx : Function.Injective x) (s : ι) : nw x s ≠ 0 := by
  unfold nw
  refine prod_ne_zero_iff.2 fun t ht => sub_ne_zero.2 fun h => ?_
  exact (ne_of_mem_erase ht) (hx h).symm

theorem sum_pow_div_nw {x : ι → F} (hx : Function.Injective x) {d : ℕ}
    (hd : d + 1 < Fintype.card ι) : ∑ s, x s ^ d / nw x s = 0 := by
  have h := Lagrange.coeff_eq_sum (s := (univ : Finset ι)) (v := x) hx.injOn
    (P := (X : F[X]) ^ d) (by rw [degree_X_pow, card_univ]; exact_mod_cast (by omega))
  rw [card_univ, coeff_X_pow, if_neg (by omega)] at h
  simpa [nw] using h.symm

/-- **Hankel duality (nonvanishing form).**  With `N = m + k` distinct nodes `x_s` and nonzero
weights `ω_s`, the `m × m` Hankel matrix of `ω` is nonsingular as soon as the `k × k` Hankel matrix of
the dual weights `1 / (ω_s Π'(x_s)²)` is. -/
theorem hankel_ne_zero_of_dual {x : ι → F} (hx : Function.Injective x) (ω : ι → F)
    (hω : ∀ s, ω s ≠ 0) {m k : ℕ} (hmk : m + k = Fintype.card ι)
    (hk : (Matrix.of fun i j : Fin k => ∑ s, x s ^ ((i : ℕ) + j) / (ω s * nw x s ^ 2)).det ≠ 0) :
    (Matrix.of fun i j : Fin m => ∑ s, ω s * x s ^ ((i : ℕ) + j)).det ≠ 0 := by
  classical
  have hcard : Fintype.card (Fin m ⊕ Fin k) = Fintype.card ι := by simp [hmk]
  let e : Fin m ⊕ Fin k ≃ ι := Fintype.equivOfCardEq hcard
  let V : Matrix (Fin m ⊕ Fin k) (Fin m) F := Matrix.of fun a i => x (e a) ^ (i : ℕ)
  let U : Matrix (Fin m ⊕ Fin k) (Fin k) F := Matrix.of fun a j => x (e a) ^ (j : ℕ) / nw x (e a)
  have hH : Vᵀ * diagonal (fun a => ω (e a)) * V =
      Matrix.of fun i j : Fin m => ∑ s, ω s * x s ^ ((i : ℕ) + j) := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [V, Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.of_apply]
    rw [← Equiv.sum_comp e (fun s => ω s * x s ^ ((i : ℕ) + j))]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [pow_add]; ring
  have hG : Uᵀ * diagonal (fun a => (ω (e a))⁻¹) * U =
      Matrix.of fun i j : Fin k => ∑ s, x s ^ ((i : ℕ) + j) / (ω s * nw x s ^ 2) := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [U, Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.of_apply]
    rw [← Equiv.sum_comp e (fun s => x s ^ ((i : ℕ) + j) / (ω s * nw x s ^ 2))]
    refine Finset.sum_congr rfl fun a _ => ?_
    have h1 := hω (e a)
    have h2 := nw_ne_zero hx (e a)
    rw [pow_add]; field_simp
  have hUV : Uᵀ * V = 0 := by
    ext j i
    simp only [U, V, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.zero_apply]
    have := sum_pow_div_nw hx (d := (i : ℕ) + j) (by have := i.2; have := j.2; omega)
    rw [← Equiv.sum_comp e (fun s => x s ^ ((i : ℕ) + j) / nw x s)] at this
    rw [← this]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [pow_add]; ring
  have hV : ∀ c, V *ᵥ c = 0 → c = 0 := by
    intro c hc
    set f : F[X] := ∑ i : Fin m, C (c i) * X ^ (i : ℕ) with hf
    have hev : ∀ s : ι, f.eval (x s) = 0 := by
      intro s
      have h1 := congrFun hc (e.symm s)
      rw [Matrix.mulVec, dotProduct, Pi.zero_apply] at h1
      have h2 : f.eval (x s) = ∑ i : Fin m, c i * x s ^ (i : ℕ) := by
        rw [hf, eval_finset_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [eval_mul, eval_C, eval_pow, eval_X]
      rw [h2, ← h1]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [V, Matrix.of_apply, Equiv.apply_symm_apply]
      ring
    have hf0 : f = 0 := Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero (univ : Finset ι) (v := x) hx.injOn
      (lt_of_lt_of_le (degree_sum_fin_lt c) (by rw [card_univ, ← hmk]; exact_mod_cast Nat.le_add_right m k))
      (fun s _ => hev s)
    ext i
    have := congrArg (fun p : F[X] => p.coeff (i : ℕ)) hf0
    simp only [hf, finset_sum_coeff, coeff_C_mul_X_pow, coeff_zero] at this
    simpa [Fin.val_inj] using this
  have := det_ne_zero_of_dual V U (fun a => ω (e a)) (fun a => hω _) hUV hV (by rw [hG]; exact hk)
  rwa [hH] at this

end Inst

end CatalanCore.Lai.NV7

end

section
open Matrix Finset Polynomial

namespace CatalanCore.Lai.NV7

section ZModPart

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

theorem prod_X_sub_C_zmod : ∏ y : ZMod ℓ, (X - C y) = (X ^ ℓ - X : (ZMod ℓ)[X]) := by
  have hq : Fintype.card (ZMod ℓ) = ℓ := ZMod.card ℓ
  have hroots := FiniteField.roots_X_pow_card_sub_X (ZMod ℓ)
  rw [hq] at hroots
  have hmon : (X ^ ℓ - X : (ZMod ℓ)[X]).Monic :=
    monic_X_pow_sub (by rw [degree_X]; exact_mod_cast hℓ.out.one_lt)
  have hdeg : (X ^ ℓ - X : (ZMod ℓ)[X]).natDegree = ℓ :=
    FiniteField.X_pow_card_sub_X_natDegree_eq (ZMod ℓ) hℓ.out.one_lt
  have := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon
    (by rw [hroots, hdeg]; simp [ZMod.card])
  rw [hroots] at this
  exact this

/-- `∏_{t ≠ z} (z - t) = -1` over `𝔽_ℓ` (the derivative of `X^ℓ - X`). -/
theorem prod_erase_sub_zmod (z : ZMod ℓ) : ∏ t ∈ (univ : Finset (ZMod ℓ)).erase z, (z - t) = -1 := by
  have h := Lagrange.eval_nodal_derivative_eval_node_eq (s := (univ : Finset (ZMod ℓ)))
    (v := fun y : ZMod ℓ => y) (i := z) (mem_univ z)
  rw [Lagrange.nodal_eq, prod_X_sub_C_zmod, Lagrange.eval_nodal] at h
  simp only [derivative_sub, derivative_X_pow, derivative_X, eval_sub, eval_mul, eval_pow, eval_X,
    eval_C, eval_one, eval_natCast, ZMod.natCast_self, zero_mul, zero_sub] at h
  rw [← h]

/-- Power sums over `𝔽_ℓ`: `∑_z P(z) = -[X^{ℓ-1}] P` for `deg P ≤ ℓ - 1`. -/
theorem sum_eval_zmod (P : (ZMod ℓ)[X]) (hP : P.natDegree ≤ ℓ - 1) :
    ∑ z : ZMod ℓ, P.eval z = - P.coeff (ℓ - 1) := by
  have h2 := hℓ.out.two_le
  have hlt : P.natDegree < ℓ := by omega
  have hz : ∀ i, i < ℓ - 1 → ∑ z : ZMod ℓ, z ^ i = 0 := fun i hi =>
    FiniteField.sum_pow_lt_card_sub_one (ZMod ℓ) i (by rwa [ZMod.card])
  have htop : ∑ z : ZMod ℓ, z ^ (ℓ - 1) = -1 := by
    have e1 : ∀ z : ZMod ℓ, z ^ (ℓ - 1) = if z ≠ 0 then 1 else 0 := by
      intro z
      by_cases h : z = 0
      · simp [h, show ℓ - 1 ≠ 0 by omega]
      · simp [h, ZMod.pow_card_sub_one_eq_one h]
    simp_rw [e1]
    rw [Finset.sum_boole, Finset.filter_ne' , Finset.card_erase_of_mem (mem_univ _), Finset.card_univ,
      ZMod.card, Nat.cast_sub (by omega), ZMod.natCast_self]
    simp
  simp_rw [eval_eq_sum_range' hlt]
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single (ℓ - 1)]
  · rw [← Finset.mul_sum, htop]; ring
  · intro i hi hne
    have : i < ℓ - 1 := by have := Finset.mem_range.1 hi; omega
    rw [← Finset.mul_sum, hz i this, mul_zero]
  · intro hn
    exfalso; apply hn; rw [Finset.mem_range]; omega

end ZModPart

end CatalanCore.Lai.NV7

end

section
open Matrix Finset Polynomial

namespace CatalanCore.Lai.NV7

section Top

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

theorem cast_inj_lt {s t : ℕ} (hs : s < ℓ) (ht : t < ℓ) (h : (s : ZMod ℓ) = t) : s = t := by
  have := (ZMod.natCast_eq_natCast_iff' s t ℓ).1 h
  rwa [Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt ht] at this

/-- The low block `{0, …, A}` and the top block `{A + 1, …, ℓ - 1}` of residues. -/
def lowS (ℓ A : ℕ) : Finset (ZMod ℓ) := (range (A + 1)).image (fun s : ℕ => (s : ZMod ℓ))

def topS (ℓ A : ℕ) : Finset (ZMod ℓ) := (Ico (A + 1) ℓ).image (fun s : ℕ => (s : ZMod ℓ))

theorem topS_card (A : ℕ) : (topS ℓ A).card = ℓ - (A + 1) := by
  rw [topS, card_image_of_injOn, Nat.card_Ico]
  intro s hs t ht h
  exact cast_inj_lt (mem_Ico.1 hs).2 (mem_Ico.1 ht).2 h

theorem disjoint_low_top (A : ℕ) (hA : A + 1 ≤ ℓ) : Disjoint (lowS ℓ A) (topS ℓ A) := by
  rw [Finset.disjoint_left]
  intro z hz hz'
  obtain ⟨s, hs, rfl⟩ := mem_image.1 hz
  obtain ⟨t, ht, hst⟩ := mem_image.1 hz'
  have h1 := mem_range.1 hs
  have h2 := mem_Ico.1 ht
  have := cast_inj_lt (by omega) (by omega) hst
  omega

theorem low_or_top (A : ℕ) (hA : A + 1 ≤ ℓ) (z : ZMod ℓ) : z ∈ lowS ℓ A ∨ z ∈ topS ℓ A := by
  haveI : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  have hz := ZMod.val_lt z
  by_cases h : z.val < A + 1
  · left; exact mem_image.2 ⟨z.val, mem_range.2 h, ZMod.natCast_zmod_val z⟩
  · right; exact mem_image.2 ⟨z.val, mem_Ico.2 ⟨by omega, hz⟩, ZMod.natCast_zmod_val z⟩

def Dlow (ℓ A : ℕ) (z : ZMod ℓ) : ZMod ℓ := ∏ i ∈ range (A + 1), (z - (i : ZMod ℓ))

def Dal (ℓ α : ℕ) (z : ZMod ℓ) : ZMod ℓ := ∏ i ∈ range α, (z - (i : ZMod ℓ))

def Ehi (ℓ α A : ℕ) (z : ZMod ℓ) : ZMod ℓ := ∏ i ∈ Ico α (A + 1), (z - (i : ZMod ℓ))

theorem prod_low (A : ℕ) (hA : A + 1 ≤ ℓ) (z : ZMod ℓ) :
    ∏ c ∈ lowS ℓ A, (z - c) = Dlow ℓ A z := by
  rw [lowS, prod_image]
  · rfl
  · intro s hs t ht h
    exact cast_inj_lt (by have := mem_range.1 hs; omega) (by have := mem_range.1 ht; omega) h

theorem Dlow_eq {α A : ℕ} (hα : α ≤ A + 1) (z : ZMod ℓ) :
    Dlow ℓ A z = Dal ℓ α z * Ehi ℓ α A z := (prod_range_mul_prod_Ico _ hα).symm

theorem Dlow_zero_of_low {A : ℕ} {z : ZMod ℓ} (hz : z ∈ lowS ℓ A) : Dlow ℓ A z = 0 := by
  obtain ⟨s, hs, rfl⟩ := mem_image.1 hz
  exact prod_eq_zero hs (sub_self _)

theorem Dlow_ne_zero_of_top {A : ℕ} (hA : A + 1 ≤ ℓ) {s : ZMod ℓ} (hs : s ∈ topS ℓ A) :
    Dlow ℓ A s ≠ 0 := by
  rw [← prod_low A hA]
  refine prod_ne_zero_iff.2 fun c hc => sub_ne_zero.2 fun h => ?_
  exact (disjoint_left.1 (disjoint_low_top A hA)) hc (h ▸ hs)

/-- Wilson reflection for the top block: `Π'_{top}(s) · ∏_{c ≤ A} (s - c) = -1`. -/
theorem prod_top_erase {A : ℕ} (hA : A + 1 ≤ ℓ) {s : ZMod ℓ} (hs : s ∈ topS ℓ A) :
    (∏ t ∈ (topS ℓ A).erase s, (s - t)) * Dlow ℓ A s = -1 := by
  have h1 := prod_erase_sub_zmod (ℓ := ℓ) s
  have hsub : (topS ℓ A).erase s ⊆ (univ : Finset (ZMod ℓ)).erase s :=
    erase_subset_erase _ (subset_univ _)
  have h2 := prod_sdiff (f := fun t => s - t) hsub
  have h3 : (univ.erase s) \ ((topS ℓ A).erase s) = lowS ℓ A := by
    have hd := disjoint_low_top A hA
    have hu := low_or_top (ℓ := ℓ) A hA
    ext z
    simp only [mem_sdiff, mem_erase, mem_univ, and_true]
    constructor
    · rintro ⟨hz, hn⟩
      rcases hu z with h | h
      · exact h
      · exact absurd ⟨hz, h⟩ hn
    · intro hz
      refine ⟨fun h => ?_, fun h => ?_⟩
      · subst h; exact disjoint_left.1 hd hz hs
      · exact disjoint_left.1 hd hz h.2
  rw [h3, prod_low A hA] at h2
  rw [mul_comm]
  rw [h2, h1]

theorem nw_subtype (S : Finset (ZMod ℓ)) (z : S) :
    nw (fun t : S => (t : ZMod ℓ)) z = ∏ t ∈ S.erase z.1, (z.1 - t) := by
  unfold nw
  have : S.erase z.1 = (univ.erase z).map (Function.Embedding.subtype (· ∈ S)) := by
    ext t
    simp only [mem_erase, mem_map, mem_univ, Function.Embedding.coe_subtype, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨t, h2⟩, ⟨fun h => h1 (by rw [← h]), trivial⟩, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨fun h => hu.1 (Subtype.ext h), u.2⟩
  rw [this, prod_map]
  rfl

end Top

end CatalanCore.Lai.NV7

end

section
open Matrix Finset Polynomial

namespace CatalanCore.Lai.NV7

section Final

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-- The dual weight polynomial `Φ = ∏_{c ≤ A}(X - c) · ∏_{α ≤ i ≤ A}(X - i)`. -/
noncomputable def PhiP (ℓ α A : ℕ) : (ZMod ℓ)[X] :=
  (∏ i ∈ range (A + 1), (X - C (i : ZMod ℓ))) * ∏ i ∈ Ico α (A + 1), (X - C (i : ZMod ℓ))

theorem PhiP_eval (α A : ℕ) (z : ZMod ℓ) :
    (PhiP ℓ α A).eval z = Dlow ℓ A z * Ehi ℓ α A z := by
  simp [PhiP, eval_prod, Dlow, Ehi]

theorem PhiP_monic (α A : ℕ) : (PhiP ℓ α A).Monic := by
  unfold PhiP
  exact (monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _).mul
    (monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _)

theorem PhiP_natDegree (α A : ℕ) (hα : α ≤ A + 1) :
    (PhiP ℓ α A).natDegree = (A + 1) + (A + 1 - α) := by
  unfold PhiP
  rw [Monic.natDegree_mul (monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _)
    (monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _),
    natDegree_finsetProd_X_sub_C_eq_card, natDegree_finsetProd_X_sub_C_eq_card, card_range,
    Nat.card_Ico]

theorem PhiP_nextCoeff (α A : ℕ) :
    (PhiP ℓ α A).nextCoeff = -(∑ i ∈ range (A + 1), (i : ZMod ℓ) + ∑ i ∈ Ico α (A + 1), (i : ZMod ℓ)) := by
  unfold PhiP
  rw [Monic.nextCoeff_mul (monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _)
    (monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _), prod_X_sub_C_nextCoeff,
    prod_X_sub_C_nextCoeff]
  ring

/-- `τ_e = ∑_{z ∈ 𝔽_ℓ} Φ(z) z^e`. -/
noncomputable def tau (ℓ : ℕ) [Fact ℓ.Prime] (α A e : ℕ) : ZMod ℓ := ∑ z : ZMod ℓ, (PhiP ℓ α A).eval z * z ^ e

theorem tau_zero_deg_l (α A : ℕ) (hα : α ≤ A + 1) (h3 : 3 ≤ ℓ) (hd : (A + 1) + (A + 1 - α) = ℓ) :
    tau ℓ α A 0 = ∑ i ∈ range (A + 1), (i : ZMod ℓ) + ∑ i ∈ Ico α (A + 1), (i : ZMod ℓ) := by
  have h5 := hℓ.out.two_le
  set Φ := PhiP ℓ α A with hΦ
  have hdeg : Φ.natDegree = ℓ := by rw [hΦ, PhiP_natDegree α A hα]; exact hd
  have hmon : Φ.Monic := PhiP_monic α A
  set P' : (ZMod ℓ)[X] := Φ - (X ^ ℓ - X) with hP'
  have hP'deg : P'.natDegree ≤ ℓ - 1 := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    simp only [hP', coeff_sub, coeff_X_pow, coeff_X]
    by_cases hNl : N = ℓ
    · rw [hNl]
      have : Φ.coeff ℓ = 1 := by have := hmon.coeff_natDegree; rwa [hdeg] at this
      have h1l : (1 : ℕ) ≠ ℓ := by omega
      simp [this, h1l]
    · have : Φ.coeff N = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
      rw [this]
      have : N ≠ 1 := by omega
      have h1N : (1 : ℕ) ≠ N := by omega
      simp [hNl, this, h1N]
  have hev : ∀ z : ZMod ℓ, P'.eval z = Φ.eval z := by
    intro z
    simp [hP', ZMod.pow_card]
  have hsum := sum_eval_zmod P' hP'deg
  have hc : P'.coeff (ℓ - 1) = Φ.coeff (ℓ - 1) := by
    simp only [hP', coeff_sub, coeff_X_pow, coeff_X]
    have : ℓ - 1 ≠ ℓ := by omega
    have h1 : ℓ - 1 ≠ 1 := by omega
    simp [this, h1, h1.symm]
  have hnc : Φ.coeff (ℓ - 1) = Φ.nextCoeff := by
    rw [nextCoeff, if_neg (by omega), hdeg]
  unfold tau
  simp only [pow_zero, mul_one]
  rw [← hΦ, Finset.sum_congr rfl (fun z _ => (hev z).symm), hsum, hc, hnc, hΦ, PhiP_nextCoeff]
  ring

theorem tau_k2 (α A : ℕ) (hα : α ≤ A + 1) (h3 : 3 ≤ ℓ) (hd : (A + 1) + (A + 1 - α) + 2 = ℓ) :
    tau ℓ α A 0 = 0 ∧ tau ℓ α A 1 = -1 := by
  set Φ := PhiP ℓ α A with hΦ
  have hdeg : Φ.natDegree = ℓ - 2 := by rw [hΦ, PhiP_natDegree α A hα]; omega
  have hmon : Φ.Monic := PhiP_monic α A
  constructor
  · unfold tau
    simp only [pow_zero, mul_one]
    rw [← hΦ, sum_eval_zmod Φ (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]
    simp
  · unfold tau
    have hz : ∀ z : ZMod ℓ, Φ.eval z * z ^ 1 = (Φ * X).eval z := by intro z; simp
    rw [← hΦ, Finset.sum_congr rfl (fun z _ => hz z),
      sum_eval_zmod (Φ * X) (by rw [natDegree_mul_X hmon.ne_zero]; omega)]
    have : ℓ - 1 = (ℓ - 2) + 1 := by omega
    rw [this, coeff_mul_X]
    have h1 : Φ.coeff (ℓ - 2) = 1 := by have := hmon.coeff_natDegree; rwa [hdeg] at this
    rw [h1]

/-- **The Hankel determinant of `D_α` on the top block** (content Lemma 2.4 + Wilson + Heine duality).
`m + k = ℓ - A - 1` points, `k ∈ {1, 2}`, `deg Φ ∈ {ℓ, ℓ - 2}`. -/
theorem top_hankel_ne_zero (A α m k : ℕ) (hA : A + 1 < ℓ) (hα : α ≤ A + 1) (h3 : 3 ≤ ℓ)
    (hmk : m + k = ℓ - (A + 1))
    (hk : (k = 1 ∧ (A + 1) + (A + 1 - α) = ℓ ∧
          (∑ i ∈ range (A + 1), (i : ZMod ℓ) + ∑ i ∈ Ico α (A + 1), (i : ZMod ℓ)) ≠ 0) ∨
          (k = 2 ∧ (A + 1) + (A + 1 - α) + 2 = ℓ)) :
    (Matrix.of fun i j : Fin m => ∑ s ∈ topS ℓ A, Dal ℓ α s * s ^ ((i : ℕ) + j)).det ≠ 0 := by
  classical
  set S := topS ℓ A with hS
  let x : S → ZMod ℓ := fun t => (t : ZMod ℓ)
  have hx : Function.Injective x := Subtype.val_injective
  let ω : S → ZMod ℓ := fun t => Dal ℓ α t
  have hDlow : ∀ t : S, Dlow ℓ A t ≠ 0 := fun t => Dlow_ne_zero_of_top hA.le t.2
  have hω : ∀ t : S, ω t ≠ 0 := by
    intro t
    have := hDlow t
    rw [Dlow_eq hα] at this
    exact left_ne_zero_of_mul this
  have hEhi : ∀ t : S, Ehi ℓ α A t ≠ 0 := by
    intro t
    have := hDlow t
    rw [Dlow_eq hα] at this
    exact right_ne_zero_of_mul this
  have hcard : m + k = Fintype.card S := by rw [Fintype.card_coe, hS, topS_card]; exact hmk
  -- dual weights
  have hw : ∀ (t : S) (e : ℕ), x t ^ e / (ω t * nw x t ^ 2) = (PhiP ℓ α A).eval (t : ZMod ℓ) * (t : ZMod ℓ) ^ e := by
    intro t e
    have hP := prod_top_erase hA.le t.2
    have hnw : nw x t = ∏ u ∈ S.erase t.1, (t.1 - u) := nw_subtype S t
    have hD := hDlow t
    have hω' := hω t
    have hE := hEhi t
    have hnw' : nw x t = -(Dlow ℓ A t)⁻¹ := by
      rw [hnw]; field_simp at hP ⊢; linear_combination hP
    rw [hnw', PhiP_eval, Dlow_eq hα]
    simp only [x, ω]
    field_simp
  have hτ : ∀ e : ℕ, ∑ t : S, x t ^ e / (ω t * nw x t ^ 2) = tau ℓ α A e := by
    intro e
    simp_rw [hw]
    rw [Finset.sum_coe_sort S (fun s => (PhiP ℓ α A).eval s * s ^ e)]
    unfold tau
    refine Finset.sum_subset (subset_univ _) fun z _ hz => ?_
    have hzl : z ∈ lowS ℓ A := (low_or_top A hA.le z).resolve_right hz
    rw [PhiP_eval, Dlow_zero_of_low hzl]; simp
  have hdual : (Matrix.of fun i j : Fin k => ∑ t : S, x t ^ ((i : ℕ) + j) / (ω t * nw x t ^ 2)).det ≠ 0 := by
    simp_rw [hτ]
    rcases hk with ⟨hk1, hd1, he1⟩ | ⟨hk2, hd2⟩
    · subst hk1
      rw [Matrix.det_unique]
      simp only [Matrix.of_apply, Fin.default_eq_zero, Fin.val_zero, add_zero]
      rw [tau_zero_deg_l α A hα h3 hd1]
      exact he1
    · subst hk2
      rw [Matrix.det_fin_two]
      simp only [Matrix.of_apply, Fin.val_zero, Fin.val_one, add_zero, zero_add]
      obtain ⟨h0, h1⟩ := tau_k2 α A hα h3 hd2
      rw [h0, h1]
      simp
  have hmain := hankel_ne_zero_of_dual hx ω hω hcard hdual
  have : (Matrix.of fun i j : Fin m => ∑ s : S, ω s * x s ^ ((i : ℕ) + j)) =
      Matrix.of fun i j : Fin m => ∑ s ∈ S, Dal ℓ α s * s ^ ((i : ℕ) + j) := by
    ext i j
    simp only [Matrix.of_apply]
    exact Finset.sum_coe_sort S (fun s => Dal ℓ α s * s ^ ((i : ℕ) + j))
  rwa [this] at hmain

end Final

end CatalanCore.Lai.NV7

end

section
/-!
# The two block determinants of the `E′` reduction (pure algebra over a field)

* `det_AA_ne_zero`: a block diagonal matrix with blocks `B_r · H` (`3 × 3`) is nonsingular;
* `det_BB_ne_zero`: `[[D, C], [Cᵀ, E]]` with `D` diagonal is nonsingular as soon as the Schur complement is;
* `det_signed_hankel`: the sign twist `(-1)^{i+j}` does not change a determinant;
* `sum_Ico_top`: content Lemma 2.4, `∑_{T2} + ∑_{T4} = 0` for `D_α(s) (-s)^e`.
-/

open Matrix Finset Polynomial

namespace CatalanCore.Lai.NV7

section AlgField

variable {F : Type*} [Field F]

theorem det_AA_ne_zero {α : ℕ} (B : Fin α → F) (hB : ∀ r, B r ≠ 0) (H : Matrix (Fin 3) (Fin 3) F)
    (hH : H.det ≠ 0) :
    (Matrix.of fun (x y : Fin α × Fin 3) => if x.1 = y.1 then B x.1 * H x.2 y.2 else 0).det ≠ 0 := by
  classical
  have hmat : (Matrix.of fun (x y : Fin α × Fin 3) => if x.1 = y.1 then B x.1 * H x.2 y.2 else 0) =
      (blockDiagonal (fun r : Fin α => B r • H)).submatrix (Equiv.prodComm (Fin α) (Fin 3))
        (Equiv.prodComm (Fin α) (Fin 3)) := by
    ext ⟨r, i⟩ ⟨r', i'⟩
    simp only [Matrix.of_apply, Matrix.submatrix_apply, Equiv.prodComm_apply, Prod.swap_prod_mk,
      blockDiagonal_apply, Matrix.smul_apply, smul_eq_mul]
  rw [hmat, det_submatrix_equiv_self, det_blockDiagonal]
  refine Finset.prod_ne_zero_iff.2 fun r _ => ?_
  rw [det_smul]
  exact mul_ne_zero (pow_ne_zero _ (hB r)) hH

theorem det_BB_ne_zero {c2 d : ℕ} (DD : Fin c2 → F) (hD : ∀ u, DD u ≠ 0) (CC : Fin c2 → Fin d → F)
    (EE : Matrix (Fin d) (Fin d) F)
    (hS : (EE - Matrix.of fun m m' => ∑ u, CC u m * (DD u)⁻¹ * CC u m').det ≠ 0) :
    (fromBlocks (diagonal DD) (Matrix.of CC) (Matrix.of CC)ᵀ EE).det ≠ 0 := by
  classical
  haveI : Invertible (diagonal DD) := invertibleOfIsUnitDet _ (by
    rw [det_diagonal]; exact isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun u _ => hD u))
  rw [det_fromBlocks₁₁]
  refine mul_ne_zero ?_ ?_
  · rw [det_diagonal]; exact Finset.prod_ne_zero_iff.2 fun u _ => hD u
  · have hinv : ⅟(diagonal DD) = diagonal (fun u => (DD u)⁻¹) := by
      refine invOf_eq_right_inv ?_
      rw [diagonal_mul_diagonal]
      have : (fun u => DD u * (DD u)⁻¹) = fun _ => (1 : F) := funext fun u => mul_inv_cancel₀ (hD u)
      rw [this]; exact diagonal_one
    have hm : (Matrix.of CC)ᵀ * diagonal (fun u => (DD u)⁻¹) * Matrix.of CC =
        Matrix.of fun m m' => ∑ u, CC u m * (DD u)⁻¹ * CC u m' := by
      ext m m'
      rw [Matrix.mul_apply]
      simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.of_apply]
    rw [hinv, hm]
    exact hS

end AlgField

section Signed

variable {F : Type*} [Field F]

theorem det_signed {d : ℕ} (M : Matrix (Fin d) (Fin d) F) :
    (Matrix.of fun i j : Fin d => (-1 : F) ^ ((i : ℕ) + j) * M i j).det = M.det := by
  have h1 : (Matrix.of fun i j : Fin d => (-1 : F) ^ ((i : ℕ) + j) * M i j) =
      Matrix.of fun i j : Fin d => (-1 : F) ^ (i : ℕ) * ((-1 : F) ^ (j : ℕ) * M i j) := by
    ext i j; simp only [Matrix.of_apply, pow_add]; ring
  have e2 := det_mul_column (fun i : Fin d => (-1 : F) ^ (i : ℕ))
    (Matrix.of fun i j : Fin d => (-1 : F) ^ (j : ℕ) * M i j)
  have e3 := det_mul_row (fun j : Fin d => (-1 : F) ^ (j : ℕ)) M
  simp only [Matrix.of_apply] at e2
  rw [h1, e2, e3, ← mul_assoc, ← Finset.prod_mul_distrib]
  have : ∏ i : Fin d, ((-1 : F) ^ (i : ℕ) * (-1 : F) ^ (i : ℕ)) = 1 := by
    refine Finset.prod_eq_one fun i _ => ?_
    rw [← mul_pow]; simp
  rw [this, one_mul]

end Signed

section Top

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-- **Content Lemma 2.4** (`T2 + T4 = 0`). -/
theorem sum_Ico_top (α A e : ℕ) (hαA : α ≤ A + 1) (hA : A + 1 < ℓ) (he : α + e + 2 ≤ ℓ) :
    ∑ s ∈ Ico α (A + 1), Dal ℓ α (s : ZMod ℓ) * (-(s : ZMod ℓ)) ^ e +
      ∑ s ∈ topS ℓ A, Dal ℓ α s * (-s) ^ e = 0 := by
  classical
  set P : (ZMod ℓ)[X] := (∏ i ∈ range α, (X - C (i : ZMod ℓ))) * (-X) ^ e with hP
  have hev : ∀ z : ZMod ℓ, P.eval z = Dal ℓ α z * (-z) ^ e := by
    intro z; simp [hP, eval_prod, Dal]
  have hdeg : P.natDegree ≤ ℓ - 1 := by
    refine (natDegree_mul_le).trans ?_
    rw [natDegree_finsetProd_X_sub_C_eq_card, card_range, natDegree_pow, natDegree_neg, natDegree_X]
    omega
  have hc : P.coeff (ℓ - 1) = 0 := by
    refine coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt natDegree_mul_le ?_)
    rw [natDegree_finsetProd_X_sub_C_eq_card, card_range, natDegree_pow, natDegree_neg, natDegree_X]
    omega
  have hsum := sum_eval_zmod P hdeg
  rw [hc, neg_zero] at hsum
  simp_rw [hev] at hsum
  have hu : lowS ℓ A ∪ topS ℓ A = Finset.univ :=
    Finset.eq_univ_of_forall fun z => mem_union.2 (low_or_top A hA.le z)
  rw [← hu, Finset.sum_union (disjoint_low_top A hA.le)] at hsum
  have hlow : ∑ z ∈ lowS ℓ A, Dal ℓ α z * (-z) ^ e =
      ∑ s ∈ Ico α (A + 1), Dal ℓ α (s : ZMod ℓ) * (-(s : ZMod ℓ)) ^ e := by
    rw [lowS, Finset.sum_image]
    · rw [← Finset.sum_range_add_sum_Ico _ hαA]
      have : ∑ s ∈ range α, Dal ℓ α (s : ZMod ℓ) * (-(s : ZMod ℓ)) ^ e = 0 := by
        refine Finset.sum_eq_zero fun s hs => ?_
        have : Dal ℓ α (s : ZMod ℓ) = 0 := Finset.prod_eq_zero hs (sub_self _)
        rw [this, zero_mul]
      rw [this, zero_add]
    · intro s hs t ht h
      exact cast_inj_lt (by have := mem_range.1 hs; omega) (by have := mem_range.1 ht; omega) h
  rw [hlow] at hsum
  exact hsum

end Top

end CatalanCore.Lai.NV7

end
