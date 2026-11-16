module

public import CatalanCore.Zeta5.Local.Reflect

@[expose] public section

/-!
# ZC24: the own-source symbol and its oddness under `r ↦ -1 - r`

For a finite set `I ⊆ ℤ` of consecutive integers (the local indices `r` of the poles of one class
`a` modulo `p`, `x = a + p r`) the *own-source symbol* is the bilinear form
`(U, V) ↦ τ₀(U V / B_I)`, `B_I = ∏_{k ∈ I} (X - k)`, where `τ₀(1/(r - k)) = H⁽⁵⁾_{d(k)}`,
`d(k) = k` for `k ≥ 0` and `-k-1` otherwise (`dd`).  Two versions are given.

* the **residue symbol** `resSym I h W = ∑_{k ∈ I} res_k (W / B_I) · h k` over an arbitrary field
  `F`, for a weight function `h : ℤ → F` with `h (-1-k) = h k` (for the leading form of the
  determinant entries `h k` is the harmonic number `H⁽⁵⁾_{d(k)}`; the polynomial part of the
  quotient is negligible there by the direct bound);
* the **full symbol** `tauX I (U V)` over `ℚ` (polynomial part included), `zc24_odd_full`.

For an interval `I` of **even** length symmetric under `refl` (`ℓ` even: the interval is centred at
`r = -1/2`, i.e. `z = r + 1/2 = 0`), `B_I(z - 1/2)` is even and both symbols are odd under
`J : r ↦ -1 - r`:  `C(JU, JV) = -C(U, V)` (`zc24_odd`, `zc24_odd_full`).  Also `z^i` has parity `i`
(`zpow_comp_J`).
-/

open Finset Polynomial

namespace Apery

section generic
variable {F : Type*} [Field F]

/-- `B_I = ∏_{k ∈ I} (X - k)` over a field. -/
noncomputable def piF (I : Finset ℤ) : F[X] := ∏ k ∈ I, (X - C (k : F))

/-- The reflection `J : U ↦ U(-1 - X)` of polynomials. -/
noncomputable def Jr (U : F[X]) : F[X] := U.comp (-X - 1)

lemma Jr_mul (U V : F[X]) : Jr (U * V) = Jr U * Jr V := by simp [Jr, mul_comp]
lemma Jr_add (U V : F[X]) : Jr (U + V) = Jr U + Jr V := by simp [Jr, add_comp]
lemma Jr_C_mul (c : F) (U : F[X]) : Jr (C c * U) = C c * Jr U := by simp [Jr, mul_comp]
lemma Jr_Jr (U : F[X]) : Jr (Jr U) = U := by
  simp only [Jr, comp_assoc]
  have : ((-X - 1 : F[X]).comp (-X - 1)) = X := by
    simp only [sub_comp, neg_comp, X_comp, one_comp]; ring
  rw [this, comp_X]

/-- The centred variable `z = r + 1/2`. -/
noncomputable def zv : F[X] := X + C (1 / 2 : F)

lemma Jr_zv (hF : (2 : F) ≠ 0) : Jr (zv : F[X]) = - zv := by
  simp only [Jr, zv, add_comp, X_comp, C_comp, neg_add]
  have : C (1 / 2 : F) + C (1 / 2 : F) = (1 : F[X]) := by
    rw [← C_add, ← C_1]; congr 1; field_simp; norm_num
  linear_combination this

lemma Jr_zpow (hF : (2 : F) ≠ 0) (i : ℕ) : Jr ((zv : F[X]) ^ i) = (-1) ^ i * zv ^ i := by
  induction i with
  | zero => simp [Jr]
  | succ i ih =>
    rw [pow_succ, Jr_mul, ih, Jr_zv hF]; ring

/-- The symmetric even interval: closed under `refl` and of even cardinality. -/
lemma piF_Jr {I : Finset ℤ} (hsym : I.image refl = I) (hev : Even I.card) :
    Jr (piF I : F[X]) = piF I := by
  have h1 : Jr (piF I : F[X]) = C ((-1 : F) ^ I.card) * (∏ k ∈ I.image refl, (X - C (k : F))) := by
    rw [Finset.prod_image (fun a _ b _ h => refl_injective h)]
    unfold Jr piF
    rw [Polynomial.prod_comp,
      show C ((-1 : F) ^ I.card) = ∏ _s ∈ I, C (-1 : F) by rw [Finset.prod_const, map_pow],
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun s _ => ?_
    simp only [refl, sub_comp, X_comp, C_comp]
    push_cast
    simp only [C_sub, C_neg, C_1]
    ring
  rw [h1, hsym, hev.neg_one_pow]; simp [piF]

/-- The residue symbol `∑_{k ∈ I} res_k(W / B_I) h(k)`. -/
noncomputable def resSym (I : Finset ℤ) (h : ℤ → F) (W : F[X]) : F :=
  ∑ k ∈ I, W.eval (k : F) / (∏ s ∈ I.erase k, ((k : F) - s)) * h k

lemma resSym_add (I : Finset ℤ) (h : ℤ → F) (W W' : F[X]) :
    resSym I h (W + W') = resSym I h W + resSym I h W' := by
  unfold resSym; rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [eval_add]; ring

lemma resSym_smul (I : Finset ℤ) (h : ℤ → F) (c : F) (W : F[X]) :
    resSym I h (C c * W) = c * resSym I h W := by
  unfold resSym; rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [eval_mul, eval_C]; ring

lemma resSym_sum {ι : Type*} (s : Finset ι) (I : Finset ℤ) (h : ℤ → F) (W : ι → F[X]) :
    resSym I h (∑ i ∈ s, W i) = ∑ i ∈ s, resSym I h (W i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [resSym]
  | insert a s ha ih => rw [Finset.sum_insert ha, resSym_add, ih, Finset.sum_insert ha]

lemma resSym_zero (I : Finset ℤ) (h : ℤ → F) : resSym I h 0 = 0 := by simp [resSym]

/-- **ZC24 (residue form).**  Oddness of the own-source residue symbol under `J` for an even
symmetric interval.  `h` is the (reflection invariant) weight `H⁽⁵⁾_{d(k)}`. -/
theorem zc24_odd {I : Finset ℤ} (hsym : I.image refl = I) (hev : Even I.card) (h : ℤ → F)
    (hh : ∀ k, h (refl k) = h k) (W : F[X]) :
    resSym I h (Jr W) = - resSym I h W := by
  unfold resSym
  rw [← Finset.sum_neg_distrib]
  have hbij : ∀ k ∈ I, (refl k ∈ I) := fun k hk => by
    rw [← hsym]; exact Finset.mem_image_of_mem _ hk
  -- reindex the left sum by `k ↦ refl k`
  refine Finset.sum_bij (fun k _ => refl k) hbij (fun a _ b _ hab => refl_injective hab)
    (fun k hk => ⟨refl k, hbij k hk, refl_refl k⟩) fun k hk => ?_
  have hcard : (-1 : F) ^ (I.card - 1) = -1 := by
    obtain ⟨m, hm⟩ := hev
    have hpos : 1 ≤ I.card := by
      by_contra h0
      have : I.card = 0 := by omega
      rw [this] at hm
      have : I = ∅ := Finset.card_eq_zero.mp this
      subst this
      exact absurd (hbij k hk) (by simp)
    have : I.card - 1 = 2 * (m - 1) + 1 := by omega
    rw [this, pow_succ, pow_mul]; simp
  have hden : ∏ s ∈ I.erase (refl k), (((refl k : ℤ) : F) - (s : F)) =
      (-1) ^ (I.card - 1) * ∏ s ∈ I.erase k, ((k : F) - (s : F)) := by
    have himg : I.erase (refl k) = (I.erase k).image refl := by
      rw [Finset.image_erase refl_injective, hsym]
    rw [himg, Finset.prod_image (fun a _ b _ hab => refl_injective hab)]
    have hc : (I.erase k).card = I.card - 1 := Finset.card_erase_of_mem hk
    rw [← hc, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun s _ => ?_
    simp only [refl]; push_cast; ring
  have hev' : ((Jr W).eval (k : F)) = W.eval (((refl k : ℤ)) : F) := by
    simp only [Jr, eval_comp, eval_sub, eval_neg, eval_X, eval_one, refl]; push_cast; ring_nf
  rw [hev', hden, hcard, hh k]
  rw [show (-1 : F) * ∏ s ∈ I.erase k, ((k : F) - (s : F)) = -∏ s ∈ I.erase k, ((k : F) - (s : F))
      by ring, div_neg]
  ring

/-- The harmonic weight `H⁽⁵⁾_{d(k)}` in a field of characteristic `0` or any field, via the cast
of the rational number. -/
noncomputable def H5w (F : Type*) [Field F] (k : ℤ) : F := ((H5 (dd k) : ℚ) : F)

lemma H5w_refl (k : ℤ) : H5w F (refl k) = H5w F k := by
  unfold H5w; rw [dd_refl]

/-- The own-source bilinear form `C(U, V) = τ₀(U V / B_I)` (residue part). -/
noncomputable def ownSym (I : Finset ℤ) (h : ℤ → F) (U V : F[X]) : F := resSym I h (U * V)

/-- **ZC24.**  For an even symmetric interval, `C(JU, JV) = -C(U, V)`. -/
theorem zc24_own_odd {I : Finset ℤ} (hsym : I.image refl = I) (hev : Even I.card) (h : ℤ → F)
    (hh : ∀ k, h (refl k) = h k) (U V : F[X]) :
    ownSym I h (Jr U) (Jr V) = - ownSym I h U V := by
  unfold ownSym; rw [← Jr_mul]; exact zc24_odd hsym hev h hh _

/-- The pairing of two even (resp. two odd) polynomials vanishes: `J U = ± U`, `J V = ± V` with
the same sign gives `C(U, V) = 0` (characteristic `≠ 2`). -/
theorem zc24_own_same_parity {I : Finset ℤ} (hsym : I.image refl = I) (hev : Even I.card)
    (h : ℤ → F) (hh : ∀ k, h (refl k) = h k) (hF : (2 : F) ≠ 0) {U V : F[X]} {e : F}
    (he : e = 1 ∨ e = -1) (hU : Jr U = C e * U) (hV : Jr V = C e * V) :
    ownSym I h U V = 0 := by
  have h1 := zc24_own_odd hsym hev h hh U V
  rw [hU, hV] at h1
  have h2 : C e * U = U * C e := mul_comm _ _
  unfold ownSym at h1 ⊢
  have h3 : (C e * U) * (C e * V) = U * V := by
    have : e * e = 1 := by rcases he with rfl | rfl <;> ring
    calc (C e * U) * (C e * V) = C (e * e) * (U * V) := by rw [C_mul]; ring
      _ = U * V := by rw [this, C_1, one_mul]
  rw [h3] at h1
  have : (2 : F) * resSym I h (U * V) = 0 := by linear_combination h1
  rcases mul_eq_zero.mp this with h4 | h4
  · exact absurd h4 hF
  · exact h4

end generic

/-! ### The full symbol over `ℚ` (polynomial part included) -/

/-- **ZC24 (full symbol).**  `τ_X(U V / B_I)`, with the polynomial part of the quotient included,
is odd under `J` for an even symmetric interval: `C(JU, JV) = -C(U, V)`. -/
theorem zc24_odd_full {I : Finset ℤ} (hsym : I.image refl = I) (hev : Even I.card)
    (U V : ℚ[X]) : tauX (Jr U * Jr V) I = - tauX (U * V) I := by
  have h := tauX_reflect (U * V) I
  rw [hsym] at h
  have : reflNum I (U * V) = Jr U * Jr V := by
    unfold reflNum; rw [hev.neg_one_pow]; simp [Jr, mul_comp]
  rwa [this] at h

end Apery
