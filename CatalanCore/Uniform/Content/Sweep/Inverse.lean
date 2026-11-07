module

public import CatalanCore.Uniform.Content.Sweep.CellAction
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

/-!
# The inverse of the sweep (lane H, wave H2; ledger P203)

**Lemma 3** of the sweep (`PLANE2-SIMPLIFICATION` §1.2).  Let `R` be a local ring, algebra over `ℤ_(p)`
(`p ≥ 5` prime), whose maximal ideal is `(p)`: the paper's `𝒪 = ℤ_(p)[X]_(p)` is the example, with residue
field `𝔽_p(X)`, but nothing else about it is used.  Fix integers `v, u ≠ 0`, `ξ ∈ R`, `κ ≥ 1`, `N ≥ κ p`
with `2N < p²`, and let `Q = p³ H[K]` on `K = [0, κ p)`, `Q(n, t) = Qent n t` (`CellAction`), so that
`H = p⁻³ Q`.  Let `B̄` be the `κ × κ` matrix over the residue field

  `B̄[l, l] = ξ̄ + p³ Ḡ(l)`,   `B̄[l, j] = p²(S̄(l) - S̄(j))/(l - j)`  (`l ≠ j`),

the reduction of the matrix `Bent` of the cell operator `𝐁` (`Bop`) on the first half of each period
(`Bent_res_half`: the second half gives the same matrix).  If `det B̄ ≠ 0`, then

* **(a)** `Q ≡ B̄ ⊗ I_p (mod p)` (`res_Qmat`), so `det Q` is a unit of `R` (`isUnit_det_Qmat`); that is,
  `v(det H[K]) = -3|K|` and `Z = H[K]⁻¹ = p³ Q⁻¹ ∈ p³ Mat(R)`;
* **(b)** `𝐁` is bijective on the functions with `φ(j,0) ≡ φ(j,1) (mod p)` (`Bop_bijective`): for each such
  `e` there is exactly one `γ` (on the cells of `K`) with `𝐁 γ = e`, and it again satisfies
  `γ(j,0) ≡ γ(j,1)`;
* **(c)** with `y = Q⁻¹ ẽ` (`Ysol`; `ẽ = e ∘ cell`): `Q y = ẽ`, `y ≡ γ̃ (mod p²)`, that is
  `Z ẽ ≡ p³ γ̃ (mod p⁵)`, and for every node `n < N`, in particular outside `K`,
  `p³ H(n, K) Z ẽ = (Q y)(n) ≡ (𝐁 γ)(cell n) (mod p²)` (`sweep_inverse`).

Instead of the paper's finiteness argument for (b) (injective, hence surjective, on `𝒱 / p 𝒪^{2κ}`), the
proof inverts the two `κ × κ` matrices of `𝐁` on the two halves over `R` (their reductions are both `B̄`) and
checks that the solution lies in `𝒱` by reducing the difference of the two halves.  No valuation function and
no property of `R` beyond `maximalIdeal R = (p)` is used.
-/

open Polynomial Finset Matrix CatalanCore.Basic CatalanCore.Arith.Hybrid
open CatalanCore.Uniform.Support
open scoped Kronecker

namespace CatalanCore.Uniform.Content.Sweep

/-! ### Reduction modulo the maximal ideal -/

section Residue

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] [IsLocalRing R]
  [Algebra (LocRing p) R]

theorem residue_eq_zero_iff_dvd (hmax : IsLocalRing.maximalIdeal R = Ideal.span {(p : R)}) (x : R) :
    IsLocalRing.residue R x = 0 ↔ (p : R) ∣ x := by
  rw [IsLocalRing.residue_eq_zero_iff, hmax, Ideal.mem_span_singleton]

theorem res_toR_zero (hmax : IsLocalRing.maximalIdeal R = Ideal.span {(p : R)}) {x : ℚ}
    (hx : Dv p 1 x) : IsLocalRing.residue R (toR p x : R) = 0 := by
  rw [residue_eq_zero_iff_dvd hmax]
  simpa using toR_dvd (R := R) hx

theorem res_toR_congr (hmax : IsLocalRing.maximalIdeal R = Ideal.span {(p : R)}) {a b : ℚ}
    (ha : a ∈ LocRing p) (hb : b ∈ LocRing p) (h : Dv p 1 (a - b)) :
    IsLocalRing.residue R (toR p a : R) = IsLocalRing.residue R (toR p b : R) := by
  have := res_toR_zero hmax (R := R) h
  rw [toR_sub (R := R) ha hb, map_sub, sub_eq_zero] at this
  exact this

theorem kappa_lt {N κ : ℕ} (hκN : κ * p ≤ N) (hN : 2 * N < p * p) : κ < p := by
  by_contra hge
  have := Nat.mul_le_mul_right p (not_lt.1 hge)
  nlinarith

theorem odd_of_ge5 (hp5 : 5 ≤ p) : p % 2 = 1 := by
  rcases hp.out.eq_two_or_odd with h | h
  · omega
  · exact h

end Residue

/-! ### The matrix of `𝐁` on one half of the periods -/

section Bent

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] [Algebra (LocRing p) R]

variable (p) in
/-- The entry `(l, j)` of the matrix of `𝐁` on the cells `(·, h)`:
`ξ + p³ G(l,h)` on the diagonal, `p²(S(l,h) - S(j,h))/(l - j)` off it. -/
noncomputable def Bent (v u : ℤ) (ξ : R) (h l j : ℕ) : R :=
  if l = j then ξ + toR p ((p : ℚ) ^ 3 * Gcell v u p (l, h))
  else toR p ((p : ℚ) ^ 2 * (Scell v u p (l, h) - Scell v u p (j, h)) / ((l : ℚ) - j))

variable (v u : ℤ)

theorem Bop_eq_sum (ξ : R) (κ : ℕ) (φ : ℕ × ℕ → R) {l : ℕ} (hl : l < κ) (h : ℕ) :
    Bop (p := p) v u ξ κ φ (l, h) = ∑ j ∈ range κ, Bent p v u ξ h l j * φ (j, h) := by
  have hterm : ∀ j ∈ range κ, Bent p v u ξ h l j * φ (j, h) =
      (if j = l then (ξ + toR p ((p : ℚ) ^ 3 * Gcell v u p (l, h))) * φ (l, h) else 0) +
      (if j = l then 0 else
        toR p ((p : ℚ) ^ 2 * (Scell v u p (l, h) - Scell v u p (j, h)) / ((l : ℚ) - j)) *
          φ (j, h)) := by
    intro j _
    by_cases hjl : j = l
    · subst hjl; simp [Bent]
    · simp [Bent, hjl, Ne.symm hjl]
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_ite_eq',
    if_pos (Finset.mem_range.2 hl)]
  unfold Bop
  simp only [hl, if_true]

end Bent

/-! ### The reduction of the entries -/

section Entries

variable {p : ℕ} [hp : Fact p.Prime] (v u : ℤ) (hv : v ≠ 0) (hu : u ≠ 0) {N : ℕ}
  {R : Type*} [CommRing R] [IsLocalRing R] [Algebra (LocRing p) R]

theorem res_G_half (hmax : IsLocalRing.maximalIdeal R = Ideal.span {(p : R)}) (hodd : p % 2 = 1)
    (hN : 2 * N < p * p) {l : ℕ} (hl : (l + 1) * p ≤ N) {h : ℕ} (hh : h ≤ 1) :
    IsLocalRing.residue R (toR p ((p : ℚ) ^ 3 * Gcell v u p (l, h)) : R) =
      IsLocalRing.residue R (toR p ((p : ℚ) ^ 3 * Gcell v u p (l, 0)) : R) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hh with rfl | rfl
  · rfl
  · refine (res_toR_congr hmax (G_mem_cell v u hodd hN hl (by norm_num))
      (G_mem_cell v u hodd hN hl (by norm_num)) ?_).symm
    have h := Gcell_halves v u hodd hN hl
    rwa [mul_sub] at h

theorem res_S_half (hmax : IsLocalRing.maximalIdeal R = Ideal.span {(p : R)}) (hodd : p % 2 = 1)
    (hN : 2 * N < p * p) {l j : ℕ} (hl : (l + 1) * p ≤ N) (hj : (j + 1) * p ≤ N) (hlj : l ≠ j)
    (hlp : l < p) (hjp : j < p) {h : ℕ} (hh : h ≤ 1) :
    IsLocalRing.residue R (toR p ((p : ℚ) ^ 2 * (Scell v u p (l, h) - Scell v u p (j, h)) /
        ((l : ℚ) - j)) : R) =
      IsLocalRing.residue R (toR p ((p : ℚ) ^ 2 * (Scell v u p (l, 0) - Scell v u p (j, 0)) /
        ((l : ℚ) - j)) : R) := by
  have hunit := unit_diff (p := p) hlj hlp hjp
  have hmem : ∀ h' : ℕ, h' ≤ 1 → (p : ℚ) ^ 2 * (Scell v u p (l, h') - Scell v u p (j, h')) /
      ((l : ℚ) - j) ∈ LocRing p := fun h' hh' => by
    rw [div_eq_mul_inv]
    exact (LocRing p).mul_mem (S_diff_mem v u hodd hN hl hj hh') hunit
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hh with rfl | rfl
  · rfl
  · refine (res_toR_congr hmax (hmem 0 (by norm_num)) (hmem 1 (by norm_num)) ?_).symm
    have e : (p : ℚ) ^ 2 * (Scell v u p (l, 0) - Scell v u p (j, 0)) / ((l : ℚ) - j) -
        (p : ℚ) ^ 2 * (Scell v u p (l, 1) - Scell v u p (j, 1)) / ((l : ℚ) - j) =
        -(((l : ℚ) - j)⁻¹ * ((p : ℚ) ^ 2 * (Scell v u p (l, 1) - Scell v u p (l, 0)) -
          (p : ℚ) ^ 2 * (Scell v u p (j, 1) - Scell v u p (j, 0)))) := by
      ring
    rw [e]
    exact Dv.neg (Dv.mul_mem hunit (Dv.sub (Scell_halves v u hodd hN hl)
      (Scell_halves v u hodd hN hj)))

theorem res_Bent_half (hmax : IsLocalRing.maximalIdeal R = Ideal.span {(p : R)}) (hodd : p % 2 = 1)
    (hN : 2 * N < p * p) {l j : ℕ} (hl : (l + 1) * p ≤ N) (hj : (j + 1) * p ≤ N)
    (hlp : l < p) (hjp : j < p) (ξ : R) {h : ℕ} (hh : h ≤ 1) :
    IsLocalRing.residue R (Bent p v u ξ h l j) = IsLocalRing.residue R (Bent p v u ξ 0 l j) := by
  by_cases hlj : l = j
  · unfold Bent
    rw [if_pos hlj, if_pos hlj, map_add, map_add, res_G_half v u hmax hodd hN hl hh]
  · unfold Bent
    rw [if_neg hlj, if_neg hlj]
    exact res_S_half v u hmax hodd hN hl hj hlj hlp hjp hh

/-- Off the residue classes of `B̄`, the entries of `Q` are `0 (mod p)`. -/
theorem Dv_q_far (hN : 2 * N < p * p) {a b : ℕ} (ha : a < N) (hb : b < N) (hmod : a % p ≠ b % p) :
    Dv p 1 ((p : ℚ) ^ 3 * Lm v u hv hu a b) := by
  have h := weight_table v u hv hu hN a b ha hb
  have hne : a ≠ b := fun h => hmod (h ▸ rfl)
  have hW : Wt p a b ≤ 2 := by
    unfold Wt w3
    rw [if_neg hne, if_neg hmod]
    split_ifs <;> omega
  have h2 := Dv.of_Vp (k := 3 - Wt p a b) h
  rw [show Wt p a b + (3 - Wt p a b) = 3 by omega] at h2
  exact Dv.mono (by omega) h2

/-- **The reduction of `Q = p³ H[K]`**: entry by entry, `Q ≡ B̄ ⊗ I_p (mod p)`. -/
theorem res_Qent (hmax : IsLocalRing.maximalIdeal R = Ideal.span {(p : R)}) (hp5 : 5 ≤ p)
    (hN : 2 * N < p * p) {κ : ℕ} (hκN : κ * p ≤ N) (ξ : R) {n t : ℕ} (hn : n < κ * p)
    (ht : t < κ * p) :
    IsLocalRing.residue R (Qent (p := p) v u hv hu ξ n t) =
      if n % p = t % p then IsLocalRing.residue R (Bent p v u ξ 0 (n / p) (t / p)) else 0 := by
  have hp0 : 0 < p := hp.out.pos
  have hodd := odd_of_ge5 hp5
  have hκp := kappa_lt hκN hN
  have hnN : n < N := lt_of_lt_of_le hn hκN
  have htN : t < N := lt_of_lt_of_le ht hκN
  have hnl : n / p < κ := (Nat.div_lt_iff_lt_mul hp0).2 hn
  have htl : t / p < κ := (Nat.div_lt_iff_lt_mul hp0).2 ht
  have hlN : (n / p + 1) * p ≤ N := le_trans (Nat.mul_le_mul_right p hnl) hκN
  have hjN : (t / p + 1) * p ≤ N := le_trans (Nat.mul_le_mul_right p htl) hκN
  by_cases hmod : n % p = t % p
  · rw [if_pos hmod]
    by_cases hnt : n = t
    · subst hnt
      have hhh : half p n ≤ 1 := by rcases half_eq (p := p) n with h | h <;> omega
      unfold Qent Bent
      rw [if_pos rfl, if_pos rfl, map_add, map_add]
      congr 1
      have h1 := res_toR_congr hmax (q_mem v u hv hu hN hnN hnN) (G_mem v u hodd hN hnN)
        (Dv.mono (by norm_num) (Dv_q_diag v u hv hu hodd (a := n)))
      rw [h1]
      exact res_G_half v u hmax hodd hN hlN hhh
    · have hlj : n / p ≠ t / p := fun h => hnt (by
        have h1 := Nat.div_add_mod n p
        have h2 := Nat.div_add_mod t p
        rw [h, hmod] at h1
        omega)
      have hq := q_decomp v u hv hu hodd hp5 hN hnN htN hnt
      have hhn : half p n ≤ 1 := by rcases half_eq (p := p) n with h | h <;> omega
      have hht : half p t = half p n := by unfold half; rw [hmod]
      have hcellt : cell p t = (t / p, half p n) := by
        show (t / p, half p t) = _
        rw [hht]
      have hcelln : cell p n = (n / p, half p n) := rfl
      have hn' : (n : ℚ) = p * (n / p : ℕ) + (n % p : ℕ) := by
        exact_mod_cast (Nat.div_add_mod n p).symm
      have ht' : (t : ℚ) = p * (t / p : ℕ) + (t % p : ℕ) := by
        exact_mod_cast (Nat.div_add_mod t p).symm
      have hmodq : ((n % p : ℕ) : ℚ) = ((t % p : ℕ) : ℚ) := by rw [hmod]
      have hdiff : (t : ℚ) - n = (((t / p : ℕ) : ℚ) - ((n / p : ℕ) : ℚ)) * p := by
        rw [hn', ht', hmodq]; ring
      have hp0q : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
      have hlj' : (((n / p : ℕ) : ℚ) - ((t / p : ℕ) : ℚ)) ≠ 0 :=
        sub_ne_zero.2 (by exact_mod_cast hlj)
      have hjl' : (((t / p : ℕ) : ℚ) - ((n / p : ℕ) : ℚ)) ≠ 0 :=
        sub_ne_zero.2 (by exact_mod_cast (Ne.symm hlj))
      have hb : (p : ℚ) * sdiff v u p n (cell p t) * (((t : ℚ) - n)⁻¹) =
          (p : ℚ) ^ 2 * (Scell v u p (n / p, half p n) - Scell v u p (t / p, half p n)) /
            (((n / p : ℕ) : ℚ) - ((t / p : ℕ) : ℚ)) := by
        unfold sdiff
        rw [hcellt, hcelln, hdiff]
        field_simp
        ring
      rw [hb] at hq
      have hunit := unit_diff (p := p) hlj (by omega) (by omega)
      have hcmem : (p : ℚ) ^ 2 * (Scell v u p (n / p, half p n) - Scell v u p (t / p, half p n)) /
            (((n / p : ℕ) : ℚ) - ((t / p : ℕ) : ℚ)) ∈ LocRing p := by
        rw [div_eq_mul_inv]
        exact (LocRing p).mul_mem (S_diff_mem v u hodd hN hlN hjN hhn) hunit
      have h1 := res_toR_congr hmax (q_mem v u hv hu hN hnN htN) hcmem (Dv.mono (by norm_num) hq)
      unfold Qent
      rw [if_neg hnt, zero_add, h1]
      unfold Bent
      rw [if_neg hlj]
      exact res_S_half v u hmax hodd hN hlN hjN hlj (by omega) (by omega) hhn
  · rw [if_neg hmod]
    have hne : n ≠ t := fun h => hmod (h ▸ rfl)
    unfold Qent
    rw [if_neg hne, zero_add]
    exact res_toR_zero hmax (Dv_q_far v u hv hu hN hnN htN hmod)

end Entries

/-! ### The matrices, and part (a) -/

section Matrices

variable {p : ℕ} [hp : Fact p.Prime] (v u : ℤ) (hv : v ≠ 0) (hu : u ≠ 0) {N : ℕ}
  {R : Type*} [CommRing R] [IsLocalRing R] [Algebra (LocRing p) R]

variable (p) in
/-- `B̄`, the reduction of the matrix of `𝐁` on the first half of the periods. -/
noncomputable def Bbar (v u : ℤ) (ξ : R) (κ : ℕ) :
    Matrix (Fin κ) (Fin κ) (IsLocalRing.ResidueField R) :=
  Matrix.of fun a b => IsLocalRing.residue R (Bent p v u ξ 0 a b)

variable (p) in
/-- The matrix of `𝐁` on the cells `(·, h)` over `R`. -/
noncomputable def Bmat (v u : ℤ) (ξ : R) (κ h : ℕ) :
    Matrix (Fin κ) (Fin κ) R :=
  Matrix.of fun a b => Bent p v u ξ h a b

variable (p) in
/-- `Q = p³ H[K]` on the nodes `[0, κ p)`. -/
noncomputable def Qmat (v u : ℤ) (hv : v ≠ 0) (hu : u ≠ 0) (ξ : R) (κ : ℕ) :
    Matrix (Fin (κ * p)) (Fin (κ * p)) R :=
  Matrix.of fun a b => Qent (p := p) v u hv hu ξ a b

theorem Bmat_res (hmax : IsLocalRing.maximalIdeal R = Ideal.span {(p : R)}) (hp5 : 5 ≤ p)
    (hN : 2 * N < p * p) {κ : ℕ} (hκN : κ * p ≤ N) (ξ : R) {h : ℕ} (hh : h ≤ 1) :
    (Bmat p v u ξ κ h).map (IsLocalRing.residue R) = Bbar p v u ξ κ := by
  have hκp := kappa_lt hκN hN
  ext a b
  have ha := a.2
  have hb := b.2
  simp only [Matrix.map_apply, Bmat, Bbar, Matrix.of_apply]
  exact res_Bent_half v u hmax (odd_of_ge5 hp5) hN
    (le_trans (Nat.mul_le_mul_right p ha) hκN) (le_trans (Nat.mul_le_mul_right p hb) hκN)
    (by omega) (by omega) ξ hh

/-- **Lemma 3 (a), reduction**: `Q ≡ B̄ ⊗ I_p (mod p)`, in the node order `(period, residue)`. -/
theorem res_Qmat (hmax : IsLocalRing.maximalIdeal R = Ideal.span {(p : R)}) (hp5 : 5 ≤ p)
    (hN : 2 * N < p * p) {κ : ℕ} (hκN : κ * p ≤ N) (ξ : R) :
    Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm
        ((Qmat p v u hv hu ξ κ).map (IsLocalRing.residue R)) =
      Bbar p v u ξ κ ⊗ₖ (1 : Matrix (Fin p) (Fin p) (IsLocalRing.ResidueField R)) := by
  have hp0 : 0 < p := hp.out.pos
  ext ⟨⟨i, hi⟩, ⟨r, hr⟩⟩ ⟨⟨j, hj⟩, ⟨s, hs⟩⟩
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.map_apply, Qmat, Matrix.of_apply, Equiv.symm_symm,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Bbar, finProdFinEquiv_apply_val]
  have hi' : i < κ := hi
  have hj' : j < κ := hj
  have hn : r + p * i < κ * p := by nlinarith
  have ht : s + p * j < κ * p := by nlinarith
  have hq := res_Qent v u hv hu hmax hp5 hN hκN ξ hn ht
  have hmr : (r + p * i) % p = r := by
    rw [Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt hr
  have hms : (s + p * j) % p = s := by
    rw [Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt hs
  have hdr : (r + p * i) / p = i := by
    rw [Nat.add_mul_div_left _ _ hp0, Nat.div_eq_of_lt hr, zero_add]
  have hds : (s + p * j) / p = j := by
    rw [Nat.add_mul_div_left _ _ hp0, Nat.div_eq_of_lt hs, zero_add]
  rw [hq, hmr, hms, hdr, hds]
  by_cases hrs : r = s
  · subst hrs; simp
  · have hne : (⟨r, hr⟩ : Fin p) ≠ ⟨s, hs⟩ := fun h => hrs (Fin.mk.inj h)
    simp [hrs, hne]

/-- **Lemma 3 (a)**: `det Q` is a unit of `R` when `det B̄ ≠ 0`; equivalently `v(det H[K]) = -3|K|`
and `Z = H[K]⁻¹ = p³ Q⁻¹ ∈ p³ Mat(R)`. -/
theorem isUnit_det_Qmat (hmax : IsLocalRing.maximalIdeal R = Ideal.span {(p : R)}) (hp5 : 5 ≤ p)
    (hN : 2 * N < p * p) {κ : ℕ} (hκN : κ * p ≤ N) (ξ : R)
    (hB : (Bbar p v u ξ κ).det ≠ 0) : IsUnit (Qmat p v u hv hu ξ κ).det := by
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
  change ((Qmat p v u hv hu ξ κ).map (IsLocalRing.residue R)).det ≠ 0
  rw [← Matrix.det_reindex_self finProdFinEquiv.symm, res_Qmat v u hv hu hmax hp5 hN hκN ξ,
    Matrix.det_kronecker]
  simpa using pow_ne_zero p hB

theorem isUnit_det_Bmat (hmax : IsLocalRing.maximalIdeal R = Ideal.span {(p : R)}) (hp5 : 5 ≤ p)
    (hN : 2 * N < p * p) {κ : ℕ} (hκN : κ * p ≤ N) (ξ : R) {h : ℕ} (hh : h ≤ 1)
    (hB : (Bbar p v u ξ κ).det ≠ 0) : IsUnit (Bmat p v u ξ κ h).det := by
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
  change ((Bmat p v u ξ κ h).map (IsLocalRing.residue R)).det ≠ 0
  rw [Bmat_res v u hmax hp5 hN hκN ξ hh]
  exact hB

end Matrices

/-! ### Parts (b) and (c) -/

section Inverse

variable {p : ℕ} [hp : Fact p.Prime] (v u : ℤ) (hv : v ≠ 0) (hu : u ≠ 0) {N : ℕ}
  {R : Type*} [CommRing R] [IsLocalRing R] [Algebra (LocRing p) R]

theorem Bop_mulVec (ξ : R) (κ : ℕ) (φ : ℕ × ℕ → R) (h : ℕ) (l : Fin κ) :
    Bop (p := p) v u ξ κ φ (l, h) =
      ((Bmat p v u ξ κ h) *ᵥ (fun i : Fin κ => φ (i, h))) l := by
  rw [Bop_eq_sum v u ξ κ φ l.2 h, Finset.sum_range]
  simp [Matrix.mulVec, dotProduct, Bmat]

/-- **Lemma 3 (b)**: `𝐁` is bijective on the functions `φ` on the cells of `K` with
`φ(j,0) ≡ φ(j,1) (mod p)`.  For such an `e` there is a unique `γ` with `𝐁 γ = e` on the cells of `K`, and it
lies in the same class. -/
theorem Bop_bijective (hmax : IsLocalRing.maximalIdeal R = Ideal.span {(p : R)}) (hp5 : 5 ≤ p)
    (hN : 2 * N < p * p) {κ : ℕ} (hκN : κ * p ≤ N) (ξ : R)
    (hB : (Bbar p v u ξ κ).det ≠ 0) (e : ℕ × ℕ → R)
    (he : ∀ j < κ, (p : R) ∣ e (j, 0) - e (j, 1)) :
    ∃ γ : ℕ × ℕ → R, (∀ j < κ, (p : R) ∣ γ (j, 0) - γ (j, 1)) ∧
      (∀ l < κ, ∀ h ≤ 1, Bop (p := p) v u ξ κ γ (l, h) = e (l, h)) ∧
      ∀ γ' : ℕ × ℕ → R, (∀ l < κ, ∀ h ≤ 1, Bop (p := p) v u ξ κ γ' (l, h) = e (l, h)) →
        ∀ j < κ, ∀ h ≤ 1, γ' (j, h) = γ (j, h) := by
  have hunit : ∀ h, h ≤ 1 → IsUnit (Bmat p v u ξ κ h).det :=
    fun h hh => isUnit_det_Bmat v u hmax hp5 hN hκN ξ hh hB
  let vec : ℕ → Fin κ → R := fun h i => e (i, h)
  let γ : ℕ × ℕ → R := fun c =>
    if hc : c.1 < κ then ((Bmat p v u ξ κ c.2)⁻¹ *ᵥ vec c.2) ⟨c.1, hc⟩ else 0
  have hγvec : ∀ h, (fun i : Fin κ => γ (i, h)) = (Bmat p v u ξ κ h)⁻¹ *ᵥ vec h := by
    intro h; funext i; simp [γ, i.2]
  have hsol : ∀ h, h ≤ 1 → (Bmat p v u ξ κ h) *ᵥ (fun i : Fin κ => γ (i, h)) = vec h := by
    intro h hh
    rw [hγvec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hunit h hh), Matrix.one_mulVec]
  have hBγ : ∀ l < κ, ∀ h ≤ 1, Bop (p := p) v u ξ κ γ (l, h) = e (l, h) := by
    intro l hl h hh
    have := congrFun (hsol h hh) ⟨l, hl⟩
    rw [← Bop_mulVec v u ξ κ γ h ⟨l, hl⟩] at this
    exact this
  refine ⟨γ, ?_, hBγ, ?_⟩
  · -- the class `𝒱`: reduce the difference of the two halves
    let rγ : ℕ → Fin κ → IsLocalRing.ResidueField R := fun h i => IsLocalRing.residue R (γ (i, h))
    have hres : ∀ h, h ≤ 1 → (Bbar p v u ξ κ) *ᵥ rγ h =
        fun l => IsLocalRing.residue R (vec h l) := by
      intro h hh
      funext l
      rw [← hsol h hh]
      have := RingHom.map_mulVec (IsLocalRing.residue R) (Bmat p v u ξ κ h)
        (fun i : Fin κ => γ (i, h)) l
      rw [this, Bmat_res v u hmax hp5 hN hκN ξ hh]
      rfl
    have hzero : (Bbar p v u ξ κ) *ᵥ (rγ 0 - rγ 1) = 0 := by
      rw [Matrix.mulVec_sub, hres 0 (by norm_num), hres 1 (by norm_num)]
      funext l
      simp only [Pi.sub_apply, Pi.zero_apply, vec]
      rw [← map_sub, (residue_eq_zero_iff_dvd hmax _).2 (he l l.2)]
    have h0 := Matrix.eq_zero_of_mulVec_eq_zero hB hzero
    intro j hj
    have := congrFun h0 ⟨j, hj⟩
    have h3 : IsLocalRing.residue R (γ (j, 0) - γ (j, 1)) = 0 := by
      rw [map_sub]; exact this
    exact (residue_eq_zero_iff_dvd hmax _).1 h3
  · intro γ' hγ' j hj h hh
    have h1 : (Bmat p v u ξ κ h) *ᵥ (fun i : Fin κ => γ' (i, h)) = vec h := by
      funext l
      rw [← Bop_mulVec v u ξ κ γ' h l]
      exact hγ' l l.2 h hh
    have h2 : (fun i : Fin κ => γ' (i, h)) = (Bmat p v u ξ κ h)⁻¹ *ᵥ vec h := by
      rw [← h1, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (hunit h hh), Matrix.one_mulVec]
    have := congrFun h2 ⟨j, hj⟩
    rw [← hγvec h] at h2
    exact congrFun h2 ⟨j, hj⟩

variable (p) in
/-- `y = Q⁻¹ ẽ` on the nodes of `K` (`Z ẽ = p³ y`), `ẽ = e ∘ cell`; zero off `K`. -/
noncomputable def Ysol (v u : ℤ) (hv : v ≠ 0) (hu : u ≠ 0) (ξ : R) (κ : ℕ) (e : ℕ × ℕ → R) : ℕ → R :=
  fun t => if h : t < κ * p then
    ((Qmat p v u hv hu ξ κ)⁻¹ *ᵥ (fun i : Fin (κ * p) => e (cell p i))) ⟨t, h⟩ else 0

/-- **Lemma 3 (c)**: the sweep inverse.  Let `e` be a function on the cells with `e(j,0) ≡ e(j,1)`, and
`γ = 𝐁⁻¹ e` (part (b)).  With `y = Q⁻¹ ẽ` (`Ysol`; `Z ẽ = p³ y`):
`Q y = ẽ` on `K`; `y ≡ γ̃ (mod p²)` on `K`, that is `Z ẽ ≡ p³ γ̃ (mod p⁵)`; and for every node `n < N`
(so for `n ∉ K` too) `p³ H(n, K) Z ẽ = (Q y)(n) ≡ (𝐁 γ)(cell n) (mod p²)`. -/
theorem sweep_inverse (hmax : IsLocalRing.maximalIdeal R = Ideal.span {(p : R)}) (hp5 : 5 ≤ p)
    (hN : 2 * N < p * p) {κ : ℕ} (hκN : κ * p ≤ N) (ξ : R)
    (hB : (Bbar p v u ξ κ).det ≠ 0) (e : ℕ × ℕ → R)
    (he : ∀ j < κ, (p : R) ∣ e (j, 0) - e (j, 1)) :
    ∃ γ : ℕ × ℕ → R, (∀ j < κ, (p : R) ∣ γ (j, 0) - γ (j, 1)) ∧
      (∀ l < κ, ∀ h ≤ 1, Bop (p := p) v u ξ κ γ (l, h) = e (l, h)) ∧
      (∀ n < κ * p, ∑ t ∈ range (κ * p), Qent (p := p) v u hv hu ξ n t *
          Ysol p v u hv hu ξ κ e t = e (cell p n)) ∧
      (∀ t < κ * p, (p : R) ^ 2 ∣ Ysol p v u hv hu ξ κ e t - γ (cell p t)) ∧
      (∀ n < N, (p : R) ^ 2 ∣ (∑ t ∈ range (κ * p), Qent (p := p) v u hv hu ξ n t *
          Ysol p v u hv hu ξ κ e t) - Bop (p := p) v u ξ κ γ (cell p n)) := by
  have hp0 : 0 < p := hp.out.pos
  have hodd := odd_of_ge5 hp5
  obtain ⟨γ, hγV, hBγ, -⟩ := Bop_bijective v u hmax hp5 hN hκN ξ hB e he
  have hQ := isUnit_det_Qmat v u hv hu hmax hp5 hN hκN ξ hB
  set Q := Qmat p v u hv hu ξ κ with hQdef
  let ey : Fin (κ * p) → R := fun i => e (cell p i)
  let w : Fin (κ * p) → R := fun i => γ (cell p i)
  let y : Fin (κ * p) → R := Q⁻¹ *ᵥ ey
  have hYs : ∀ t (ht : t < κ * p), Ysol p v u hv hu ξ κ e t = y ⟨t, ht⟩ := by
    intro t ht; simp [Ysol, y, ey, ht, hQdef]
  have hsumF : ∀ (n : ℕ) (z : ℕ → R) (z' : Fin (κ * p) → R),
      (∀ t (ht : t < κ * p), z t = z' ⟨t, ht⟩) →
      ∑ t ∈ range (κ * p), Qent (p := p) v u hv hu ξ n t * z t =
        ∑ t : Fin (κ * p), Qent (p := p) v u hv hu ξ n t * z' t := by
    intro n z z' hz
    rw [Finset.sum_range]
    exact Finset.sum_congr rfl fun t _ => by rw [hz t t.2]
  -- the exact equation
  have hQy : Q *ᵥ y = ey := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hQ, Matrix.one_mulVec]
  -- cell action for `γ`
  have hCA : ∀ n < N, (p : R) ^ 2 ∣ (∑ t ∈ range (κ * p), Qent (p := p) v u hv hu ξ n t * γ (cell p t)) -
      Bop (p := p) v u ξ κ γ (cell p n) := fun n hn =>
    cell_action v u hv hu hodd hp5 hN hκN ξ γ hγV n hn
  have hBn : ∀ n (hn : n < κ * p), Bop (p := p) v u ξ κ γ (cell p n) = e (cell p n) := by
    intro n hn
    have hnl : n / p < κ := (Nat.div_lt_iff_lt_mul hp0).2 hn
    have hh : half p n ≤ 1 := by rcases half_eq (p := p) n with h | h <;> omega
    exact hBγ (n / p) hnl (half p n) hh
  -- `Q w ≡ ey`
  have hQw : ∀ i : Fin (κ * p), (p : R) ^ 2 ∣ (ey - Q *ᵥ w) i := by
    intro i
    have h1 := hCA i (lt_of_lt_of_le i.2 hκN)
    rw [hBn i i.2, hsumF i (fun t => γ (cell p t)) w (fun t ht => rfl), ← dvd_neg, neg_sub] at h1
    simpa [Matrix.mulVec, dotProduct, Q, Qmat, ey, w] using h1
  have hyw : ∀ i : Fin (κ * p), (p : R) ^ 2 ∣ (y - w) i := by
    intro i
    have : y - w = Q⁻¹ *ᵥ (ey - Q *ᵥ w) := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hQ, Matrix.one_mulVec]
    rw [this]
    show (p : R) ^ 2 ∣ ∑ t, Q⁻¹ i t * (ey - Q *ᵥ w) t
    exact Finset.dvd_sum fun t _ => (hQw t).mul_left _
  refine ⟨γ, hγV, hBγ, ?_, ?_, ?_⟩
  · intro n hn
    rw [hsumF n _ y (fun t ht => hYs t ht)]
    have := congrFun hQy ⟨n, hn⟩
    simpa [Matrix.mulVec, dotProduct, Q, Qmat, ey] using this
  · intro t ht
    rw [hYs t ht]
    simpa [w] using hyw ⟨t, ht⟩
  · intro n hn
    have h1 := hCA n hn
    have h2 : (∑ t ∈ range (κ * p), Qent (p := p) v u hv hu ξ n t * Ysol p v u hv hu ξ κ e t) -
        (∑ t ∈ range (κ * p), Qent (p := p) v u hv hu ξ n t * γ (cell p t)) =
        ∑ t ∈ range (κ * p), Qent (p := p) v u hv hu ξ n t *
          (Ysol p v u hv hu ξ κ e t - γ (cell p t)) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun t _ => by ring
    have h3 : (p : R) ^ 2 ∣ ∑ t ∈ range (κ * p), Qent (p := p) v u hv hu ξ n t *
          (Ysol p v u hv hu ξ κ e t - γ (cell p t)) := by
      refine Finset.dvd_sum fun t ht => ?_
      have htl := Finset.mem_range.1 ht
      rw [hYs t htl]
      exact (by simpa [w] using hyw ⟨t, htl⟩ : (p : R) ^ 2 ∣ y ⟨t, htl⟩ - γ (cell p t)).mul_left _
    have e1 : (∑ t ∈ range (κ * p), Qent (p := p) v u hv hu ξ n t * Ysol p v u hv hu ξ κ e t) -
        Bop (p := p) v u ξ κ γ (cell p n) =
        ((∑ t ∈ range (κ * p), Qent (p := p) v u hv hu ξ n t * Ysol p v u hv hu ξ κ e t) -
          (∑ t ∈ range (κ * p), Qent (p := p) v u hv hu ξ n t * γ (cell p t))) +
        ((∑ t ∈ range (κ * p), Qent (p := p) v u hv hu ξ n t * γ (cell p t)) -
          Bop (p := p) v u ξ κ γ (cell p n)) := by ring
    rw [e1, h2]
    exact dvd_add h3 h1

end Inverse

end CatalanCore.Uniform.Content.Sweep

#print axioms CatalanCore.Uniform.Content.Sweep.res_Qmat
#print axioms CatalanCore.Uniform.Content.Sweep.isUnit_det_Qmat
#print axioms CatalanCore.Uniform.Content.Sweep.Bop_bijective
#print axioms CatalanCore.Uniform.Content.Sweep.sweep_inverse
