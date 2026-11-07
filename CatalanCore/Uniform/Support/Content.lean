module

public import CatalanCore.Uniform.Support.Datum
public import CatalanCore.Uniform.Support.SeqFamily
public import CatalanCore.Uniform.Content.BankShared.CrudeDet

@[expose] public section

/-!
# No bad primes on plane 2 (lane H, wave H2; ledger S11)

**Lemma 4.2.**  Let `(v, u)` be integers, `v ≠ 0 ≠ u`, and take the datum `a₁ = u, a_½ = -u, b₁ = v`
(`Datum.plane2 v u`).  Every row of the plane 2 table is valid for this datum at every prime `p` with
`p² > 2N + 2p`, including those dividing `v`.

* For `p ∤ v` the matrix is `v` times that of `b = u/v` (`seqFullN_smul_eval`: scaling the pair `(f, g)`
  and the variable by `c` scales the matrix, so the determinant by `c^n`), so the rows hold for the integer
  datum exactly as for `b`, and primes dividing `den b` never enter.
* For `p ∣ v`, the table rows are lower bounds on valuations of integer-weighted poles and hold as before;
  for the two rows `E₁`, `E₂` (`Sweep.RowE1`, `Sweep.RowE2`) the double-pole term `v/(z+1)²` has
  valuation at least `-1`, so every `f` has valuation at least `-1`, every entry at least `-2`:
  `plane2_entry_gle`.  Hence every coefficient of every member has `v_p(den) ≤ 2 (r + m)`
  (`plane2_member_gle`), which is at most `E₁ = 3r + τ₃` as `r ≥ 2m`, and at most
  `E₂ = 4r - 2p + 2m + τ₂` on `p ≤ r` (`bad_prime_rows`).

The statements are generic in `(v, u)` and in the nodes; `N` is only the bound on the node set.
-/

open Polynomial Finset Matrix CatalanCore.Basic CatalanCore.Arith.Hybrid

namespace CatalanCore.Uniform.Support

/-! ### Scaling -/

theorem lw_smul (c : ℚ) (f g : ℕ → ℚ) (a b : ℕ) :
    lw (fun t => c * f t) (fun t => c * g t) a b = c * lw f g a b := by
  unfold lw
  split_ifs
  · ring
  · ring

/-- Scaling `(f, g)` and the variable by `c` scales the matrix by `c`. -/
theorem seqFullN_smul_eval {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (c : ℚ) (f g : ℕ → ℚ) (cn : ι → ℕ) (xs ys : κ → ℕ) (x : ℚ) :
    seqFullN (fun t => c * f t) (fun t => c * g t) cn xs ys (c * x) =
      c • seqFullN f g cn xs ys x := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [seqFullN, Rect.Blk, Matrix.fromBlocks, Matrix.one_apply, lw_smul]
  by_cases h : a = b <;> simp [h] <;> try ring

/-- `P_int(x) = c^n P(x / c)`: the determinant of the scaled matrix. -/
theorem det_seqFullN_smul_eval {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (c : ℚ) (f g : ℕ → ℚ) (cn : ι → ℕ) (xs ys : κ → ℕ) (x : ℚ) :
    (seqFullN (fun t => c * f t) (fun t => c * g t) cn xs ys (c * x)).det =
      c ^ (Fintype.card ι + Fintype.card κ) * (seqFullN f g cn xs ys x).det := by
  rw [seqFullN_smul_eval, Matrix.det_smul]
  simp

/-! ### Inverse of an integer below `p²` -/

section PAdic

variable {p : ℕ} [hp : Fact p.Prime]

/-- `p / n` is `p`-integral for `0 < n < p²`: every integer below `p²` has `p`-valuation at most `1`. -/
theorem p_div_mem (n : ℕ) (hn : 0 < n) (hnp : n < p * p) :
    (p : ℚ) * (1 / (n : ℚ)) ∈ LocRing p := by
  have h1 : (p : ℚ) ^ (Nat.log p n) * (1 / (n : ℚ)) ∈ LocRing p :=
    Content.BankShared.pow_mul_inv_mem hn le_rfl
  have hlog : Nat.log p n ≤ 1 := by
    have : Nat.log p n < 2 := Nat.log_lt_of_lt_pow hn.ne' (by rw [pow_two]; exact hnp)
    omega
  have := Content.BankShared.mem_of_le (p := p) hlog h1
  simpa using this

theorem p_div_mem_int (m : ℤ) (n : ℕ) (hn : 0 < n) (hnp : n < p * p) :
    (p : ℚ) * ((m : ℚ) / (n : ℚ)) ∈ LocRing p := by
  have := (LocRing p).mul_mem (int_mem_locRing (ℓ := p) m) (p_div_mem (p := p) n hn hnp)
  convert this using 1
  ring

end PAdic

/-! ### Entries of the plane 2 matrix at a prime dividing `v` -/

section Plane2

variable (v u : ℤ) (hv : v ≠ 0) (hu : u ≠ 0)

theorem plane2_delta (x : ℚ) :
    (Datum.plane2 v u hv hu).delta x = u / (x + 1) - v / (x + 1) ^ 2 - u / (x + 1 / 2) := by
  simp [Datum.delta, Fin.sum_univ_two, Datum.plane2]
  try ring

theorem plane2_delta1 (x : ℚ) :
    (Datum.plane2 v u hv hu).delta1 x =
      -u / (x + 1) ^ 2 + 2 * v / (x + 1) ^ 3 + u / (x + 1 / 2) ^ 2 := by
  simp [Datum.delta1, Fin.sum_univ_two, Datum.plane2]
  try ring

variable {p : ℕ} [hp : Fact p.Prime]

/-- With `p ∣ v`, `p δ(k)` is `p`-integral as soon as `2k + 1 < p²`. -/
theorem plane2_pdelta_mem (hpv : (p : ℤ) ∣ v) (k : ℕ) (hk : 2 * k + 1 < p * p) :
    (p : ℚ) * (Datum.plane2 v u hv hu).delta k ∈ LocRing p := by
  obtain ⟨v', rfl⟩ := hpv
  have ha := p_div_mem (p := p) (k + 1) (by omega) (by nlinarith)
  have hb := p_div_mem (p := p) (2 * k + 1) (by omega) hk
  have e : (p : ℚ) * (Datum.plane2 (p * v') u hv hu).delta k =
      (u : ℚ) * ((p : ℚ) * (1 / ((k + 1 : ℕ) : ℚ))) -
      (v' : ℚ) * ((p : ℚ) * (1 / ((k + 1 : ℕ) : ℚ))) ^ 2 -
      2 * (u : ℚ) * ((p : ℚ) * (1 / ((2 * k + 1 : ℕ) : ℚ))) := by
    rw [plane2_delta]
    have h1 : ((k : ℚ) + 1) ≠ 0 := by positivity
    have h2 : ((k : ℚ) + 1 / 2) ≠ 0 := by positivity
    have h3 : (2 * (k : ℚ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
    try ring
  rw [e]
  refine (LocRing p).sub_mem ((LocRing p).sub_mem ?_ ?_) ?_
  · exact (LocRing p).mul_mem (int_mem_locRing u) ha
  · exact (LocRing p).mul_mem (int_mem_locRing v') ((LocRing p).pow_mem ha 2)
  · exact (LocRing p).mul_mem
      ((LocRing p).mul_mem (by exact_mod_cast int_mem_locRing (ℓ := p) 2) (int_mem_locRing u)) hb

/-- With `p ∣ v`, `p² δ′(k)` is `p`-integral as soon as `2k + 1 < p²`. -/
theorem plane2_p2delta1_mem (hpv : (p : ℤ) ∣ v) (k : ℕ) (hk : 2 * k + 1 < p * p) :
    (p : ℚ) ^ 2 * (Datum.plane2 v u hv hu).delta1 k ∈ LocRing p := by
  obtain ⟨v', rfl⟩ := hpv
  have ha := p_div_mem (p := p) (k + 1) (by omega) (by nlinarith)
  have hb := p_div_mem (p := p) (2 * k + 1) (by omega) hk
  have e : (p : ℚ) ^ 2 * (Datum.plane2 (p * v') u hv hu).delta1 k =
      -(u : ℚ) * ((p : ℚ) * (1 / ((k + 1 : ℕ) : ℚ))) ^ 2 +
      2 * (v' : ℚ) * ((p : ℚ) * (1 / ((k + 1 : ℕ) : ℚ))) ^ 3 +
      4 * (u : ℚ) * ((p : ℚ) * (1 / ((2 * k + 1 : ℕ) : ℚ))) ^ 2 := by
    rw [plane2_delta1]
    have h1 : ((k : ℚ) + 1) ≠ 0 := by positivity
    have h2 : ((k : ℚ) + 1 / 2) ≠ 0 := by positivity
    have h3 : (2 * (k : ℚ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
    try ring
  rw [e]
  refine (LocRing p).add_mem ((LocRing p).add_mem ?_ ?_) ?_
  · exact (LocRing p).mul_mem (by exact_mod_cast int_mem_locRing (ℓ := p) (-u)) ((LocRing p).pow_mem ha 2)
  · exact (LocRing p).mul_mem
      ((LocRing p).mul_mem (by exact_mod_cast int_mem_locRing (ℓ := p) 2) (int_mem_locRing v'))
      ((LocRing p).pow_mem ha 3)
  · exact (LocRing p).mul_mem
      ((LocRing p).mul_mem (by exact_mod_cast int_mem_locRing (ℓ := p) 4) (int_mem_locRing u))
      ((LocRing p).pow_mem hb 2)

theorem plane2_pf_mem (hpv : (p : ℤ) ∣ v) {N : ℕ} (hN : 2 * N + 2 * p < p * p) (t : ℕ) (ht : t < N) :
    (p : ℚ) * (Datum.plane2 v u hv hu).f t ∈ LocRing p := by
  unfold Datum.f
  rw [Finset.mul_sum]
  refine (LocRing p).sum_mem fun k hk => ?_
  have := Finset.mem_range.1 hk
  exact plane2_pdelta_mem v u hv hu hpv k (by omega)

theorem plane2_p2e_mem (hpv : (p : ℤ) ∣ v) {N : ℕ} (hN : 2 * N + 2 * p < p * p) (t : ℕ) (ht : t < N) :
    (p : ℚ) ^ 2 * (Datum.plane2 v u hv hu).e t ∈ LocRing p := by
  unfold Datum.e
  have e : (p : ℚ) ^ 2 * (-∑ k ∈ Finset.range t, (Datum.plane2 v u hv hu).delta1 k) =
      -∑ k ∈ Finset.range t, ((p : ℚ) ^ 2 * (Datum.plane2 v u hv hu).delta1 k) := by
    rw [mul_neg, Finset.mul_sum]
  rw [e]
  refine (LocRing p).neg_mem ((LocRing p).sum_mem fun k hk => ?_)
  have := Finset.mem_range.1 hk
  exact plane2_p2delta1_mem v u hv hu hpv k (by omega)

/-- **Every entry of the plane 2 matrix has `p`-valuation at least `-2` when `p ∣ v`.** -/
theorem plane2_lw_mem (hpv : (p : ℤ) ∣ v) {N : ℕ} (hN : 2 * N + 2 * p < p * p) (a b : ℕ)
    (ha : a < N) (hb : b < N) :
    (p : ℚ) ^ 2 * lw (Datum.plane2 v u hv hu).f (Datum.plane2 v u hv hu).e a b ∈ LocRing p := by
  unfold lw
  split_ifs with hab
  · subst hab
    have h := plane2_p2e_mem v u hv hu hpv hN a ha
    have e : (p : ℚ) ^ 2 * -(Datum.plane2 v u hv hu).e a = -((p : ℚ) ^ 2 * (Datum.plane2 v u hv hu).e a) := by
      ring
    rw [e]; exact (LocRing p).neg_mem h
  · -- off the diagonal: the divided difference of `f`
    have key : ∀ x y : ℕ, x < N → y < N → x < y →
        (p : ℚ) ^ 2 * (((Datum.plane2 v u hv hu).f y - (Datum.plane2 v u hv hu).f x) / ((y : ℚ) - x)) ∈
          LocRing p := by
      intro x y hx hy hxy
      have h1 := plane2_pf_mem v u hv hu hpv hN y hy
      have h2 := plane2_pf_mem v u hv hu hpv hN x hx
      have h3 := p_div_mem (p := p) (y - x) (by omega) (by omega)
      have e : (p : ℚ) ^ 2 * (((Datum.plane2 v u hv hu).f y - (Datum.plane2 v u hv hu).f x) / ((y : ℚ) - x)) =
          ((p : ℚ) * (Datum.plane2 v u hv hu).f y - (p : ℚ) * (Datum.plane2 v u hv hu).f x) *
            ((p : ℚ) * (1 / ((y - x : ℕ) : ℚ))) := by
        have hne : (y : ℚ) - x ≠ 0 := by
          have : (x : ℚ) < y := by exact_mod_cast hxy
          linarith
        rw [Nat.cast_sub hxy.le]
        field_simp
      rw [e]
      exact (LocRing p).mul_mem ((LocRing p).sub_mem h1 h2) h3
    rcases Nat.lt_or_gt_of_ne hab with hlt | hgt
    · exact key a b ha hb hlt
    · have := key b a hb ha hgt
      have e : ((Datum.plane2 v u hv hu).f b - (Datum.plane2 v u hv hu).f a) / ((b : ℚ) - a) =
          ((Datum.plane2 v u hv hu).f a - (Datum.plane2 v u hv hu).f b) / ((a : ℚ) - b) := by
        have hne : (a : ℚ) - b ≠ 0 := by
          have : (b : ℚ) < a := by exact_mod_cast hgt
          linarith
        have hne2 : (b : ℚ) - a ≠ 0 := by intro h; apply hne; linarith
        field_simp
        ring
      rw [e]; exact this

/-- Every coefficient of every entry of the plane 2 matrix has `p`-valuation at least `-2`. -/
theorem plane2_entry_gle (hpv : (p : ℤ) ∣ v) {N : ℕ} (hN : 2 * N + 2 * p < p * p)
    {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (cn : ι → ℕ) (xs ys : κ → ℕ) (hc : ∀ a, cn a < N) (hx : ∀ i, xs i < N) (hy : ∀ i, ys i < N)
    (a b : ι ⊕ κ) :
    GLE p 2 (seqFullN (Datum.plane2 v u hv hu).f (Datum.plane2 v u hv hu).e cn xs ys
      (X : ℚ[X]) a b) := by
  have hX : GLE p 2 (X : ℚ[X]) := GLE.X.mono (Nat.zero_le _)
  have hC := fun a b : ℕ => fun (ha : a < N) (hb : b < N) =>
    GLE.C_iff.2 (plane2_lw_mem v u hv hu hpv hN a b ha hb)
  rcases a with a | i <;> rcases b with b | j
  · simp only [seqFullN, Rect.Blk, Matrix.fromBlocks_apply₁₁, Matrix.add_apply, Matrix.smul_apply,
      Matrix.one_apply, Matrix.of_apply, smul_eq_mul, Polynomial.algebraMap_eq]
    by_cases h : a = b
    · simp only [h, if_true, mul_one]
      exact (hC _ _ (hc b) (hc b)).add hX
    · simp only [h, if_false, mul_zero, add_zero]
      exact hC _ _ (hc a) (hc b)
  · simp only [seqFullN, Rect.Blk, Matrix.fromBlocks_apply₁₂, Matrix.of_apply, Polynomial.algebraMap_eq]
    exact hC _ _ (hc a) (hy j)
  · simp only [seqFullN, Rect.Blk, Matrix.fromBlocks_apply₂₁, Matrix.of_apply, Polynomial.algebraMap_eq]
    exact hC _ _ (hx i) (hc b)
  · simp only [seqFullN, Rect.Blk, Matrix.fromBlocks_apply₂₂, Matrix.of_apply, Polynomial.algebraMap_eq]
    exact hC _ _ (hx i) (hy j)

/-- Every coefficient of the determinant is `p^{2 (|ι| + |κ|)}`-integral. -/
theorem plane2_det_gle (hpv : (p : ℤ) ∣ v) {N : ℕ} (hN : 2 * N + 2 * p < p * p)
    {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (cn : ι → ℕ) (xs ys : κ → ℕ) (hc : ∀ a, cn a < N) (hx : ∀ i, xs i < N) (hy : ∀ i, ys i < N) :
    GLE p (2 * (Fintype.card ι + Fintype.card κ))
      (seqFullN (Datum.plane2 v u hv hu).f (Datum.plane2 v u hv hu).e cn xs ys (X : ℚ[X])).det := by
  have h := det_gle (p := p) (seqFullN (Datum.plane2 v u hv hu).f (Datum.plane2 v u hv hu).e cn xs ys
    (X : ℚ[X])) (fun _ _ => 2) (plane2_entry_gle v u hv hu hpv hN cn xs ys hc hx hy)
  rw [Content.BankShared.tropVal_const, Fintype.card_sum] at h
  rw [mul_comm] at h
  exact h

/-- **Plane 2 members at a prime dividing `v`:** every coefficient of every member of the family has
`v_p(den) ≤ 2 (r + m)`, for any geometry whose nodes lie below `N`, `p² > 2N + 2p`. -/
theorem plane2_member_gle (hpv : (p : ℤ) ∣ v) {N : ℕ} (hN : 2 * N + 2 * p < p * p)
    (G : Rect.Geometry) (S : Finset G.C) (hC : ∀ a ∈ G.C, a < N) (hX : ∀ a ∈ G.X', a < N)
    (hY : ∀ a ∈ G.Y', a < N) :
    GLE p (2 * (G.C.card + G.k))
      (seqFullN (Datum.plane2 v u hv hu).f (Datum.plane2 v u hv hu).e
        (fun a : S => ((a.1 : G.C) : ℕ)) G.xs G.ys (X : ℚ[X])).det := by
  have h := plane2_det_gle v u hv hu hpv hN (fun a : S => ((a.1 : G.C) : ℕ)) G.xs G.ys
    (fun a => hC _ a.1.2) (fun i => hX _ (Finset.orderEmbOfFin_mem _ _ i))
    (fun i => hY _ (Finset.orderEmbOfFin_mem _ _ i))
  refine h.mono ?_
  have : Fintype.card S ≤ G.C.card := by simpa using Finset.card_le_univ S
  simp only [Fintype.card_fin]
  omega

end Plane2

/-- The two rows at a prime dividing `v` (arithmetic of Lemma 4.2): `2 (r + m)` is at most
`E₁ = 3 r + τ₃` as `r ≥ 2 m`, and at most `E₂ = 4 r - 2 p + 2 m + τ₂` on `p ≤ r`. -/
theorem bad_prime_rows (r m p t t' : ℕ) (hm : 2 * m ≤ r) (hpr : p ≤ r) :
    2 * (r + m) ≤ 3 * r + t ∧ 2 * (r + m) + 2 * p ≤ 4 * r + 2 * m + t' := by
  omega

end CatalanCore.Uniform.Support

#print axioms CatalanCore.Uniform.Support.plane2_member_gle
#print axioms CatalanCore.Uniform.Support.det_seqFullN_smul_eval
