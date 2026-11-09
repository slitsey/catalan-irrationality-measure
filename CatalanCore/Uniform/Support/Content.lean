module

public import CatalanCore.Uniform.Support.Datum
public import CatalanCore.Uniform.Support.SeqFamily
public import CatalanCore.Uniform.Content.BankShared.CrudeDet
public import CatalanCore.Arith.Hybrid.RankGLE

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


/-! ### Finite arbitrary-order integer-pole sums (Q05, Q15)

These arithmetic identities use no balance/top-coefficient hypothesis and do not
impose a pole-order bound. They also support repeated exponent labels.
-/

section PowerSums

variable {α : Type*} [DecidableEq α]

def powerSum (J : Finset α) (ν : α → ℕ) (d : α → ℚ) (t : ℕ) : ℚ :=
  ∑ k ∈ range t, ∑ j ∈ J, d j / ((k : ℚ) + 1) ^ ν j

def powerPolar (p m : ℕ) (J : Finset α) (ν : α → ℕ) (d : α → ℚ) (l : ℕ) : ℚ :=
  ∑ j ∈ J, d j * (p : ℚ) ^ (m - ν j) *
    (∑ k ∈ range l, 1 / ((k : ℚ) + 1) ^ ν j)

def powerRegular (p : ℕ) (J : Finset α) (ν : α → ℕ) (d : α → ℚ) (t : ℕ) : ℚ :=
  ∑ k ∈ range t, if p ∣ k + 1 then 0 else ∑ j ∈ J, d j / ((k : ℚ) + 1) ^ ν j

theorem powerPolar_succ (p m : ℕ) (J : Finset α) (ν : α → ℕ) (d : α → ℚ) (l : ℕ) :
    powerPolar p m J ν d (l + 1) = powerPolar p m J ν d l +
      ∑ j ∈ J, d j * (p : ℚ) ^ (m - ν j) / ((l : ℚ) + 1) ^ ν j := by
  unfold powerPolar
  simp only [Finset.sum_range_succ]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem power_cancel (p m n : ℕ) (hp : p ≠ 0) (hn : n ≤ m) (d l : ℚ) :
    (p : ℚ) ^ m * (d / ((p : ℚ) * l) ^ n) =
      d * (p : ℚ) ^ (m - n) / l ^ n := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp
  have he : (p : ℚ) ^ m = (p : ℚ) ^ (m - n) * (p : ℚ) ^ n := by
    rw [← pow_add, Nat.sub_add_cancel hn]
  rw [he, mul_pow]
  by_cases hl : l = 0
  · subst hl
    by_cases hn0 : n = 0
    · simp [hn0]; ring
    · simp [zero_pow hn0]
  · field_simp

theorem powerSum_split (p m : ℕ) (hp : p ≠ 0) (J : Finset α)
    (ν : α → ℕ) (d : α → ℚ) (hν : ∀ j ∈ J, ν j ≤ m) (t : ℕ) :
    (p : ℚ) ^ m * powerSum J ν d t = powerPolar p m J ν d (t / p) +
      (p : ℚ) ^ m * powerRegular p J ν d t := by
  induction t with
  | zero => simp [powerSum, powerPolar, powerRegular]
  | succ t ih =>
    have hsum : powerSum J ν d (t + 1) = powerSum J ν d t +
        ∑ j ∈ J, d j / ((t : ℚ) + 1) ^ ν j := by simp [powerSum, Finset.sum_range_succ]
    have hreg : powerRegular p J ν d (t + 1) = powerRegular p J ν d t +
        (if p ∣ t + 1 then 0 else ∑ j ∈ J, d j / ((t : ℚ) + 1) ^ ν j) := by
      simp [powerRegular, Finset.sum_range_succ]
    rw [hsum, hreg, mul_add, mul_add, ih]
    by_cases hd : p ∣ t + 1
    · rw [Nat.succ_div_of_dvd hd, powerPolar_succ]
      have ht : t + 1 = p * (t / p + 1) := by
        rw [← Nat.succ_div_of_dvd hd]
        exact (Nat.mul_div_cancel' hd).symm
      have htq : (t : ℚ) + 1 = (p : ℚ) * ((t / p : ℕ) + 1) := by exact_mod_cast ht
      have hinc : (p : ℚ) ^ m * (∑ j ∈ J, d j / ((t : ℚ) + 1) ^ ν j) =
          ∑ j ∈ J, d j * (p : ℚ) ^ (m - ν j) / (((t / p : ℕ) : ℚ) + 1) ^ ν j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [htq]
        exact power_cancel p m (ν j) hp (hν j hj) (d j) _
      rw [hinc]
      simp [hd]
      ring
    · rw [Nat.succ_div_of_not_dvd hd]
      simp [hd]
      ring

variable {p : ℕ} [hp : Fact p.Prime]

theorem powerRegular_mem (J : Finset α) (ν : α → ℕ) (d : α → ℚ)
    (hd : ∀ j ∈ J, d j ∈ LocRing p) (t : ℕ) :
    powerRegular p J ν d t ∈ LocRing p := by
  apply (LocRing p).sum_mem
  intro k _
  by_cases hk : p ∣ k + 1
  · simp only [powerRegular, hk, if_true]
    exact (LocRing p).zero_mem
  · simp only [hk, if_false]
    apply (LocRing p).sum_mem
    intro j hj
    rw [div_eq_mul_inv, ← inv_pow]
    have hkq : (((k : ℚ) + 1)⁻¹) ∈ LocRing p := by
      simpa only [Nat.cast_add, Nat.cast_one] using inv_natCast_mem_locRing hk
    exact (LocRing p).mul_mem (hd j hj) ((LocRing p).pow_mem hkq _)

theorem powerPolar_mem (m : ℕ) (J : Finset α) (ν : α → ℕ) (d : α → ℚ)
    (hd : ∀ j ∈ J, d j ∈ LocRing p) {l : ℕ} (hl : l < p) :
    powerPolar p m J ν d l ∈ LocRing p := by
  apply (LocRing p).sum_mem
  intro j hj
  apply (LocRing p).mul_mem
  · exact (LocRing p).mul_mem (hd j hj)
      ((LocRing p).pow_mem (by exact_mod_cast int_mem_locRing (ℓ := p) (p : ℤ)) _)
  · apply (LocRing p).sum_mem
    intro k hk
    have hk0 : 0 < k + 1 := by omega
    have hkp : k + 1 < p := by have := mem_range.mp hk; omega
    have hnd : ¬ p ∣ k + 1 := fun h => by have := Nat.le_of_dvd hk0 h; omega
    have hmem : (((k : ℚ) + 1)⁻¹) ∈ LocRing p := by
      simpa only [Nat.cast_add, Nat.cast_one] using inv_natCast_mem_locRing hnd
    simpa only [one_div, inv_pow] using (LocRing p).pow_mem hmem (ν j)

theorem powerSum_scaled_mem (m : ℕ) (J : Finset α) (ν : α → ℕ) (d : α → ℚ)
    (hν : ∀ j ∈ J, ν j ≤ m) (hd : ∀ j ∈ J, d j ∈ LocRing p)
    {t : ℕ} (ht : t / p < p) : (p : ℚ) ^ m * powerSum J ν d t ∈ LocRing p := by
  rw [powerSum_split p m hp.out.ne_zero J ν d hν t]
  exact (LocRing p).add_mem (powerPolar_mem m J ν d hd ht)
    ((LocRing p).mul_mem ((LocRing p).pow_mem
      (by exact_mod_cast int_mem_locRing (ℓ := p) (p : ℤ)) m) (powerRegular_mem J ν d hd t))

theorem powerSum_sub_same_period_mem (m : ℕ) (J : Finset α) (ν : α → ℕ) (d : α → ℚ)
    (hν : ∀ j ∈ J, ν j ≤ m) (hd : ∀ j ∈ J, d j ∈ LocRing p)
    {s t : ℕ} (hper : s / p = t / p) :
    powerSum J ν d t - powerSum J ν d s ∈ LocRing p := by
  have hs := powerSum_split p m hp.out.ne_zero J ν d hν s
  have ht := powerSum_split p m hp.out.ne_zero J ν d hν t
  rw [hper] at hs
  have he : powerSum J ν d t - powerSum J ν d s =
      powerRegular p J ν d t - powerRegular p J ν d s := by
    apply mul_left_cancel₀ (pow_ne_zero m (by exact_mod_cast hp.out.ne_zero : (p : ℚ) ≠ 0))
    linear_combination ht - hs
  rw [he]
  exact (LocRing p).sub_mem (powerRegular_mem J ν d hd t) (powerRegular_mem J ν d hd s)

end PowerSums


/-! ### The arbitrary-order single-pole assignment table -/

section IntegerPole

variable {p : ℕ} [hp : Fact p.Prime]

theorem hpoleF_scaled_mem (h : ℕ) (d : ℕ → ℚ)
    (hd : ∀ j ∈ Icc 1 (h - 1), d j ∈ LocRing p) {t : ℕ} (ht : t < p * p) :
    (p : ℚ) ^ (h - 1) * hpoleF h d t ∈ LocRing p := by
  exact powerSum_scaled_mem (h - 1) (Icc 1 (h - 1)) id d
    (fun j hj => (mem_Icc.mp hj).2) hd
    ((Nat.div_lt_iff_lt_mul hp.out.pos).mpr ht)

theorem hpoleE_scaled_mem (h : ℕ) (hh : 2 ≤ h) (d : ℕ → ℚ)
    (hd : ∀ j ∈ Icc 1 (h - 1), d j ∈ LocRing p) {t : ℕ} (ht : t < p * p) :
    (p : ℚ) ^ h * hpoleE h d t ∈ LocRing p := by
  apply powerSum_scaled_mem h (Icc 1 (h - 1)) (fun j => j + 1) (fun j => (j : ℚ) * d j)
  · intro j hj; have := (mem_Icc.mp hj).2; omega
  · intro j hj
    exact (LocRing p).mul_mem (by exact_mod_cast int_mem_locRing (ℓ := p) (j : ℤ)) (hd j hj)
  · exact (Nat.div_lt_iff_lt_mul hp.out.pos).mpr ht

theorem hpoleF_sub_period_mem (h : ℕ) (d : ℕ → ℚ)
    (hd : ∀ j ∈ Icc 1 (h - 1), d j ∈ LocRing p)
    {s t : ℕ} (hper : s / p = t / p) : hpoleF h d t - hpoleF h d s ∈ LocRing p :=
  powerSum_sub_same_period_mem (h - 1) (Icc 1 (h - 1)) id d
    (fun j hj => (mem_Icc.mp hj).2) hd hper

theorem hpoleE_first_period_mem (h : ℕ) (hh : 2 ≤ h) (d : ℕ → ℚ)
    (hd : ∀ j ∈ Icc 1 (h - 1), d j ∈ LocRing p) {t : ℕ} (ht : t < p) :
    hpoleE h d t ∈ LocRing p := by
  have hd' : ∀ j ∈ Icc 1 (h - 1), (j : ℚ) * d j ∈ LocRing p := fun j hj =>
    (LocRing p).mul_mem (by exact_mod_cast int_mem_locRing (ℓ := p) (j : ℤ)) (hd j hj)
  have he := powerSum_sub_same_period_mem h (Icc 1 (h - 1)) (fun j => j + 1)
    (fun j => (j : ℚ) * d j) (fun j hj => by have := (mem_Icc.mp hj).2; omega) hd'
    (s := 0) (t := t) (by rw [Nat.zero_div, Nat.div_eq_of_lt ht])
  simpa only [hpoleE, powerSum, Finset.range_zero, Finset.sum_empty, sub_zero] using he

/-- The four-valued assignment majorant, including the integral first-period diagonal. -/
def hpoleWeight (h p s t : ℕ) : ℕ :=
  if s = t then (if p ≤ s then h else 0)
  else if s / p = t / p then 0
  else if s % p = t % p then h else h - 1

theorem hpoleWeight_symm (h p s t : ℕ) : hpoleWeight h p s t = hpoleWeight h p t s := by
  by_cases he : s = t
  · subst he; rfl
  · simp only [hpoleWeight, he, Ne.symm he, if_false]
    simp only [eq_comm]

theorem lw_symm (f g : ℕ → ℚ) (s t : ℕ) : lw f g s t = lw f g t s := by
  by_cases he : s = t
  · subst he; rfl
  · simp only [lw, he, Ne.symm he, if_false]
    have he1 : f s - f t = -(f t - f s) := by ring
    have he2 : (s : ℚ) - t = -((t : ℚ) - s) := by ring
    rw [he1, he2, neg_div_neg_eq]

theorem hpole_weight_table (h : ℕ) (hh : 2 ≤ h) (d : ℕ → ℚ)
    (hd : ∀ j ∈ Icc 1 (h - 1), d j ∈ LocRing p)
    (s t : ℕ) (hs : s < p * p) (ht : t < p * p) :
    (p : ℚ) ^ hpoleWeight h p s t * lw (hpoleF h d) (hpoleE h d) s t ∈ LocRing p := by
  have hp0 : 0 < p := hp.out.pos
  have off : ∀ s t : ℕ, s < t → s < p * p → t < p * p →
      (p : ℚ) ^ hpoleWeight h p s t * lw (hpoleF h d) (hpoleE h d) s t ∈ LocRing p := by
    intro s t hst hs ht
    have hne := hst.ne
    have he : ((t : ℚ) - s) = ((t - s : ℕ) : ℚ) := by rw [Nat.cast_sub hst.le]
    rw [lw, if_neg hne, he]
    by_cases hper : s / p = t / p
    · have hlt : t - s < p := by
        have h1 := Nat.div_add_mod s p
        have h2 := Nat.div_add_mod t p
        rw [hper] at h1
        have := Nat.mod_lt s hp0
        have := Nat.mod_lt t hp0
        omega
      have hnd : ¬ p ∣ t - s := fun h => by have := Nat.le_of_dvd (by omega : 0 < t - s) h; omega
      simp only [hpoleWeight, hne, if_false, hper, if_true, pow_zero, one_mul]
      rw [div_eq_mul_inv]
      exact (LocRing p).mul_mem (hpoleF_sub_period_mem h d hd hper) (inv_natCast_mem_locRing hnd)
    · have hf := (LocRing p).sub_mem (hpoleF_scaled_mem h d hd ht) (hpoleF_scaled_mem h d hd hs)
      have hf' : (p : ℚ) ^ (h - 1) * (hpoleF h d t - hpoleF h d s) ∈ LocRing p := by
        simpa only [mul_sub] using hf
      by_cases hm : s % p = t % p
      · simp only [hpoleWeight, hne, if_false, hper, hm, if_true]
        have hdm := p_div_mem (p := p) (t - s) (by omega) (by omega)
        have heq : (p : ℚ) ^ h * ((hpoleF h d t - hpoleF h d s) / ((t - s : ℕ) : ℚ)) =
            ((p : ℚ) ^ (h - 1) * (hpoleF h d t - hpoleF h d s)) *
              ((p : ℚ) * (1 / ((t - s : ℕ) : ℚ))) := by
          have hh1 : h - 1 + 1 = h := by omega
          have hpwh : (p : ℚ) ^ h = (p : ℚ) ^ (h - 1) * p := by
            rw [← pow_succ, hh1]
          rw [hpwh]
          ring
        rw [heq]
        exact (LocRing p).mul_mem hf' hdm
      · simp only [hpoleWeight, hne, if_false, hper, hm]
        have hnd : ¬ p ∣ t - s := fun h => hm ((Nat.modEq_iff_dvd' hst.le).mpr h)
        have heq : (p : ℚ) ^ (h - 1) * ((hpoleF h d t - hpoleF h d s) / ((t - s : ℕ) : ℚ)) =
            ((p : ℚ) ^ (h - 1) * (hpoleF h d t - hpoleF h d s)) * (((t - s : ℕ) : ℚ)⁻¹) := by ring
        rw [heq]
        exact (LocRing p).mul_mem hf' (inv_natCast_mem_locRing hnd)
  by_cases he : s = t
  · subst he
    simp only [hpoleWeight, if_true, lw]
    by_cases hps : p ≤ s
    · rw [if_pos hps, mul_neg]
      exact (LocRing p).neg_mem (hpoleE_scaled_mem h hh d hd hs)
    · rw [if_neg hps, pow_zero, one_mul]
      exact (LocRing p).neg_mem (hpoleE_first_period_mem h hh d hd (by omega))
  · rcases lt_or_gt_of_ne he with hst | hts
    · exact off s t hst hs ht
    · rw [hpoleWeight_symm h p s t, lw_symm (hpoleF h d) (hpoleE h d) s t]
      exact off t s hts ht hs

theorem coefficient_mem_of_den_dvd {M : ℕ} (q : ℚ) (hden : q.den ∣ M) (hpM : ¬ p ∣ M) :
    q ∈ LocRing p := by
  rw [mem_locRing]
  exact fun h => hpM (dvd_trans h hden)

end IntegerPole

/-! The polynomial determinant bridge is sequence-generic; source arithmetic only
supplies the entry exponents. Common-node injectivity is not used here. -/

section SequenceDual

variable {p : ℕ} [Fact p.Prime] {ι κ : Type}
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem seqFullN_entry_gle (f g : ℕ → ℚ) (cn : ι → ℕ) (xs ys : κ → ℕ)
    (e : (ι ⊕ κ) → (ι ⊕ κ) → ℕ)
    (hval : ∀ a b, (p : ℚ) ^ e a b * lw f g (Sum.elim cn xs a) (Sum.elim cn ys b) ∈ LocRing p)
    (a b : ι ⊕ κ) : GLE p (e a b) (seqFullN f g cn xs ys (X : ℚ[X]) a b) := by
  have key := fun a b => GLE.C_iff.mpr (hval a b)
  rcases a with a | i <;> rcases b with b | j
  · simp only [seqFullN, Rect.Blk, Matrix.fromBlocks_apply₁₁, Matrix.add_apply, Matrix.smul_apply,
      Matrix.one_apply, Matrix.of_apply, smul_eq_mul, Polynomial.algebraMap_eq]
    by_cases h : a = b
    · subst h
      simp only [if_true, mul_one]
      exact (key (Sum.inl a) (Sum.inl a)).add (GLE.X.mono (Nat.zero_le _))
    · simp only [h, if_false, mul_zero, add_zero]
      exact key (Sum.inl a) (Sum.inl b)
  · simp only [seqFullN, Rect.Blk, Matrix.fromBlocks_apply₁₂, Matrix.of_apply, Polynomial.algebraMap_eq]
    exact key (Sum.inl a) (Sum.inr j)
  · simp only [seqFullN, Rect.Blk, Matrix.fromBlocks_apply₂₁, Matrix.of_apply, Polynomial.algebraMap_eq]
    exact key (Sum.inr i) (Sum.inl b)
  · simp only [seqFullN, Rect.Blk, Matrix.fromBlocks_apply₂₂, Matrix.of_apply, Polynomial.algebraMap_eq]
    exact key (Sum.inr i) (Sum.inr j)

theorem seqFullN_det_gle_of_dual (f g : ℕ → ℚ) (cn : ι → ℕ) (xs ys : κ → ℕ)
    (e : (ι ⊕ κ) → (ι ⊕ κ) → ℕ)
    (hval : ∀ a b, (p : ℚ) ^ e a b * lw f g (Sum.elim cn xs a) (Sum.elim cn ys b) ∈ LocRing p)
    (ur uc : (ι ⊕ κ) → ℕ) (he : ∀ a b, e a b ≤ ur a + uc b) :
    GLE p (∑ a, ur a + ∑ b, uc b) (seqFullN f g cn xs ys (X : ℚ[X])).det := by
  have h := det_gle (p := p) (seqFullN f g cn xs ys (X : ℚ[X])) e
    (seqFullN_entry_gle f g cn xs ys e hval)
  refine h.mono ?_
  refine tropVal_le_of_dual e (fun a => (ur a : ℚ)) (fun b => (uc b : ℚ)) ?_ ?_
  · intro a b; exact_mod_cast he a b
  · push_cast; exact le_rfl

end SequenceDual

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

#print axioms CatalanCore.Uniform.Support.powerSum_split
#print axioms CatalanCore.Uniform.Support.hpole_weight_table
#print axioms CatalanCore.Uniform.Support.seqFullN_det_gle_of_dual
