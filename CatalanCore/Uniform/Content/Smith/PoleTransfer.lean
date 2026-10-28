module

public import CatalanCore.Arith.Hybrid.LemmaE.Harmonic

@[expose] public section

/-!
# Generalised pole transfer modulo `p` (PTg) and the two-term case (PT)

A *frame modulo `p`* is a finite family of terms `i`, with a coefficient `c i ∈ 𝔽_p` and a pole
index `k i ∈ ℕ`, `k i ≤ p` (the first index at which the term has a pole; the harmonic term
`1/j` has `k = p`).  Its prefix is `F(n) = Σ_i c_i Σ_{j=1}^n (j - k_i)⁻¹`.  The Loewner kernel is
`M[u,w] = (F(w) - F(u))/(w - u)`.

* `ptg` (Lemma PTg): if `Σ c_i = 0`, for `u < w < k_i` (all `i`)
  `F(w) - F(u) = -(w - u) Σ_{x<p} Cum(x) · 1/((x-u)(x-w))`,  `Cum(x) = Σ_{k_i ≤ x} c_i`.
  This is the cell form `-Σ_j C_j Σ_{c ∈ [k_(j), k_(j+1))} 1/((c-u)(c-w))` without sorting.
* `pt` (Lemma PT): for the two-term frame `1/j - 1/(j-k)`, `u < w < k ≤ p`:
  `M[u,w] = Σ_{x ∈ [k,p)} 1/((x-u)(x-w))`.
* `pt_diag`: for `p ≥ 5`, `k ≤ p` and every `u`:
  `Σ_{j ≤ u}((j-k)⁻² - j⁻²) - Σ_{x ∈ [k,p)} (x-u)⁻² = H^{(2)}_{k-1}` (independent of `u`),
  so the `U × U` Schur complement after eliminating the level-one block is `(x + H^{(2)}_{k-1})·I`.
-/

open Finset

namespace CatalanCore.Uniform.Content.Smith

variable {p : ℕ} [Fact p.Prime]

section Frame

variable {ι : Type*} [Fintype ι] (k : ι → ℕ) (c : ι → ZMod p)

/-- Prefix of a frame modulo `p`. -/
def modF (n : ℕ) : ZMod p :=
  ∑ i, c i * ∑ j ∈ Icc 1 n, ((j : ZMod p) - (k i : ZMod p))⁻¹

/-- Cumulative coefficient of the poles at or below `x`. -/
def cum (x : ℕ) : ZMod p := ∑ i ∈ univ.filter (fun i => k i ≤ x), c i

end Frame

/-- The Cauchy kernel `1/((x-u)(x-w))`. -/
def cauchyKer (u w x : ℕ) : ZMod p := ((x : ZMod p) - u)⁻¹ * ((x : ZMod p) - w)⁻¹

lemma zmod_sub_ne_zero_of_lt {a b : ℕ} (hab : a < b) (hlt : b - a < p) :
    ((b : ZMod p) - (a : ZMod p)) ≠ 0 := by
  intro h
  have h1 : ((b - a : ℕ) : ZMod p) = 0 := by rw [Nat.cast_sub hab.le]; exact h
  rw [ZMod.natCast_eq_zero_iff] at h1
  exact absurd (Nat.le_of_dvd (by omega) h1) (by omega)

/-- Telescoping of the shift `K → K + 1` of a pole index. -/
lemma tele (K u : ℕ) : ∀ w, u ≤ w →
    ∑ j ∈ Ioc u w, ((j : ZMod p) - (K : ZMod p))⁻¹ -
        ∑ j ∈ Ioc u w, ((j : ZMod p) - ((K + 1 : ℕ) : ZMod p))⁻¹ =
      ((w : ZMod p) - K)⁻¹ - ((u : ZMod p) - K)⁻¹ := by
  intro w hw
  induction w, hw using Nat.le_induction with
  | base => simp
  | succ w hw ih =>
    rw [Finset.sum_Ioc_succ_top hw, Finset.sum_Ioc_succ_top hw]
    have e : (((w + 1 : ℕ) : ZMod p) - ((K + 1 : ℕ) : ZMod p)) = (w : ZMod p) - K := by
      push_cast; ring
    rw [e]
    linear_combination ih

/-- One step of the pole-index shift. -/
lemma pole_step (K u w : ℕ) (huw : u < w) (hwK : w < K) (hKp : K < p) :
    ∑ j ∈ Ioc u w, ((j : ZMod p) - (K : ZMod p))⁻¹ -
        ∑ j ∈ Ioc u w, ((j : ZMod p) - ((K + 1 : ℕ) : ZMod p))⁻¹ =
      -(((w : ZMod p) - (u : ZMod p)) * cauchyKer u w K) := by
  rw [tele K u w huw.le]
  have h1 : (K : ZMod p) - w ≠ 0 := zmod_sub_ne_zero_of_lt hwK (by omega)
  have h2 : (K : ZMod p) - u ≠ 0 := zmod_sub_ne_zero_of_lt (by omega) (by omega)
  have e1 : (w : ZMod p) - K = -((K : ZMod p) - w) := by ring
  have e2 : (u : ZMod p) - K = -((K : ZMod p) - u) := by ring
  have e3 : (w : ZMod p) - u = ((K : ZMod p) - u) - ((K : ZMod p) - w) := by ring
  unfold cauchyKer
  rw [e1, e2, e3, inv_neg, inv_neg]
  generalize (K : ZMod p) - w = a at *
  generalize (K : ZMod p) - u = b at *
  field_simp
  ring

/-- Chain of shifts from pole index `K` to `K'`. -/
lemma pole_chain (K u w : ℕ) (huw : u < w) (hwK : w < K) : ∀ K', K ≤ K' → K' ≤ p →
    ∑ j ∈ Ioc u w, ((j : ZMod p) - (K : ZMod p))⁻¹ -
        ∑ j ∈ Ioc u w, ((j : ZMod p) - (K' : ZMod p))⁻¹ =
      -(((w : ZMod p) - (u : ZMod p)) * ∑ x ∈ Ico K K', cauchyKer u w x) := by
  intro K' hK
  induction K', hK using Nat.le_induction with
  | base => intro _; simp
  | succ K' hK ih =>
    intro hp
    have h := ih (by omega)
    have hs := pole_step (p := p) K' u w huw (by omega) (by omega)
    rw [Finset.sum_Ico_succ_top hK]
    linear_combination h + hs

lemma Icc_eq_Ioc (n : ℕ) : Icc 1 n = Ioc 0 n := by
  ext x; simp only [mem_Icc, mem_Ioc]; omega

/-- **Lemma PTg.** Generalised pole transfer: the Loewner numerator of a balanced frame modulo `p`
below its first pole is a Cauchy sum over the pole cells. -/
theorem ptg {ι : Type*} [Fintype ι] (k : ι → ℕ) (c : ι → ZMod p) (hbal : ∑ i, c i = 0)
    {u w : ℕ} (huw : u < w) (hk : ∀ i, w < k i) (hkp : ∀ i, k i ≤ p) :
    modF k c w - modF k c u =
      -(((w : ZMod p) - (u : ZMod p)) * ∑ x ∈ range p, cum k c x * cauchyKer u w x) := by
  set S0 : ZMod p := ∑ j ∈ Ioc u w, ((j : ZMod p) - (p : ZMod p))⁻¹ with hS0
  have hdiff : ∀ i, ∑ j ∈ Icc 1 w, ((j : ZMod p) - (k i : ZMod p))⁻¹ -
      ∑ j ∈ Icc 1 u, ((j : ZMod p) - (k i : ZMod p))⁻¹ =
      S0 - ((w : ZMod p) - (u : ZMod p)) * ∑ x ∈ Ico (k i) p, cauchyKer u w x := by
    intro i
    rw [Icc_eq_Ioc, Icc_eq_Ioc, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le u) huw.le]
    have h := pole_chain (k i) u w huw (hk i) p (hkp i) le_rfl
    rw [hS0]
    linear_combination h
  have hmod : modF k c w - modF k c u = ∑ i, c i * (S0 - ((w : ZMod p) - (u : ZMod p)) *
      ∑ x ∈ Ico (k i) p, cauchyKer u w x) := by
    unfold modF
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hdiff i]; ring
  rw [hmod]
  have hico : ∀ i, ∑ x ∈ Ico (k i) p, cauchyKer (p := p) u w x =
      ∑ x ∈ range p, if k i ≤ x then cauchyKer (p := p) u w x else 0 := by
    intro i
    rw [← Finset.sum_filter]
    congr 1
    ext x; simp only [mem_Ico, mem_filter, mem_range]; have := hkp i; omega
  have hcs : ∑ i, c i * ∑ x ∈ Ico (k i) p, cauchyKer u w x =
      ∑ x ∈ range p, cum k c x * cauchyKer u w x := by
    simp_rw [hico, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    unfold cum
    rw [Finset.sum_mul, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  rw [← hcs]
  have e1 : ∀ i, c i * (S0 - ((w : ZMod p) - (u : ZMod p)) * ∑ x ∈ Ico (k i) p, cauchyKer u w x) =
      c i * S0 - ((w : ZMod p) - (u : ZMod p)) * (c i * ∑ x ∈ Ico (k i) p, cauchyKer u w x) :=
    fun i => by ring
  rw [Finset.sum_congr rfl (fun i _ => e1 i), Finset.sum_sub_distrib, ← Finset.sum_mul, hbal,
    zero_mul, zero_sub, ← Finset.mul_sum]

/-! ### The two-term frame -/

/-- Prefix of the two-term frame `1/j - 1/(j - k)`. -/
def F2 (k n : ℕ) : ZMod p := ∑ j ∈ Icc 1 n, (((j : ZMod p))⁻¹ - ((j : ZMod p) - (k : ZMod p))⁻¹)

lemma F2_eq_modF (k n : ℕ) :
    F2 (p := p) k n = modF (fun i : Fin 2 => (![p, k] : Fin 2 → ℕ) i)
      (![1, -1] : Fin 2 → ZMod p) n := by
  unfold F2 modF
  rw [Fin.sum_univ_two]
  rw [Finset.sum_sub_distrib]
  simp <;> ring

lemma cum_two {k x : ℕ} (hx : x < p) :
    cum (fun i : Fin 2 => (![p, k] : Fin 2 → ℕ) i) (![1, -1] : Fin 2 → ZMod p) x =
      if k ≤ x then -1 else 0 := by
  unfold cum
  rw [Finset.sum_filter, Fin.sum_univ_two]
  simp [not_le.mpr hx]

/-- **Lemma PT.** For `u < w < k ≤ p`: `F(w) - F(u) = (w - u) Σ_{x ∈ [k,p)} 1/((x-u)(x-w))`;
that is, the level-zero Loewner kernel equals the Cauchy sum over the level-one block `[k,p)`. -/
theorem pt {k u w : ℕ} (huw : u < w) (hwk : w < k) (hkp : k ≤ p) :
    F2 (p := p) k w - F2 (p := p) k u =
      ((w : ZMod p) - (u : ZMod p)) * ∑ x ∈ Ico k p, cauchyKer u w x := by
  rw [F2_eq_modF, F2_eq_modF]
  have hbal : ∑ i, (![1, -1] : Fin 2 → ZMod p) i = 0 := by
    rw [Fin.sum_univ_two]; simp
  have h := ptg (fun i : Fin 2 => (![p, k] : Fin 2 → ℕ) i) (![1, -1] : Fin 2 → ZMod p) hbal huw
    (by intro i; fin_cases i <;> simp <;> omega) (by intro i; fin_cases i <;> simp <;> omega)
  rw [h]
  have : ∑ x ∈ range p, cum (fun i : Fin 2 => (![p, k] : Fin 2 → ℕ) i)
      (![1, -1] : Fin 2 → ZMod p) x * cauchyKer u w x =
      -∑ x ∈ Ico k p, cauchyKer u w x := by
    rw [← Finset.sum_neg_distrib]
    have hico : Ico k p = (range p).filter (fun x => k ≤ x) := by
      ext x; simp only [mem_Ico, mem_filter, mem_range]; omega
    rw [hico, Finset.sum_filter]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [cum_two (mem_range.1 hx)]
    split_ifs <;> simp
  rw [this]; ring

/-- Off-diagonal form: `M[u,w] = Σ_{x ∈ [k,p)} 1/((x-u)(x-w))`. -/
theorem pt_loewner {k u w : ℕ} (huw : u < w) (hwk : w < k) (hkp : k ≤ p) (hd : w - u < p) :
    (F2 (p := p) k w - F2 (p := p) k u) / ((w : ZMod p) - (u : ZMod p)) =
      ∑ x ∈ Ico k p, cauchyKer u w x := by
  rw [pt huw hwk hkp]
  have := zmod_sub_ne_zero_of_lt huw hd
  field_simp

/-! ### The diagonal -/

/-- Square prefix of the two-term frame (`Σ_{j ≤ n} ((j - k)⁻² - j⁻²)`). -/
def E2 (k n : ℕ) : ZMod p :=
  ∑ j ∈ Icc 1 n, ((((j : ZMod p) - (k : ZMod p))⁻¹) ^ 2 - (((j : ZMod p))⁻¹) ^ 2)

/-- Second harmonic number. -/
def H2 (n : ℕ) : ZMod p := ∑ t ∈ Icc 1 n, (((t : ZMod p))⁻¹) ^ 2

lemma sum_inv_sq_range (hp5 : 5 ≤ p) : ∑ x ∈ range p, (((x : ℕ) : ZMod p)⁻¹) ^ 2 = 0 := by
  rw [CatalanCore.Arith.Hybrid.LemmaE.sum_range_cast p (fun x => (x⁻¹) ^ 2)]
  have h1 : ∑ x : ZMod p, (x⁻¹) ^ 2 = ∑ x : ZMod p, x ^ 2 :=
    Fintype.sum_equiv (Function.Involutive.toPerm (fun x : ZMod p => x⁻¹) inv_involutive) _ _
      (fun x => by simp)
  rw [h1]
  exact FiniteField.sum_pow_lt_card_sub_one (ZMod p) 2 (by rw [ZMod.card]; omega)

lemma sum_Icc_eq_range {M : Type*} [AddCommMonoid M] (h : ℕ → M) (h0 : h 0 = 0) :
    ∀ n, ∑ t ∈ Icc 1 n, h t = ∑ x ∈ range (n + 1), h x := by
  intro n
  induction n with
  | zero => simp [h0]
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ _ (n + 1)]

lemma tele_Ico {M : Type*} [AddCommGroup M] (a : ℕ → M) (k : ℕ) :
    ∀ n, k ≤ n → ∑ x ∈ Ico k n, (a x - a (x + 1)) = a k - a n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih => rw [Finset.sum_Ico_succ_top hn, ih]; abel

/-- The diagonal Schur term is independent of `u`. -/
lemma diag_step (k u : ℕ) (hkp : k ≤ p) :
    E2 (p := p) k (u + 1) - ∑ x ∈ Ico k p, ((((x : ZMod p) - ((u + 1 : ℕ) : ZMod p))⁻¹) ^ 2) =
    E2 (p := p) k u - ∑ x ∈ Ico k p, ((((x : ZMod p) - (u : ZMod p))⁻¹) ^ 2) := by
  have ht := tele_Ico (fun x : ℕ => (((x : ZMod p) - ((u + 1 : ℕ) : ZMod p))⁻¹) ^ 2) k p hkp
  have hsh : ∀ x : ℕ, (((x + 1 : ℕ) : ZMod p) - ((u + 1 : ℕ) : ZMod p)) = (x : ZMod p) - u := by
    intro x; push_cast; ring
  simp only [hsh] at ht
  rw [Finset.sum_sub_distrib] at ht
  have hp0 : (((p : ℕ) : ZMod p) - ((u + 1 : ℕ) : ZMod p)) = -(((u + 1 : ℕ) : ZMod p)) := by
    rw [ZMod.natCast_self]; ring
  have hk0 : (((k : ℕ) : ZMod p) - ((u + 1 : ℕ) : ZMod p)) =
      -((((u + 1 : ℕ) : ZMod p)) - (k : ZMod p)) := by ring
  simp only [hp0, hk0, inv_neg, neg_sq] at ht
  unfold E2
  rw [Finset.sum_Icc_succ_top (by omega)]
  linear_combination -ht

theorem pt_diag (hp5 : 5 ≤ p) {k : ℕ} (hkp : k ≤ p) :
    ∀ u : ℕ, E2 (p := p) k u - ∑ x ∈ Ico k p, ((((x : ZMod p) - (u : ZMod p))⁻¹) ^ 2) =
      H2 (p := p) (k - 1) := by
  intro u
  induction u with
  | zero =>
    have e0 : E2 (p := p) k 0 = 0 := by simp [E2]
    rw [e0, zero_sub]
    simp only [Nat.cast_zero, sub_zero]
    have hfull := sum_inv_sq_range hp5
    have hsplit : ∑ x ∈ range p, (((x : ℕ) : ZMod p)⁻¹) ^ 2 =
        ∑ x ∈ range k, (((x : ℕ) : ZMod p)⁻¹) ^ 2 + ∑ x ∈ Ico k p, (((x : ℕ) : ZMod p)⁻¹) ^ 2 := by
      rw [Finset.range_eq_Ico, Finset.range_eq_Ico, Finset.sum_Ico_consecutive _ (Nat.zero_le k) hkp]
    have hH : H2 (p := p) (k - 1) = ∑ x ∈ range k, (((x : ℕ) : ZMod p)⁻¹) ^ 2 := by
      unfold H2
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; simp
      · rw [sum_Icc_eq_range (fun t : ℕ => (((t : ℕ) : ZMod p)⁻¹) ^ 2) (by simp), Nat.sub_add_cancel hk]
    rw [hH]
    linear_combination -hfull + hsplit
  | succ u ih =>
    rw [diag_step k u hkp]; exact ih

end CatalanCore.Uniform.Content.Smith
