module

public import CatalanCore.Uniform.Content.Hybrid.PoleSplit
public import CatalanCore.Arith.Hybrid.LemmaE.Harmonic

@[expose] public section

/-!
# Exact pole subtraction for a rational digamma frame

A rational digamma frame has finitely many poles `j` with shifts `μ_j = u_j/q_j` and rational
coefficients `c_j` (normalisation absorbed; balance `Σ c_j = 0` is NOT required):

  `f_n = Σ_j c_j Σ_{k<n} 1/(k + μ_j) = Σ_j Σ_{k<n} c_j q_j/(q_j k + u_j)`,
  `e_n = Σ_j Σ_{k<n} c_j q_j²/(q_j k + u_j)²`.

At a prime `p ≥ 3` with `p ∤ q_j`, `c_j` `p`-integral, and nodes `n ≤ B` with
`q_j B + u_j ≤ p²` (the compact band), `DigammaFrame.poleSplit` gives the exact pole split:
singular summands (`p ∣ q_j k + u_j`) form `Lf/p` and `E/p²` with `p`-integral `Lf, E`; the
regular parts `F, Gq` are `p`-integral; and `F` is PERIODIC modulo `p` per pole, because a block of
`p` consecutive summands runs through all residues and `Σ_{x ∈ 𝔽_p} x⁻¹ = 0`.
-/

open Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid

namespace CatalanCore.Uniform.Content.Hybrid

variable {p : ℕ} [hp : Fact p.Prime]

/-- A rational digamma frame. -/
structure DigammaFrame (J : Type*) [Fintype J] where
  u : J → ℕ
  q : J → ℕ
  c : J → ℚ

lemma sum_inv_zmod (hp3 : 3 ≤ p) : ∑ x : ZMod p, x⁻¹ = 0 := by
  have h1 : ∑ x : ZMod p, x⁻¹ = ∑ x : ZMod p, x :=
    Fintype.sum_equiv (Function.Involutive.toPerm (fun x : ZMod p => x⁻¹) inv_involutive) _ _
      (fun x => rfl)
  rw [h1]
  have := FiniteField.sum_pow_lt_card_sub_one (ZMod p) 1 (by rw [ZMod.card]; omega)
  simpa using this

lemma good_zero_div_p {x : ℚ} (h : Good p x 0) : x / p ∈ S p := by
  have hx : x ∈ LocRing p := h.1
  have hr : redQ p ⟨x, hx⟩ = 0 := by rw [redQ_apply]; exact h.2
  obtain ⟨y, hy⟩ := (redQ_eq_zero_iff p _).1 hr
  have hy' : x = (p : ℚ) * (y : ℚ) := by
    have := congrArg (fun z : LocRing p => (z : ℚ)) hy
    simpa using this
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have : x / p = (y : ℚ) := by rw [hy']; field_simp
  rw [this]; exact y.2

lemma good_inv_nat {m : ℕ} (hm : ¬ p ∣ m) : Good p ((m : ℚ)⁻¹) ((m : ZMod p)⁻¹) :=
  (Good.natCast m).inv (by rw [Ne, ZMod.natCast_eq_zero_iff]; exact hm)

namespace DigammaFrame

variable {J : Type*} [Fintype J] (D : DigammaFrame J)

/-- The denominator `q_j k + u_j`. -/
def den (j : J) (k : ℕ) : ℕ := D.q j * k + D.u j

noncomputable def f (n : ℕ) : ℚ := ∑ j, ∑ k ∈ range n, D.c j * D.q j / (D.den j k : ℚ)

noncomputable def e (n : ℕ) : ℚ :=
  ∑ j, ∑ k ∈ range n, D.c j * (D.q j : ℚ) ^ 2 / (D.den j k : ℚ) ^ 2

open Classical in
/-- Pole part, scaled by `p`. -/
noncomputable def Lf (p : ℕ) (n : ℕ) : ℚ :=
  ∑ j, ∑ k ∈ range n, if p ∣ D.den j k then D.c j * D.q j * p / (D.den j k : ℚ) else 0

open Classical in
/-- Regular part. -/
noncomputable def F (p : ℕ) (n : ℕ) : ℚ :=
  ∑ j, ∑ k ∈ range n, if p ∣ D.den j k then 0 else D.c j * D.q j / (D.den j k : ℚ)

open Classical in
noncomputable def E (p : ℕ) (n : ℕ) : ℚ :=
  ∑ j, ∑ k ∈ range n, if p ∣ D.den j k then
    D.c j * (D.q j : ℚ) ^ 2 * (p : ℚ) ^ 2 / (D.den j k : ℚ) ^ 2 else 0

open Classical in
noncomputable def Gq (p : ℕ) (n : ℕ) : ℚ :=
  ∑ j, ∑ k ∈ range n, if p ∣ D.den j k then 0 else D.c j * (D.q j : ℚ) ^ 2 / (D.den j k : ℚ) ^ 2

lemma f_split (n : ℕ) : D.f n = D.Lf p n / p + D.F p n := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  classical
  simp only [f, Lf, F, Finset.sum_div, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  split_ifs
  · rw [add_zero, div_div, mul_comm (D.den j k : ℚ) p, ← div_div, mul_div_cancel_right₀ _ hp0]
  · rw [zero_div, zero_add]

lemma e_split (n : ℕ) : D.e n = D.E p n / (p : ℚ) ^ 2 + D.Gq p n := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  classical
  have hp2 : (p : ℚ) ^ 2 ≠ 0 := pow_ne_zero 2 hp0
  simp only [e, E, Gq, Finset.sum_div, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  split_ifs
  · rw [add_zero, div_div, mul_comm ((D.den j k : ℚ) ^ 2) ((p : ℚ) ^ 2), ← div_div,
      mul_div_cancel_right₀ _ hp2]
  · rw [zero_div, zero_add]

variable {D}

/-- On the compact band a singular denominator is `p·t` with `p ∤ t`. -/
lemma sing_factor {m : ℕ} (hm : p ∣ m) (hlt : m < p ^ 2) (h0 : m ≠ 0) :
    ∃ t, m = p * t ∧ ¬ p ∣ t := by
  obtain ⟨t, rfl⟩ := hm
  refine ⟨t, rfl, fun ht => ?_⟩
  obtain ⟨s, rfl⟩ := ht
  have hs : s ≠ 0 := by rintro rfl; simp at h0
  have : p ^ 2 ≤ p * (p * s) := by
    rw [pow_two, ← mul_assoc]; exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hs)
  omega

lemma S_of_den (hc : ∀ j, D.c j ∈ S p) (j : J) (k : ℕ) (hlt : D.den j k < p ^ 2) :
    (if p ∣ D.den j k then D.c j * D.q j * p / (D.den j k : ℚ) else 0) ∈ S p ∧
    (if p ∣ D.den j k then 0 else D.c j * D.q j / (D.den j k : ℚ)) ∈ S p ∧
    (if p ∣ D.den j k then
      D.c j * (D.q j : ℚ) ^ 2 * (p : ℚ) ^ 2 / (D.den j k : ℚ) ^ 2 else 0) ∈ S p ∧
    (if p ∣ D.den j k then 0 else D.c j * (D.q j : ℚ) ^ 2 / (D.den j k : ℚ) ^ 2) ∈ S p := by
  have hq : (D.q j : ℚ) ∈ S p := (Good.natCast _).1
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  by_cases hd : p ∣ D.den j k
  · simp only [if_pos hd]
    refine ⟨?_, (S p).zero_mem, ?_, (S p).zero_mem⟩
    · by_cases h0 : D.den j k = 0
      · rw [h0]; simp [(S p).zero_mem]
      obtain ⟨t, ht, hpt⟩ := sing_factor hd hlt h0
      have e1 : D.c j * D.q j * p / (D.den j k : ℚ) = D.c j * D.q j * ((t : ℚ)⁻¹) := by
        rw [ht]; push_cast; field_simp
      rw [e1]
      exact (S p).mul_mem ((S p).mul_mem (hc j) hq) (good_inv_nat hpt).1
    · by_cases h0 : D.den j k = 0
      · rw [h0]; simp [(S p).zero_mem]
      obtain ⟨t, ht, hpt⟩ := sing_factor hd hlt h0
      have e1 : D.c j * (D.q j : ℚ) ^ 2 * (p : ℚ) ^ 2 / (D.den j k : ℚ) ^ 2 =
          D.c j * (D.q j : ℚ) ^ 2 * ((t : ℚ)⁻¹) ^ 2 := by
        rw [ht]; push_cast; field_simp
      rw [e1]
      exact (S p).mul_mem ((S p).mul_mem (hc j) ((S p).pow_mem hq 2))
        ((S p).pow_mem (good_inv_nat hpt).1 2)
  · simp only [if_neg hd]
    refine ⟨(S p).zero_mem, ?_, (S p).zero_mem, ?_⟩
    · rw [div_eq_mul_inv]
      exact (S p).mul_mem ((S p).mul_mem (hc j) hq) (good_inv_nat hd).1
    · rw [div_eq_mul_inv, ← inv_pow]
      exact (S p).mul_mem ((S p).mul_mem (hc j) ((S p).pow_mem hq 2))
        ((S p).pow_mem (good_inv_nat hd).1 2)

lemma den_lt {B : ℕ} (hbd : ∀ j, D.q j * B + D.u j ≤ p ^ 2) (hpq : ∀ j, ¬ p ∣ D.q j)
    {j : J} {k : ℕ} (hk : k < B) : D.den j k < p ^ 2 := by
  have hq : 0 < D.q j := Nat.pos_of_ne_zero fun h => hpq j (h ▸ dvd_zero p)
  have := hbd j
  have : D.q j * k < D.q j * B := Nat.mul_lt_mul_of_pos_left hk hq
  unfold den; omega

open Classical in
/-- One block of `p` consecutive regular summands of one pole is `≡ 0 (mod p)`. -/
lemma block_good (hc : ∀ j, D.c j ∈ S p) (hpq : ∀ j, ¬ p ∣ D.q j) (hp3 : 3 ≤ p) (j : J)
    (k0 : ℕ) :
    Good p (∑ y ∈ range p,
      if p ∣ D.den j (k0 + y) then 0 else D.c j * D.q j / (D.den j (k0 + y) : ℚ)) 0 := by
  have hcq : Good p (D.c j * D.q j) (red p (D.c j * D.q j)) :=
    good_red ((S p).mul_mem (hc j) (Good.natCast _).1)
  have hterm : ∀ y ∈ range p, Good p
      (if p ∣ D.den j (k0 + y) then 0 else D.c j * D.q j / (D.den j (k0 + y) : ℚ))
      (red p (D.c j * D.q j) * ((D.q j : ZMod p) * (y : ZMod p) +
        ((D.q j * k0 + D.u j : ℕ) : ZMod p))⁻¹) := by
    intro y _
    have hcast : ((D.den j (k0 + y) : ℕ) : ZMod p) =
        (D.q j : ZMod p) * (y : ZMod p) + ((D.q j * k0 + D.u j : ℕ) : ZMod p) := by
      simp only [den]; push_cast; ring
    rw [← hcast]
    split_ifs with hd
    · have : ((D.den j (k0 + y) : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hd
      rw [this, inv_zero, mul_zero]; exact Good.zero
    · rw [div_eq_mul_inv]; exact hcq.mul (good_inv_nat hd)
  have hs := Good.sum _ _ _ hterm
  refine hs.congr ?_
  rw [← Finset.mul_sum]
  have hq0 : (D.q j : ZMod p) ≠ 0 := by rw [Ne, ZMod.natCast_eq_zero_iff]; exact hpq j
  rw [LemmaE.sum_range_cast p (fun x => ((D.q j : ZMod p) * x +
    ((D.q j * k0 + D.u j : ℕ) : ZMod p))⁻¹)]
  have hbij : Function.Bijective (fun x : ZMod p => (D.q j : ZMod p) * x +
      ((D.q j * k0 + D.u j : ℕ) : ZMod p)) := by
    refine (Finite.injective_iff_bijective).1 ?_
    intro x y h
    simpa [hq0] using h
  rw [Fintype.sum_bijective _ hbij (fun x => ((D.q j : ZMod p) * x +
      ((D.q j * k0 + D.u j : ℕ) : ZMod p))⁻¹) (fun x => x⁻¹) (fun x => rfl),
    sum_inv_zmod hp3, mul_zero]

open Classical in
/-- Regular prefixes over `r` complete blocks starting at `m` are `≡ 0 (mod p)`. -/
lemma blocks_good (hc : ∀ j, D.c j ∈ S p) (hpq : ∀ j, ¬ p ∣ D.q j) (hp3 : 3 ≤ p) (m : ℕ) :
    ∀ r, Good p (D.F p (m + p * r) - D.F p m) 0 := by
  intro r
  induction r with
  | zero => simpa using (Good.zero (ℓ := p))
  | succ r ih =>
    have e1 : D.F p (m + p * (r + 1)) - D.F p m = (D.F p (m + p * r) - D.F p m) +
        ∑ j, ∑ y ∈ range p, (if p ∣ D.den j ((m + p * r) + y) then 0 else
          D.c j * D.q j / (D.den j ((m + p * r) + y) : ℚ)) := by
      have : m + p * (r + 1) = (m + p * r) + p := by ring
      simp only [F, this, Finset.sum_range_add, Finset.sum_add_distrib]
      ring
    rw [e1]
    have hb : Good p (∑ j, ∑ y ∈ range p, (if p ∣ D.den j ((m + p * r) + y) then 0 else
          D.c j * D.q j / (D.den j ((m + p * r) + y) : ℚ))) (∑ _j : J, (0 : ZMod p)) :=
      Good.sum Finset.univ _ (fun _ => 0) (fun j _ => block_good hc hpq hp3 j (m + p * r))
    have := ih.add hb
    simpa using this

variable (D)

/-- **Exact pole subtraction for a rational digamma frame.** -/
noncomputable def poleSplit (B : ℕ) (hc : ∀ j, D.c j ∈ S p) (hpq : ∀ j, ¬ p ∣ D.q j)
    (hp3 : 3 ≤ p) (hbd : ∀ j, D.q j * B + D.u j ≤ p ^ 2) : PoleSplit p B D.f D.e where
  Lf := D.Lf p
  F := D.F p
  E := D.E p
  Gq := D.Gq p
  lf := fun n => red p (D.Lf p n)
  hf := fun n _ => D.f_split n
  he := fun n _ => D.e_split n
  hLf := fun n hn => good_red ((S p).sum_mem fun j _ => (S p).sum_mem fun k hk =>
    (S_of_den hc j k (den_lt hbd hpq (lt_of_lt_of_le (Finset.mem_range.1 hk) hn))).1)
  hF := fun n hn => (S p).sum_mem fun j _ => (S p).sum_mem fun k hk =>
    (S_of_den hc j k (den_lt hbd hpq (lt_of_lt_of_le (Finset.mem_range.1 hk) hn))).2.1
  hE := fun n hn => (S p).sum_mem fun j _ => (S p).sum_mem fun k hk =>
    (S_of_den hc j k (den_lt hbd hpq (lt_of_lt_of_le (Finset.mem_range.1 hk) hn))).2.2.1
  hGq := fun n hn => (S p).sum_mem fun j _ => (S p).sum_mem fun k hk =>
    (S_of_den hc j k (den_lt hbd hpq (lt_of_lt_of_le (Finset.mem_range.1 hk) hn))).2.2.2
  hper := by
    intro n _ m _ hnm
    rcases le_total m n with h | h
    · obtain ⟨r, hr⟩ : p ∣ n - m := (Nat.modEq_iff_dvd' h).1 hnm.symm
      have hn : n = m + p * r := by omega
      rw [hn]; exact good_zero_div_p (blocks_good hc hpq hp3 m r)
    · obtain ⟨r, hr⟩ : p ∣ m - n := (Nat.modEq_iff_dvd' h).1 hnm
      have hm : m = n + p * r := by omega
      rw [hm]
      have := good_zero_div_p ((blocks_good hc hpq hp3 n r).neg.congr neg_zero)
      have e : -(D.F p (n + p * r) - D.F p n) / p = (D.F p n - D.F p (n + p * r)) / p := by ring
      rw [← e]; simpa using this

end DigammaFrame

end CatalanCore.Uniform.Content.Hybrid
