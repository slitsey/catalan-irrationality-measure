module

public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.IsPrimePow
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.Prime.Pow
public import Mathlib.Algebra.Ring.Subring.Basic

@[expose] public section

/-!
# `ℓ`-integral rationals and prime-power weights

Frame-independent helpers for the content engine (`Arith/Weights`):

* `LocRing ℓ`      : the subring `ℤ_(ℓ)` of `ℚ` of rationals whose denominator is prime to `ℓ`;
* `int_of_forall_locRing` : a rational lying in every `ℤ_(ℓ)` is an integer;
* `div_mem_locRing` : `W / n ∈ ℤ_(p)` when `p^{v_p(n)} ∣ W`;
* `pow_dvd_prod_minFac` : if every prime power `p^e ∣ n` (`e > 0`) belongs to a finite set `Q`,
  then `p^{v_p(n)}` divides `∏_{q ∈ Q} minFac q`.
-/

open Finset

namespace CatalanCore.Basic

/-- The ring of `ℓ`-integral rationals `ℤ_(ℓ)`. -/
def LocRing (ℓ : ℕ) [hℓ : Fact ℓ.Prime] : Subring ℚ where
  carrier := {q | ¬ ℓ ∣ q.den}
  mul_mem' := by
    intro a b ha hb h
    rcases (Nat.Prime.dvd_mul hℓ.out).1 (h.trans (Rat.mul_den_dvd a b)) with h | h
    · exact ha h
    · exact hb h
  one_mem' := by
    show ¬ ℓ ∣ (1:ℚ).den
    rw [Rat.den_one]; exact fun h => hℓ.out.ne_one (Nat.dvd_one.1 h)
  add_mem' := by
    intro a b ha hb h
    rcases (Nat.Prime.dvd_mul hℓ.out).1 (h.trans (Rat.add_den_dvd a b)) with h | h
    · exact ha h
    · exact hb h
  zero_mem' := by
    show ¬ ℓ ∣ (0:ℚ).den
    rw [Rat.den_zero]; exact fun h => hℓ.out.ne_one (Nat.dvd_one.1 h)
  neg_mem' := by intro a ha; simpa [Rat.neg_den] using ha

variable {ℓ : ℕ} [Fact ℓ.Prime]

lemma mem_locRing {q : ℚ} : q ∈ LocRing ℓ ↔ ¬ ℓ ∣ q.den := Iff.rfl

lemma int_mem_locRing (z : ℤ) : (z : ℚ) ∈ LocRing ℓ := by
  rw [mem_locRing, Rat.den_intCast]
  exact fun h => (Fact.out : ℓ.Prime).ne_one (Nat.dvd_one.1 h)

/-- A rational lying in `ℤ_(p)` for every prime `p` is an integer. -/
lemma int_of_forall_locRing (x : ℚ) (H : ∀ (p : ℕ) [Fact p.Prime], x ∈ LocRing p) :
    ∃ z : ℤ, x = z := by
  by_cases hd : x.den = 1
  · exact ⟨x.num, (Rat.coe_int_num_of_den_eq_one hd).symm⟩
  · obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hd
    have := Fact.mk hp
    exact absurd hpd (H p)

/-- `1 / m ∈ ℤ_(ℓ)` when `ℓ ∤ m`. -/
lemma inv_natCast_mem_locRing {m : ℕ} (hm : ¬ ℓ ∣ m) : ((m : ℚ))⁻¹ ∈ LocRing ℓ := by
  rw [mem_locRing, Rat.inv_natCast_den]
  by_cases h0 : m = 0
  · subst h0; simp at hm
  · simp [h0, hm]

/-- `W / n ∈ ℤ_(p)` when `p^{v_p(n)} ∣ W`. -/
lemma div_mem_locRing {p : ℕ} [hp : Fact p.Prime] {n W : ℕ} (hn : 0 < n)
    (h : p ^ (n.factorization p) ∣ W) : ((W : ℚ) / n) ∈ LocRing p := by
  obtain ⟨t, ht⟩ := h
  have hm : ¬ p ∣ n / p ^ (n.factorization p) := Nat.not_dvd_ordCompl hp.out hn.ne'
  have hn' : p ^ (n.factorization p) * (n / p ^ (n.factorization p)) = n :=
    Nat.ordProj_mul_ordCompl_eq_self n p
  set m := n / p ^ (n.factorization p) with hmdef
  have hpv : (p : ℚ) ^ (n.factorization p) ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  have hm0 : m ≠ 0 := by
    intro h0; rw [h0] at hn'; omega
  have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast hm0
  have : ((W : ℚ) / n) = (t : ℚ) * ((m : ℚ))⁻¹ := by
    have hnq : (n : ℚ) = (p : ℚ) ^ (n.factorization p) * m := by exact_mod_cast hn'.symm
    rw [ht, hnq]; push_cast; field_simp
  rw [this]
  exact (LocRing p).mul_mem (by exact_mod_cast int_mem_locRing (ℓ := p) (t : ℤ))
    (inv_natCast_mem_locRing hm)

/-- If every prime power `p^e ∣ n` (`e > 0`) lies in `Q`, then `p^{v_p(n)}` divides
`∏_{q ∈ Q} minFac q`. -/
lemma pow_dvd_prod_minFac {Q : Finset ℕ} {n p : ℕ} (hp : p.Prime)
    (H : ∀ e, 0 < e → p ^ e ∣ n → p ^ e ∈ Q) :
    p ^ (n.factorization p) ∣ ∏ q ∈ Q, q.minFac := by
  set v := n.factorization p with hv
  have hinj : Set.InjOn (fun e : ℕ => p ^ e) (Finset.Icc 1 v : Finset ℕ) := fun x _ y _ hxy =>
    Nat.pow_right_injective hp.two_le hxy
  have h1 : p ^ v = ∏ q ∈ (Finset.Icc 1 v).image (fun e : ℕ => p ^ e), q.minFac := by
    rw [Finset.prod_image hinj]
    rw [Finset.prod_congr rfl (g := fun _ => p)]
    · simp
    · intro e he
      have : e ≠ 0 := by have := (Finset.mem_Icc.mp he).1; omega
      exact hp.pow_minFac this
  rw [h1]
  apply Finset.prod_dvd_prod_of_subset
  intro q hq
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hq
  have he1 := (Finset.mem_Icc.mp he).1
  have he2 := (Finset.mem_Icc.mp he).2
  exact H e he1 ((Nat.pow_dvd_pow p he2).trans (Nat.ordProj_dvd n p))

end CatalanCore.Basic
