module

public import CatalanFrames.Lambda.Frame
public import CatalanCore.Arith.Hybrid.LemmaE.Bridge

@[expose] public section

/-!
# λ: the entries `Mn` modulo `p` on the unpaired block (DQ Lemma 3.1 for the actual λ matrix)

Notation: `p ≥ 5` prime, `K < p` with `4K ≡ 1 (mod p)` (class `p ≡ 1 (4)`: `K = (3p+1)/4`;
class `p ≡ 3 (4)`: `K = (p+1)/4`), indices `a, b ≤ K - 1`.  The reductions of the rational entries
of `lamFrame.Mn` are
* `16 (b-a) · red(Mn a b) = φ(b) - φ(a)`,  `φ(n) = H_n + H_{K-1} - H_{K-1-n}`;
* `16 · red(Mn a a) = -(H2_a - H2_{K-1} + H2_{K-1-a})`,
and (with `Harmonic.lean`) `16 red Mn_{uw} = ∑_{c=K}^{p-1} 1/((c-u)(c-w))` for `u ≠ w`,
`16 red Mn_{uu} = ∑_c 1/(c-u)² + H2_{K-1}`: the Schur complement of the unpaired block is the
scalar `H2_{K-1}/16`, independent of `u`.
-/

open Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid.LemmaE Polynomial

namespace CatalanFrames.Lambda

/-- `T(n) = ∑_{k ≤ n} 1/(k(4k-1))`. -/
noncomputable def Tq (n : ℕ) : ℚ :=
  ∑ j ∈ range n, (((j + 1 : ℕ) : ℚ) * (4 * ((j + 1 : ℕ) : ℚ) - 1))⁻¹

lemma Ioc_zero_sum (g : ℕ → ℚ) (n : ℕ) : ∑ k ∈ Ioc 0 n, g k = ∑ j ∈ range n, g (j + 1) := by
  have : Ioc 0 n = Ico 1 (n + 1) := rfl
  rw [this, Finset.sum_Ico_eq_sum_range]
  simp [add_comm]

lemma Delta_sum (a b : ℕ) (hab : a ≤ b) :
    ∑ k ∈ Ioc a b, lamFrame.Delta k = -(Tq b - Tq a) := by
  have h := Finset.sum_Ioc_consecutive (fun k => lamFrame.Delta k) (Nat.zero_le a) hab
  have e : ∀ n, ∑ k ∈ Ioc 0 n, lamFrame.Delta k = -Tq n := by
    intro n
    rw [Ioc_zero_sum, Tq, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Delta_eq (j + 1) (by omega)]
    have h1 : (((j + 1 : ℕ) : ℚ)) ≠ 0 := by positivity
    have h2 : (4 * ((j + 1 : ℕ) : ℚ) - 1) ≠ 0 := by
      have : (1 : ℚ) ≤ ((j + 1 : ℕ) : ℚ) := by exact_mod_cast Nat.succ_pos j
      intro h; linarith
    field_simp
  rw [e, e] at h
  linarith

lemma Mn_off (a b : ℕ) (hab : a < b) :
    lamFrame.Mn a b = -(Tq b - Tq a) / (16 * ((b : ℚ) - a)) := by
  unfold Frame.Mn
  rw [if_neg (by omega), max_eq_right hab.le, min_eq_left hab.le, Delta_sum a b hab.le]
  have : (lamFrame.norm) = 16 := rfl
  rw [this]
  have : ((b : ℚ) - a) ≠ 0 := by
    have : (a : ℚ) < b := by exact_mod_cast hab
    intro h; linarith
  field_simp

section ModP

variable {p : ℕ} [Fact p.Prime]

lemma red_natCast (m : ℕ) : red p (m : ℚ) = (m : ZMod p) := Rat.cast_natCast m

lemma red_inv_nat {m : ℕ} (hm : ¬ p ∣ m) : ((m : ℚ)⁻¹) ∈ LocRing p ∧
    red p ((m : ℚ)⁻¹) = ((m : ZMod p))⁻¹ := by
  have hmem := inv_natCast_mem_locRing (ℓ := p) hm
  refine ⟨hmem, ?_⟩
  have hm0 : (m : ℚ) ≠ 0 := by
    intro h; apply hm; have : m = 0 := by exact_mod_cast h
    simp [this]
  have hmz : (m : ZMod p) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
  have hint : (m : ℚ) ∈ LocRing p := by exact_mod_cast int_mem_locRing (ℓ := p) (m : ℤ)
  have h1 : red p ((m : ℚ)⁻¹ * m) = 1 := by
    rw [inv_mul_cancel₀ hm0]; exact Rat.cast_one
  rw [red_mul hmem hint, red_natCast] at h1
  exact eq_inv_of_mul_eq_one_left h1

/-- `p ∤ k(4k-1)` for `1 ≤ k < K` (`4K ≡ 1`, `K < p`). -/
lemma not_dvd_term {K k : ℕ} (hK4 : 4 * (K : ZMod p) = 1) (hk1 : 1 ≤ k) (hkK : k < K)
    (hKp : K < p) : ¬ p ∣ k * (4 * k - 1) := by
  rw [← ZMod.natCast_eq_zero_iff]
  have h4 : (4 : ZMod p) ≠ 0 := by intro h; rw [h] at hK4; simp at hK4
  have hk0 : ((k : ℕ) : ZMod p) ≠ 0 := by
    intro h; rw [ZMod.natCast_eq_zero_iff] at h; exact absurd (Nat.le_of_dvd (by omega) h) (by omega)
  have hKk : ((K : ZMod p) - k) ≠ 0 := by
    have : (((K - k : ℕ)) : ZMod p) ≠ 0 := by
      intro h; rw [ZMod.natCast_eq_zero_iff] at h
      exact absurd (Nat.le_of_dvd (by omega) h) (by omega)
    rwa [Nat.cast_sub hkK.le] at this
  have e1 : (((4 * k - 1 : ℕ)) : ZMod p) = -4 * ((K : ZMod p) - k) := by
    rw [Nat.cast_sub (by omega)]; push_cast; linear_combination hK4
  push_cast [Nat.cast_mul]
  rw [e1]
  exact mul_ne_zero hk0 (mul_ne_zero (neg_ne_zero.mpr h4) hKk)

lemma term_red {K k : ℕ} (hK4 : 4 * (K : ZMod p) = 1) (hk1 : 1 ≤ k) (hkK : k < K) (hKp : K < p) :
    (((k : ℕ) : ℚ) * (4 * ((k : ℕ) : ℚ) - 1))⁻¹ ∈ LocRing p ∧
      red p ((((k : ℕ) : ℚ) * (4 * ((k : ℕ) : ℚ) - 1))⁻¹) =
        (((k : ℕ) : ZMod p) * (((4 * k - 1 : ℕ)) : ZMod p))⁻¹ := by
  have e : (((k : ℕ) : ℚ) * (4 * ((k : ℕ) : ℚ) - 1)) = ((k * (4 * k - 1) : ℕ) : ℚ) := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega)]; push_cast; ring
  rw [e]
  have := red_inv_nat (p := p) (not_dvd_term hK4 hk1 hkK hKp)
  refine ⟨this.1, ?_⟩
  rw [this.2]; push_cast [Nat.cast_mul]; rfl


lemma Tq_red {K : ℕ} (hK4 : 4 * (K : ZMod p) = 1) (hKp : K < p) :
    ∀ n, n ≤ K - 1 → Tq n ∈ LocRing p ∧ red p (Tq n) =
      ∑ j ∈ range n, ((((j + 1 : ℕ)) : ZMod p) * (((4 * (j + 1) - 1 : ℕ)) : ZMod p))⁻¹ := by
  intro n
  induction n with
  | zero => intro _; simp [Tq, red, (LocRing p).zero_mem]
  | succ n ih =>
    intro hn
    obtain ⟨h1, h2⟩ := ih (by omega)
    obtain ⟨t1, t2⟩ := term_red (p := p) hK4 (k := n + 1) (by omega) (by omega) hKp
    have e : Tq (n + 1) = Tq n + (((n + 1 : ℕ) : ℚ) * (4 * ((n + 1 : ℕ) : ℚ) - 1))⁻¹ := by
      unfold Tq; rw [Finset.sum_range_succ]
    rw [e, Finset.sum_range_succ]
    exact ⟨(LocRing p).add_mem h1 t1, by rw [red_add h1 t1, h2, t2]⟩

/-- `φ(n) = H_n + H_{K-1} - H_{K-1-n}` in `ZMod p`. -/
def phiH (p K n : ℕ) [Fact p.Prime] : ZMod p :=
  Gs p (fun x => x⁻¹) n + Gs p (fun x => x⁻¹) (K - 1) - Gs p (fun x => x⁻¹) (K - 1 - n)

lemma not_dvd_16 (hp : 5 ≤ p) {d : ℕ} (hd0 : 0 < d) (hdp : d < p) : ¬ p ∣ 16 * d := by
  intro h
  rcases (Nat.Prime.dvd_mul (Fact.out : p.Prime)).mp h with h | h
  · have : p ∣ 2 ^ 4 := by simpa using h
    have := (Nat.Prime.dvd_of_dvd_pow (Fact.out : p.Prime) this)
    have := Nat.le_of_dvd (by norm_num) this
    omega
  · exact absurd (Nat.le_of_dvd hd0 h) (by omega)

/-- **Off-diagonal entries of `Mn` modulo `p`.** -/
theorem Mn_off_red (hp : 5 ≤ p) {K : ℕ} (hK4 : 4 * (K : ZMod p) = 1) (hKp : K < p) {a b : ℕ}
    (hab : a < b) (hb : b ≤ K - 1) :
    lamFrame.Mn a b ∈ LocRing p ∧
      16 * ((b : ZMod p) - a) * red p (lamFrame.Mn a b) = phiH p K b - phiH p K a := by
  obtain ⟨t1, t2⟩ := Tq_red (p := p) hK4 hKp b hb
  obtain ⟨s1, s2⟩ := Tq_red (p := p) hK4 hKp a (by omega)
  have hd := not_dvd_16 (p := p) hp (d := b - a) (by omega) (by omega)
  have hinv := inv_natCast_mem_locRing (ℓ := p) hd
  have hdq : ((16 * (b - a) : ℕ) : ℚ) = 16 * ((b : ℚ) - a) := by
    rw [Nat.cast_mul, Nat.cast_sub hab.le]; push_cast; ring
  have hMn : lamFrame.Mn a b = -(Tq b - Tq a) * (((16 * (b - a) : ℕ) : ℚ))⁻¹ := by
    rw [Mn_off a b hab, hdq]; ring
  have hmem : lamFrame.Mn a b ∈ LocRing p :=
    hMn ▸ (LocRing p).mul_mem ((LocRing p).neg_mem ((LocRing p).sub_mem t1 s1)) hinv
  refine ⟨hmem, ?_⟩
  have hnum : -(Tq b - Tq a) ∈ LocRing p := (LocRing p).neg_mem ((LocRing p).sub_mem t1 s1)
  have hq : (((16 * (b - a) : ℕ) : ℚ)) ∈ LocRing p := by
    exact_mod_cast int_mem_locRing (ℓ := p) ((16 * (b - a) : ℕ) : ℤ)
  have hmul : lamFrame.Mn a b * (((16 * (b - a) : ℕ) : ℚ)) = -(Tq b - Tq a) := by
    rw [hMn, mul_assoc, inv_mul_cancel₀, mul_one]
    have : (16 * (b - a) : ℕ) ≠ 0 := by omega
    exact_mod_cast this
  have hr := congrArg (red p) hmul
  rw [red_mul hmem hq, red_neg, red_sub t1 s1, red_natCast, t2, s2] at hr
  have F1 := Fz_eq (p := p) (by omega) hK4 hKp (n := b) hb
  have F2 := Fz_eq (p := p) (by omega) hK4 hKp (n := a) (by omega)
  rw [F1, F2] at hr
  have e : (((16 * (b - a) : ℕ)) : ZMod p) = 16 * ((b : ZMod p) - a) := by
    rw [Nat.cast_mul, Nat.cast_sub hab.le]; push_cast; ring
  rw [e] at hr
  unfold phiH
  rw [mul_comm]
  linear_combination hr

lemma cast_sub_ne_zero {c u : ℕ} (huc : u < c) (hcp : c < p) : ((c : ZMod p) - u) ≠ 0 := by
  have : (((c - u : ℕ)) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro h; exact absurd (Nat.le_of_dvd (by omega) h) (by omega)
  rwa [Nat.cast_sub huc.le] at this

/-- **Scalar Schur complement, off-diagonal entries (λ, DQ Lemma 3.1).**
For `u < w < K ≤ p`: `16 · red Mn_{uw} = ∑_{c=K}^{p-1} 1/((c-u)(c-w))`, i.e. the Schur complement
`Mn_UU - (1/16) ∑ ...` vanishes off the diagonal. -/
theorem lam_UU_off (hp : 5 ≤ p) {K : ℕ} (hK4 : 4 * (K : ZMod p) = 1) (hKp : K < p) {u w : ℕ}
    (huw : u < w) (hw : w ≤ K - 1) :
    16 * red p (lamFrame.Mn u w) =
      ∑ c ∈ Ico K p, ((((c : ℕ) : ZMod p) - u)⁻¹ * (((c : ℕ) : ZMod p) - w)⁻¹) := by
  obtain ⟨_, h1⟩ := Mn_off_red hp hK4 hKp huw hw
  have h2 := schur_offdiag p (by omega) (K := K) (u := u) (w := w) (by omega) (by omega)
    (by omega)
  have hwu : ((w : ZMod p) - u) ≠ 0 := cast_sub_ne_zero huw (by omega)
  have hterm : ∀ c ∈ Ico K p, ((((c : ℕ) : ZMod p) - w)⁻¹ - (((c : ℕ) : ZMod p) - u)⁻¹) =
      ((w : ZMod p) - u) * ((((c : ℕ) : ZMod p) - u)⁻¹ * (((c : ℕ) : ZMod p) - w)⁻¹) := by
    intro c hc
    have hc' := Finset.mem_Ico.mp hc
    have a1 : ((c : ZMod p) - u) ≠ 0 := cast_sub_ne_zero (by omega) hc'.2
    have a2 : ((c : ZMod p) - w) ≠ 0 := cast_sub_ne_zero (by omega) hc'.2
    field_simp
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum] at h2
  unfold phiH at h1
  apply mul_left_cancel₀ hwu
  rw [← mul_assoc, mul_comm ((w : ZMod p) - u) 16]
  linear_combination h1 - h2

end ModP

end CatalanFrames.Lambda
