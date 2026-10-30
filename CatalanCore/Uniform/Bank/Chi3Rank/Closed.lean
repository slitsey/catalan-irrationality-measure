module

public import CatalanCore.Uniform.Content.Member.FrameDigamma
public import CatalanFrames.P6.Frame

@[expose] public section
set_option Elab.async false

/-! # Closed form of the pole part `Lf`, `E` of the chi3 digamma frame at the node `x + p d` (lane H, H16)

For the digamma presentation `frameDigamma p6Frame u3 q3` of `P6` (poles at `μ = 1, 1/3, 1/2`),
the pole parts of the prefixes at the node `n = x + p d` (`x < p`) are explicit rationals depending
only on `d`, the residue class of `p` modulo `6`, and which of the first two singular positions
(`k_A` for `μ = 1/3`, `k_B = (p-1)/2` for `μ = 1/2`) lie below `x`. -/

namespace CatalanCore.Uniform.Bank.Chi3Rank
open Finset CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.Hybrid
  CatalanCore.Uniform.Content.Member CatalanFrames.P6

/-- Singular summands of a progression `q k + u`: one per residue period. -/
theorem sing_sum (p : ℕ) [hp : Fact p.Prime] (ψ : ℕ → ℚ) (q u kj w x d : ℕ)
    (hpq : ¬ p ∣ q) (hkj : kj < p) (hw : q * kj + u = p * w) (hx : x < p) :
    ∑ k ∈ range (x + p * d), (if p ∣ q * k + u then ψ ((q * k + u) / p) else 0) =
      ∑ m ∈ range (d + if kj < x then 1 else 0), ψ (w + q * m) := by
  classical
  have hcop : Nat.gcd p q = 1 := (Nat.Prime.coprime_iff_not_dvd hp.out).2 hpq
  have hp0 : 0 < p := hp.out.pos
  rw [← Finset.sum_filter]
  have himg : (range (x + p * d)).filter (fun k => p ∣ q * k + u) =
      (range (d + if kj < x then 1 else 0)).image (fun m => kj + p * m) := by
    ext k
    simp only [mem_filter, mem_range, mem_image]
    constructor
    · rintro ⟨hk, hdv⟩
      have a1 : q * k + u ≡ 0 [MOD p] := (Nat.modEq_zero_iff_dvd).2 hdv
      have a2 : q * kj + u ≡ 0 [MOD p] := (Nat.modEq_zero_iff_dvd).2 ⟨w, hw⟩
      have h2 : q * k ≡ q * kj [MOD p] := Nat.ModEq.add_right_cancel' u (a1.trans a2.symm)
      have h3 : k ≡ kj [MOD p] := Nat.ModEq.cancel_left_of_coprime hcop h2
      have h4 : k % p = kj := by
        have := h3; unfold Nat.ModEq at this; rw [Nat.mod_eq_of_lt hkj] at this; exact this
      have h5 : k = kj + p * (k / p) := by
        have := Nat.div_add_mod k p; omega
      refine ⟨k / p, ?_, h5.symm⟩
      by_contra hm
      push_neg at hm
      split_ifs at hm with hlt
      · have h6 : p * (d + 1) ≤ p * (k / p) := Nat.mul_le_mul_left p hm
        rw [Nat.mul_add, Nat.mul_one] at h6
        omega
      · have h6 : p * d ≤ p * (k / p) := Nat.mul_le_mul_left p (by omega)
        omega
    · rintro ⟨m, hm, rfl⟩
      constructor
      · split_ifs at hm with hlt
        · have h6 : p * m ≤ p * d := Nat.mul_le_mul_left p (by omega)
          rcases Nat.lt_or_ge m d with hmd | hmd
          · have h7 : p * (m + 1) ≤ p * d := Nat.mul_le_mul_left p hmd
            rw [Nat.mul_add, Nat.mul_one] at h7
            omega
          · have : m = d := by omega
            subst this; omega
        · have h7 : p * (m + 1) ≤ p * d := Nat.mul_le_mul_left p (by omega)
          rw [Nat.mul_add, Nat.mul_one] at h7
          omega
      · refine ⟨w + q * m, ?_⟩
        calc q * (kj + p * m) + u = (q * kj + u) + p * (q * m) := by ring
          _ = p * w + p * (q * m) := by rw [hw]
          _ = p * (w + q * m) := by ring
  rw [himg, Finset.sum_image (fun a _ b _ h => by
    have : p * a = p * b := by omega
    exact Nat.eq_of_mul_eq_mul_left hp0 this)]
  refine Finset.sum_congr rfl fun m _ => ?_
  have : q * (kj + p * m) + u = p * (w + q * m) := by
    calc q * (kj + p * m) + u = (q * kj + u) + p * (q * m) := by ring
      _ = p * w + p * (q * m) := by rw [hw]
      _ = p * (w + q * m) := by ring
  rw [this, Nat.mul_div_cancel_left _ hp0]

/-- The `Lf` summand rewritten for `sing_sum`. -/
theorem lf_term (p : ℕ) [hp : Fact p.Prime] (c : ℚ) (q u kj w x d : ℕ) (hq : 0 < q)
    (hpq : ¬ p ∣ q) (hkj : kj < p) (hw : q * kj + u = p * w) (hx : x < p) :
    ∑ k ∈ range (x + p * d),
        (if p ∣ q * k + u then c * q * p / ((q * k + u : ℕ) : ℚ) else 0) =
      ∑ m ∈ range (d + if kj < x then 1 else 0), c * q / ((w + q * m : ℕ) : ℚ) := by
  classical
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [← sing_sum p (fun t => c * q / (t : ℚ)) q u kj w x d hpq hkj hw hx]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs with hdv
  · obtain ⟨t, ht⟩ := hdv
    rw [ht, Nat.mul_div_cancel_left _ hp.out.pos]
    push_cast
    by_cases h0 : (t : ℚ) = 0
    · simp [h0]
    · field_simp
  · rfl

theorem e_term (p : ℕ) [hp : Fact p.Prime] (c : ℚ) (q u kj w x d : ℕ) (hq : 0 < q)
    (hpq : ¬ p ∣ q) (hkj : kj < p) (hw : q * kj + u = p * w) (hx : x < p) :
    ∑ k ∈ range (x + p * d),
        (if p ∣ q * k + u then c * (q : ℚ) ^ 2 * (p : ℚ) ^ 2 / ((q * k + u : ℕ) : ℚ) ^ 2
          else 0) =
      ∑ m ∈ range (d + if kj < x then 1 else 0), c * (q : ℚ) ^ 2 / ((w + q * m : ℕ) : ℚ) ^ 2 := by
  classical
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [← sing_sum p (fun t => c * (q : ℚ) ^ 2 / (t : ℚ) ^ 2) q u kj w x d hpq hkj hw hx]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs with hdv
  · obtain ⟨t, ht⟩ := hdv
    rw [ht, Nat.mul_div_cancel_left _ hp.out.pos]
    push_cast
    by_cases h0 : (t : ℚ) = 0
    · simp [h0]
    · field_simp
  · rfl

/-- Numerators of the chi3 digamma frame. -/
def u3 : Fin 3 → ℕ := fun _ => 1
def q3 : Fin 3 → ℕ := ![1, 3, 2]

theorem hu3 (j : Fin 3) : p6Frame.μ j = u3 j / q3 j := by
  fin_cases j <;> simp [p6Frame, u3, q3] <;> norm_num

theorem hq3 (j : Fin 3) : 0 < q3 j := by fin_cases j <;> simp [q3]

/-- The chi3 digamma frame. -/
noncomputable abbrev Dchi : DigammaFrame (Fin 3) := frameDigamma p6Frame u3 q3

theorem Dchi_c0 : Dchi.c 0 = 1 / 36 := by simp [Dchi, frameDigamma, p6Frame]
theorem Dchi_c1 : Dchi.c 1 = 2 / 36 := by simp [Dchi, frameDigamma, p6Frame]
theorem Dchi_c2 : Dchi.c 2 = -3 / 36 := by simp [Dchi, frameDigamma, p6Frame]
theorem Dchi_q0 : Dchi.q 0 = 1 := rfl
theorem Dchi_q1 : Dchi.q 1 = 3 := rfl
theorem Dchi_q2 : Dchi.q 2 = 2 := rfl
theorem Dchi_u (j : Fin 3) : Dchi.u j = 1 := rfl

/-- Closed form of `Lf` and `E` of the chi3 frame in terms of the three singular positions. -/
theorem LfE_node (p : ℕ) [hp : Fact p.Prime] (h2 : ¬ p ∣ 2) (h3 : ¬ p ∣ 3)
    (kA wA kB wB x d : ℕ) (hkA : kA < p) (hwA : 3 * kA + 1 = p * wA) (hkB : kB < p)
    (hwB : 2 * kB + 1 = p * wB) (hx : x < p) :
    Dchi.Lf p (x + p * d) =
      (∑ m ∈ range d, Dchi.c 0 * (Dchi.q 0 : ℚ) / ((1 + Dchi.q 0 * m : ℕ) : ℚ)) +
      (∑ m ∈ range (d + if kA < x then 1 else 0),
        Dchi.c 1 * (Dchi.q 1 : ℚ) / ((wA + Dchi.q 1 * m : ℕ) : ℚ)) +
      (∑ m ∈ range (d + if kB < x then 1 else 0),
        Dchi.c 2 * (Dchi.q 2 : ℚ) / ((wB + Dchi.q 2 * m : ℕ) : ℚ)) ∧
    Dchi.E p (x + p * d) =
      (∑ m ∈ range d, Dchi.c 0 * (Dchi.q 0 : ℚ) ^ 2 / ((1 + Dchi.q 0 * m : ℕ) : ℚ) ^ 2) +
      (∑ m ∈ range (d + if kA < x then 1 else 0),
        Dchi.c 1 * (Dchi.q 1 : ℚ) ^ 2 / ((wA + Dchi.q 1 * m : ℕ) : ℚ) ^ 2) +
      (∑ m ∈ range (d + if kB < x then 1 else 0),
        Dchi.c 2 * (Dchi.q 2 : ℚ) ^ 2 / ((wB + Dchi.q 2 * m : ℕ) : ℚ) ^ 2) := by
  have hI : 1 * (p - 1) + 1 = p * 1 := by have := hp.out.pos; omega
  have hI' : ¬ (p - 1 < x) := by omega
  have hpI : p - 1 < p := by have := hp.out.pos; omega
  have hp1 : ¬ p ∣ 1 := hp.out.not_dvd_one
  have pa : ∑ k ∈ range (x + p * d), (if p ∣ Dchi.den 0 k then Dchi.c 0 * (Dchi.q 0 : ℚ) * p /
      ((Dchi.den 0 k : ℕ) : ℚ) else 0) =
      ∑ m ∈ range (d + if p - 1 < x then 1 else 0),
        Dchi.c 0 * (Dchi.q 0 : ℚ) / ((1 + Dchi.q 0 * m : ℕ) : ℚ) :=
    lf_term p (Dchi.c 0) 1 1 (p - 1) 1 x d (by norm_num) hp1 hpI hI hx
  have pb : ∑ k ∈ range (x + p * d), (if p ∣ Dchi.den 1 k then Dchi.c 1 * (Dchi.q 1 : ℚ) * p /
      ((Dchi.den 1 k : ℕ) : ℚ) else 0) =
      ∑ m ∈ range (d + if kA < x then 1 else 0),
        Dchi.c 1 * (Dchi.q 1 : ℚ) / ((wA + Dchi.q 1 * m : ℕ) : ℚ) :=
    lf_term p (Dchi.c 1) 3 1 kA wA x d (by norm_num) h3 hkA hwA hx
  have pc : ∑ k ∈ range (x + p * d), (if p ∣ Dchi.den 2 k then Dchi.c 2 * (Dchi.q 2 : ℚ) * p /
      ((Dchi.den 2 k : ℕ) : ℚ) else 0) =
      ∑ m ∈ range (d + if kB < x then 1 else 0),
        Dchi.c 2 * (Dchi.q 2 : ℚ) / ((wB + Dchi.q 2 * m : ℕ) : ℚ) :=
    lf_term p (Dchi.c 2) 2 1 kB wB x d (by norm_num) h2 hkB hwB hx
  have ea : ∑ k ∈ range (x + p * d), (if p ∣ Dchi.den 0 k then
      Dchi.c 0 * (Dchi.q 0 : ℚ) ^ 2 * (p : ℚ) ^ 2 / ((Dchi.den 0 k : ℕ) : ℚ) ^ 2 else 0) =
      ∑ m ∈ range (d + if p - 1 < x then 1 else 0),
        Dchi.c 0 * (Dchi.q 0 : ℚ) ^ 2 / ((1 + Dchi.q 0 * m : ℕ) : ℚ) ^ 2 :=
    e_term p (Dchi.c 0) 1 1 (p - 1) 1 x d (by norm_num) hp1 hpI hI hx
  have eb : ∑ k ∈ range (x + p * d), (if p ∣ Dchi.den 1 k then
      Dchi.c 1 * (Dchi.q 1 : ℚ) ^ 2 * (p : ℚ) ^ 2 / ((Dchi.den 1 k : ℕ) : ℚ) ^ 2 else 0) =
      ∑ m ∈ range (d + if kA < x then 1 else 0),
        Dchi.c 1 * (Dchi.q 1 : ℚ) ^ 2 / ((wA + Dchi.q 1 * m : ℕ) : ℚ) ^ 2 :=
    e_term p (Dchi.c 1) 3 1 kA wA x d (by norm_num) h3 hkA hwA hx
  have ec : ∑ k ∈ range (x + p * d), (if p ∣ Dchi.den 2 k then
      Dchi.c 2 * (Dchi.q 2 : ℚ) ^ 2 * (p : ℚ) ^ 2 / ((Dchi.den 2 k : ℕ) : ℚ) ^ 2 else 0) =
      ∑ m ∈ range (d + if kB < x then 1 else 0),
        Dchi.c 2 * (Dchi.q 2 : ℚ) ^ 2 / ((wB + Dchi.q 2 * m : ℕ) : ℚ) ^ 2 :=
    e_term p (Dchi.c 2) 2 1 kB wB x d (by norm_num) h2 hkB hwB hx
  rw [if_neg hI'] at pa ea
  constructor
  · unfold DigammaFrame.Lf
    rw [Fin.sum_univ_three, pa, pb, pc]
    simp
  · unfold DigammaFrame.E
    rw [Fin.sum_univ_three, ea, eb, ec]
    simp

theorem not_dvd_of_mod6 (p : ℕ) [hp : Fact p.Prime] (h : p % 6 = 1 ∨ p % 6 = 5) :
    ¬ p ∣ 2 ∧ ¬ p ∣ 3 := by
  have h2 := hp.out.two_le
  constructor <;> intro hd <;> have := Nat.le_of_dvd (by norm_num) hd <;> omega

/-- Class `p ≡ 1 (6)`, `x` above both singular positions. -/
theorem lfE_c1 (p : ℕ) [hp : Fact p.Prime] (h6 : p % 6 = 1) (x : ℕ) (hx : (p - 1) / 2 < x)
    (hxp : x < p) :
    Dchi.Lf p x = 0 ∧ Dchi.Lf p (x + p) = 1 / 72 ∧ Dchi.E p x = 1 / 6 ∧
      Dchi.E p (x + p) = 163 / 864 := by
  obtain ⟨h2, h3⟩ := not_dvd_of_mod6 p (Or.inl h6)
  have g0 := LfE_node p h2 h3 ((p - 1) / 3) 1 ((p - 1) / 2) 1 x 0 (by omega) (by omega) (by omega)
    (by omega) hxp
  have g1 := LfE_node p h2 h3 ((p - 1) / 3) 1 ((p - 1) / 2) 1 x 1 (by omega) (by omega) (by omega)
    (by omega) hxp
  have c1 : (p - 1) / 3 < x := by omega
  have c2 : (p - 1) / 2 < x := hx
  simp only [mul_zero, add_zero, mul_one, if_pos c1, if_pos c2] at g0 g1
  rw [g1.1, g1.2, g0.1, g0.2]
  simp [Dchi_c0, Dchi_c1, Dchi_c2, Dchi_q0, Dchi_q1, Dchi_q2, Finset.sum_range_succ]
  norm_num

/-- Class `p ≡ 5 (6)`, `x` below both singular positions. -/
theorem lfE_c5 (p : ℕ) [hp : Fact p.Prime] (h6 : p % 6 = 5) (x : ℕ) (hx : x ≤ (p - 1) / 2) :
    Dchi.Lf p x = 0 ∧ Dchi.Lf p (x + p) = -1 / 18 ∧ Dchi.Lf p (x + p * 2) = -23 / 360 ∧
      Dchi.E p x = 0 ∧ Dchi.E p (x + p) = -13 / 72 ∧ Dchi.E p (x + p * 2) = -2059 / 10800 := by
  have hxp : x < p := by omega
  obtain ⟨h2, h3⟩ := not_dvd_of_mod6 p (Or.inr h6)
  have g0 := LfE_node p h2 h3 ((2 * p - 1) / 3) 2 ((p - 1) / 2) 1 x 0 (by omega) (by omega)
    (by omega) (by omega) hxp
  have g1 := LfE_node p h2 h3 ((2 * p - 1) / 3) 2 ((p - 1) / 2) 1 x 1 (by omega) (by omega)
    (by omega) (by omega) hxp
  have g2 := LfE_node p h2 h3 ((2 * p - 1) / 3) 2 ((p - 1) / 2) 1 x 2 (by omega) (by omega)
    (by omega) (by omega) hxp
  have c1 : ¬ (2 * p - 1) / 3 < x := by omega
  have c2 : ¬ (p - 1) / 2 < x := by omega
  simp only [mul_zero, add_zero, mul_one, if_neg c1, if_neg c2] at g0 g1 g2
  rw [g1.1, g1.2, g0.1, g0.2, g2.1, g2.2]
  simp [Dchi_c0, Dchi_c1, Dchi_c2, Dchi_q0, Dchi_q1, Dchi_q2, Finset.sum_range_succ]
  norm_num

end CatalanCore.Uniform.Bank.Chi3Rank
