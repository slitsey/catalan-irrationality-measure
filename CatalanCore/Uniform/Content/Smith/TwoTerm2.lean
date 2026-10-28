module

public import CatalanCore.Uniform.Content.Smith.LP2Table

@[expose] public section

/-!
# Two-term frames with three singular indices `k`, `p`, `p + k` (`N ≤ 2p`): the LP1 setting

`TTCfg2` is the corrected PoleData package for nodes `t < N ≤ 2p`.  The singular indices in
`[1, N)` are among `k, p, p + k`, with pole-load residues `v = -q/j`, `1`, `v₂ = -q/(j+q)`
(`pΔ_t`) and square residues `-v²`, `1` at `k`, `p` (`p²D_t`).  `V`, `W` are the step functions of
these loads.
-/

open Finset CatalanCore CatalanCore.Arith.Hybrid CatalanCore.Arith.Hybrid.Periodic

namespace CatalanCore.Uniform.Content.Smith

variable {p : ℕ} [Fact p.Prime] {Fr : Frame} {q o N k j : ℕ}

structure TTSing2 (p q o N k j : ℕ) : Prop where
  hqp : q < p
  hk : q * k = j * p + o
  hk0 : 0 < k
  hkp : k < p
  hj0 : 0 < j
  hN2 : N ≤ 2 * p

/-- The residue `v₂ = -q/(j+q)` of the pole at `p + k`. -/
def vk2 (p q j : ℕ) : ZMod p := -((q : ZMod p) * (((j + q : ℕ) : ZMod p))⁻¹)

lemma TTSing2.toSing (S : TTSing2 p q o N k j) : TTSing p q o (min N (p + k)) k j where
  hqp := S.hqp
  hk := S.hk
  hk0 := S.hk0
  hkp := S.hkp
  hj0 := S.hj0
  hNk := min_le_right _ _

lemma TTSing2.j_ne (T : TwoTermData Fr q o) (S : TTSing2 p q o N k j) : (j : ZMod p) ≠ 0 :=
  (S.toSing).j_ne T

lemma TTSing2.k_ne (S : TTSing2 p q o N k j) : (k : ZMod p) ≠ 0 := (S.toSing).k_ne

lemma TTSing2.q_ne (T : TwoTermData Fr q o) (S : TTSing2 p q o N k j) : (q : ZMod p) ≠ 0 :=
  (S.toSing).q_ne T

lemma TTSing2.vk_ne (T : TwoTermData Fr q o) (S : TTSing2 p q o N k j) : vk p q j ≠ 0 :=
  (S.toSing).vk_ne T

/-- In `[1, N)` the singular indices are among `k`, `p`, `p + k`. -/
lemma TTSing2.sing_iff (T : TwoTermData Fr q o) (S : TTSing2 p q o N k j) {t : ℕ} (ht : 1 ≤ t)
    (htN : t < N) : ttSing p q o (t : ℤ) ↔ t = k ∨ t = p ∨ t = p + k := by
  have hp := (Fact.out : p.Prime)
  have hk := S.hk; have hkp := S.hkp; have hN2 := S.hN2; have ho := T.o_pos
  have hoq := T.o_lt
  have hoqt : o ≤ q * t := by nlinarith
  constructor
  · intro h
    rw [ttSing_nat T ht] at h
    rcases h with ⟨c, hc⟩ | ⟨c, hc⟩
    · right; left
      rcases c with _ | _ | c
      · omega
      · omega
      · have : p * (c + 1 + 1) ≥ p * 2 := Nat.mul_le_mul_left p (by omega)
        omega
    · have h1 : (q : ℤ) * t - o = p * c := by
        have := congrArg (fun x : ℕ => (x : ℤ)) hc
        simp only [Nat.cast_mul] at this
        rw [Nat.cast_sub hoqt] at this; push_cast at this; linarith
      have h2 : (q : ℤ) * k = j * p + o := by exact_mod_cast hk
      have hd : (p : ℤ) ∣ (q : ℤ) * ((t : ℤ) - k) := ⟨c - j, by linear_combination h1 - h2⟩
      have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
      rcases hpz.dvd_or_dvd hd with h3 | h3
      · exfalso
        have : p ∣ q := Int.natCast_dvd_natCast.1 h3
        have := Nat.le_of_dvd (by omega) this
        have := S.hqp; omega
      · obtain ⟨c', hc'⟩ := h3
        have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
        have hlt : (t : ℤ) < 2 * p := by exact_mod_cast (by omega : t < 2 * p)
        have hgt : (-(p : ℤ)) < (t : ℤ) - k := by
          have : (k : ℤ) < p := by exact_mod_cast hkp
          have : (0 : ℤ) < t := by exact_mod_cast (by omega : 0 < t)
          linarith
        have hkpz : (k : ℤ) < p := by exact_mod_cast hkp
        rcases lt_trichotomy c' 0 with hneg | hzero | hpos
        · exfalso; nlinarith
        · left; rw [hzero, mul_zero] at hc'; omega
        · right; right
          have hc1 : c' = 1 := by
            by_contra hne
            have : 2 ≤ c' := by omega
            nlinarith
          rw [hc1, mul_one] at hc'; omega
  · rintro (h | h | h)
    · rw [ttSing_nat T ht, h]; right
      rw [Nat.sub_eq_of_eq_add hk]; exact dvd_mul_left p j
    · rw [ttSing_nat T ht, h]; left; exact dvd_rfl
    · rw [ttSing_nat T ht, h]; right
      have : q * (p + k) - o = (j + q) * p := by
        have e : q * (p + k) = q * p + q * k := by ring
        rw [e, hk]
        have : j * p + o + q * p - o = (j + q) * p := by
          rw [add_mul]; omega
        omega
      rw [this]; exact dvd_mul_left p _

structure TTCfg2 (Fr : Frame) (p q o N k j : ℕ) [Fact p.Prime] : Prop where
  tt : TwoTermData Fr q o
  sg : TTSing2 p q o N k j
  hsq : ∀ t, 1 ≤ t → t < N → ¬ p ^ 2 ∣ q * t - o
  hnm : Fr.norm ∈ CatalanCore.S p
  hnm0 : red p Fr.norm ≠ 0

lemma TTCfg2.hN (C : TTCfg2 Fr p q o N k j) : N ≤ p * p := by
  have := C.sg.hN2; have := (Fact.out : p.Prime).two_le
  nlinarith

lemma TTCfg2.hN' (C : TTCfg2 Fr p q o N k j) (h : N ≤ 2 * p) (hp3 : 3 ≤ p) : N < p * p := by
  nlinarith

/-- The `Periodic.PoleData` of the configuration. -/
noncomputable def TTCfg2.D (C : TTCfg2 Fr p q o N k j) : Periodic.PoleData Fr p N :=
  twoTermPoleData C.tt C.hN C.hsq C.hnm C.hnm0

lemma ratCast_k2 {C : TTCfg2 Fr p q o N k j} : (q : ℚ) * k - o = j * p := by
  have h : ((q * k : ℕ) : ℚ) = ((j * p + o : ℕ) : ℚ) := by rw [C.sg.hk]
  push_cast at h; linarith

lemma TTCfg2.dv_k (C : TTCfg2 Fr p q o N k j) : C.D.dv k = vk p q j := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hj0 : (j : ℚ) ≠ 0 := by exact_mod_cast C.sg.hj0.ne'
  have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast C.sg.hk0.ne'
  have hΔ : (p : ℚ) * Fr.Delta k = (p : ℚ) * ((k : ℚ))⁻¹ - (q : ℚ) / j := by
    rw [C.tt.delta_eq k C.sg.hk0, ratCast_k2 (C := C)]
    field_simp
  have g1 := (Good.inv (Good.natCast (ℓ := p) k) C.sg.k_ne).ell_mul
  have g2 := (Good.natCast (ℓ := p) q).div (Good.natCast (ℓ := p) j) (C.sg.j_ne C.tt)
  have g := g1.sub g2
  show red p ((p : ℚ) * Fr.Delta k) = _
  rw [hΔ, g.2]
  unfold vk; ring

lemma TTCfg2.sv_k (C : TTCfg2 Fr p q o N k j) : C.D.sv k = -(vk p q j) ^ 2 := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hj0 : (j : ℚ) ≠ 0 := by exact_mod_cast C.sg.hj0.ne'
  have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast C.sg.hk0.ne'
  have hD : (p : ℚ) ^ 2 * Fr.Dsq k = (p : ℚ) * ((p : ℚ) * ((k : ℚ))⁻¹ ^ 2) - ((q : ℚ) / j) ^ 2 := by
    rw [C.tt.dsq_eq k C.sg.hk0, ratCast_k2 (C := C)]
    field_simp
  have g0 := (Good.inv (Good.natCast (ℓ := p) k) C.sg.k_ne).pow' 2
  have g1 := (g0.ell_mul).ell_mul
  have g2 := ((Good.natCast (ℓ := p) q).div (Good.natCast (ℓ := p) j) (C.sg.j_ne C.tt)).pow' 2
  have g := g1.sub g2
  show red p ((p : ℚ) ^ 2 * Fr.Dsq k) = _
  rw [hD, g.2]
  unfold vk; ring

lemma TTCfg2.dv_p (C : TTCfg2 Fr p q o N k j) : C.D.dv p = 1 := by
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).pos
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hd := not_dvd_qp_sub C.tt C.sg.hqp
  have hΔ : (p : ℚ) * Fr.Delta p = 1 - (q : ℚ) * ((p : ℚ) * (((q * p - o : ℕ) : ℚ))⁻¹) := by
    rw [C.tt.delta_eq p hp1, ← C.tt.cast_sub hp1]
    field_simp
  have g1 := (Good.inv (Good.natCast (ℓ := p) (q * p - o)) (natCast_ne_zero_of_not_dvd hd)).ell_mul
  have g := (Good.one (ℓ := p)).sub ((Good.natCast (ℓ := p) q).mul g1)
  show red p ((p : ℚ) * Fr.Delta p) = _
  rw [hΔ, g.2]; ring

lemma TTCfg2.sv_p (C : TTCfg2 Fr p q o N k j) : C.D.sv p = 1 := by
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).pos
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hd := not_dvd_qp_sub C.tt C.sg.hqp
  have hD : (p : ℚ) ^ 2 * Fr.Dsq p = 1 - (q : ℚ) ^ 2 *
      ((p : ℚ) * ((p : ℚ) * ((((q * p - o : ℕ) : ℚ))⁻¹) ^ 2)) := by
    rw [C.tt.dsq_eq p hp1, ← C.tt.cast_sub hp1]
    field_simp
  have g0 := (Good.inv (Good.natCast (ℓ := p) (q * p - o)) (natCast_ne_zero_of_not_dvd hd)).pow' 2
  have g1 := (g0.ell_mul).ell_mul
  have g := (Good.one (ℓ := p)).sub ((Good.natCast (ℓ := p) q).pow' 2 |>.mul g1)
  show red p ((p : ℚ) ^ 2 * Fr.Dsq p) = _
  rw [hD, g.2]; ring

/-- `j + q` is a unit mod `p` once `p + k < N` (corrected PoleData condition at `t = p + k`). -/
lemma TTCfg2.jq_ne (C : TTCfg2 Fr p q o N k j) (hpk : p + k < N) : ((j + q : ℕ) : ZMod p) ≠ 0 := by
  have hsq := C.hsq (p + k) (by have := C.sg.hk0; omega) hpk
  have e : q * (p + k) - o = (j + q) * p := by
    have e1 : q * (p + k) = q * p + q * k := by ring
    rw [e1, C.sg.hk]
    have : j * p + o + q * p - o = (j + q) * p := by
      rw [add_mul]; omega
    omega
  rw [e] at hsq
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro h
  apply hsq
  rw [pow_two]
  exact mul_dvd_mul_right h p

lemma TTCfg2.dv_pk (C : TTCfg2 Fr p q o N k j) (hpk : p + k < N) : C.D.dv (p + k) = vk2 p q j := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hjq := C.jq_ne hpk
  have hjqQ : ((j + q : ℕ) : ℚ) ≠ 0 := by
    have : j + q ≠ 0 := by have := C.sg.hj0; omega
    exact_mod_cast this
  have hpk0 : ((p + k : ℕ) : ℚ) ≠ 0 := by
    have : p + k ≠ 0 := by have := C.sg.hk0; omega
    exact_mod_cast this
  have h1 : 1 ≤ p + k := by have := C.sg.hk0; omega
  have hkQ : (q : ℚ) * ((p + k : ℕ) : ℚ) - o = ((j + q : ℕ) : ℚ) * p := by
    push_cast
    have := ratCast_k2 (C := C)
    linarith
  have hpkz : (((p + k : ℕ)) : ZMod p) ≠ 0 := by
    rw [Nat.cast_add, ZMod.natCast_self, zero_add]; exact C.sg.k_ne
  have hΔ : (p : ℚ) * Fr.Delta (p + k) =
      (p : ℚ) * (((p + k : ℕ) : ℚ))⁻¹ - (q : ℚ) / ((j + q : ℕ) : ℚ) := by
    rw [C.tt.delta_eq (p + k) h1, hkQ]
    field_simp
  have g1 := (Good.inv (Good.natCast (ℓ := p) (p + k)) hpkz).ell_mul
  have g2 := (Good.natCast (ℓ := p) q).div (Good.natCast (ℓ := p) (j + q)) hjq
  have g := g1.sub g2
  show red p ((p : ℚ) * Fr.Delta (p + k)) = _
  rw [hΔ, g.2]
  unfold vk2; rw [div_eq_mul_inv]; ring

lemma TTCfg2.dv_val (C : TTCfg2 Fr p q o N k j) {t : ℕ} (ht : 1 ≤ t) (htN : t < N) :
    C.D.dv t = (if t = k then vk p q j else 0) + (if t = p then 1 else 0) +
      (if t = p + k then vk2 p q j else 0) := by
  have hkp := C.sg.hkp
  by_cases h1 : t = k
  · have h2 : t ≠ p := by omega
    have h3 : t ≠ p + k := by omega
    subst h1
    rw [if_pos rfl, if_neg h2, if_neg h3, add_zero, add_zero]; exact C.dv_k
  · by_cases h2 : t = p
    · have h3 : t ≠ p + k := by have := C.sg.hk0; omega
      subst h2
      rw [if_neg h1, if_pos rfl, if_neg h3, zero_add, add_zero]; exact C.dv_p
    · by_cases h3 : t = p + k
      · subst h3
        rw [if_neg h1, if_neg h2, if_pos rfl, zero_add, zero_add]; exact C.dv_pk htN
      · rw [if_neg h1, if_neg h2, if_neg h3, add_zero, add_zero]
        refine C.D.dv_zero ht htN ?_
        intro hs
        rcases (C.sg.sing_iff C.tt ht htN).1 hs with h | h | h
        · exact h1 h
        · exact h2 h
        · exact h3 h

lemma TTCfg2.sv_val (C : TTCfg2 Fr p q o N k j) {t : ℕ} (ht : 1 ≤ t) (htN : t < N)
    (htpk : t < p + k) :
    C.D.sv t = (if t = k then -(vk p q j) ^ 2 else 0) + (if t = p then 1 else 0) := by
  have hkp := C.sg.hkp
  by_cases h1 : t = k
  · have h2 : t ≠ p := by omega
    subst h1
    rw [if_pos rfl, if_neg h2, add_zero]; exact C.sv_k
  · by_cases h2 : t = p
    · subst h2
      rw [if_neg h1, if_pos rfl, zero_add]; exact C.sv_p
    · rw [if_neg h1, if_neg h2, add_zero]
      refine C.D.sv_zero ht htN ?_
      intro hs
      rcases (C.sg.sing_iff C.tt ht htN).1 hs with h | h | h
      · exact h1 h
      · exact h2 h
      · omega

/-- **Pole-load prefix** `V(A) = [k ≤ A] v + [p ≤ A] + [p + k ≤ A] v₂`, `A < N`. -/
lemma TTCfg2.V_val (C : TTCfg2 Fr p q o N k j) {A : ℕ} (hA : A < N) :
    C.D.V A = (if k ≤ A then vk p q j else 0) + (if p ≤ A then 1 else 0) +
      (if p + k ≤ A then vk2 p q j else 0) := by
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).pos
  have hk1 : 1 ≤ k := C.sg.hk0
  unfold Periodic.PoleData.V
  rw [Finset.sum_congr rfl (fun t ht => C.dv_val (mem_Icc.1 ht).1
    (by have := (mem_Icc.1 ht).2; omega)), Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [mem_Icc]
  by_cases h1 : k ≤ A <;> by_cases h2 : p ≤ A <;> by_cases h3 : p + k ≤ A <;>
    simp [h1, h2, h3, hk1, hp1, show 1 ≤ p + k by omega]

lemma TTCfg2.W_val (C : TTCfg2 Fr p q o N k j) {A : ℕ} (hA : A < N) (hApk : A < p + k) :
    C.D.W A = (if k ≤ A then -(vk p q j) ^ 2 else 0) + (if p ≤ A then 1 else 0) := by
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).pos
  have hk1 : 1 ≤ k := C.sg.hk0
  unfold Periodic.PoleData.W
  rw [Finset.sum_congr rfl (fun t ht => C.sv_val (mem_Icc.1 ht).1
    (by have := (mem_Icc.1 ht).2; omega) (by have := (mem_Icc.1 ht).2; omega)),
    Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [mem_Icc]
  by_cases h1 : k ≤ A <;> by_cases h2 : p ≤ A <;> simp [h1, h2, hk1, hp1]

/-! ### Regular pairs below `k` -/

lemma TTCfg2.nonsing (C : TTCfg2 Fr p q o N k j) {t : ℕ} (ht : 1 ≤ t) (htN : t < N) (htk : t < k) :
    ¬ p ∣ t ∧ ¬ p ∣ q * t - o := by
  have h := (C.sg.sing_iff C.tt ht htN)
  have hkp := C.sg.hkp
  have : ¬ ttSing p q o (t : ℤ) := by
    intro hs; rcases h.1 hs with h1 | h1 | h1 <;> omega
  rw [ttSing_nat C.tt ht] at this
  push Not at this
  exact this

lemma TTCfg2.cast_d (C : TTCfg2 Fr p q o N k j) {t : ℕ} (ht : 1 ≤ t) :
    (((q * t - o : ℕ)) : ZMod p) = (q : ZMod p) * ((t : ZMod p) - (k : ZMod p)) := by
  have hoqt : o ≤ q * t := by have := C.tt.o_lt; nlinarith
  have hk : ((q * k : ℕ) : ZMod p) = ((j * p + o : ℕ) : ZMod p) := by rw [C.sg.hk]
  push_cast at hk
  rw [ZMod.natCast_self, mul_zero, zero_add] at hk
  rw [Nat.cast_sub hoqt]; push_cast
  linear_combination hk

lemma TTCfg2.good_Delta_reg (C : TTCfg2 Fr p q o N k j) {t : ℕ} (ht : 1 ≤ t) (htN : t < N)
    (htk : t < k) :
    Good p (Fr.Delta t) (((t : ZMod p))⁻¹ - ((t : ZMod p) - (k : ZMod p))⁻¹) := by
  obtain ⟨h1, h2⟩ := C.nonsing ht htN htk
  have hq := C.sg.q_ne C.tt
  have e : Fr.Delta t = ((t : ℚ))⁻¹ - (q : ℚ) * (((q * t - o : ℕ) : ℚ))⁻¹ := by
    rw [C.tt.delta_eq t ht, C.tt.cast_sub ht]; ring
  rw [e]
  have g1 := (Good.natCast (ℓ := p) t).inv (natCast_ne_zero_of_not_dvd h1)
  have g2 := (Good.natCast (ℓ := p) (q * t - o)).inv (natCast_ne_zero_of_not_dvd h2)
  have g := g1.sub ((Good.natCast (ℓ := p) q).mul g2)
  refine g.congr ?_
  rw [C.cast_d ht, mul_inv, mul_inv_cancel_left₀ hq]

lemma TTCfg2.good_Dsq_reg (C : TTCfg2 Fr p q o N k j) {t : ℕ} (ht : 1 ≤ t) (htN : t < N)
    (htk : t < k) :
    Good p (Fr.Dsq t)
      ((((t : ZMod p))⁻¹) ^ 2 - (((t : ZMod p) - (k : ZMod p))⁻¹) ^ 2) := by
  obtain ⟨h1, h2⟩ := C.nonsing ht htN htk
  have hq := C.sg.q_ne C.tt
  have e : Fr.Dsq t = (((t : ℚ))⁻¹) ^ 2 - (q : ℚ) ^ 2 * ((((q * t - o : ℕ) : ℚ))⁻¹) ^ 2 := by
    rw [C.tt.dsq_eq t ht, ← C.tt.cast_sub ht, one_div, inv_pow, div_eq_mul_inv, inv_pow]
  rw [e]
  have g1 := ((Good.natCast (ℓ := p) t).inv (natCast_ne_zero_of_not_dvd h1)).pow' 2
  have g2 := ((Good.natCast (ℓ := p) (q * t - o)).inv (natCast_ne_zero_of_not_dvd h2)).pow' 2
  have g := g1.sub (((Good.natCast (ℓ := p) q).pow' 2).mul g2)
  refine g.congr ?_
  rw [C.cast_d ht, mul_inv, mul_pow, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hq, one_pow,
    one_mul]

lemma TTCfg2.good_norm (C : TTCfg2 Fr p q o N k j) : Good p Fr.norm (red p Fr.norm) :=
  good_red C.hnm

lemma TTCfg2.good_Mn_reg (C : TTCfg2 Fr p q o N k j) {A B : ℕ} (hAB : A < B) (hBN : B < N)
    (hBk : B < k) :
    Good p (Fr.Mn A B)
      ((red p Fr.norm)⁻¹ * (((B : ZMod p) - A)⁻¹ * (F2 k B - F2 k A))) := by
  have hkp := C.sg.hkp
  have hd : ((B : ZMod p) - A) ≠ 0 := zmod_sub_ne_zero_of_lt hAB (by omega)
  rw [Mn_ord Fr hAB]
  have gn := C.good_norm.inv C.hnm0
  have gd := ((Good.natCast (ℓ := p) B).sub (Good.natCast (ℓ := p) A)).inv hd
  have gs : Good p (∑ t ∈ Ioc A B, Fr.Delta t)
      (∑ t ∈ Ioc A B, (((t : ZMod p))⁻¹ - ((t : ZMod p) - (k : ZMod p))⁻¹)) :=
    Good.sum _ _ _ fun t ht => by
      have := mem_Ioc.1 ht
      exact C.good_Delta_reg (by omega) (by omega) (by omega)
  have g := (gn.mul gd).mul gs
  rw [F2_sub hAB.le]
  refine (g.congr' ?_).congr ?_
  · simp only [one_div]
  · ring

lemma TTCfg2.good_Mn_diag_reg (C : TTCfg2 Fr p q o N k j) {A : ℕ} (hAN : A < N) (hAk : A < k) :
    Good p (Fr.Mn A A) ((red p Fr.norm)⁻¹ * E2 k A) := by
  rw [Mn_dg]
  have gn := (C.good_norm.inv C.hnm0).neg
  have gs : Good p (∑ t ∈ Icc 1 A, Fr.Dsq t)
      (∑ t ∈ Icc 1 A, ((((t : ZMod p))⁻¹) ^ 2 - (((t : ZMod p) - (k : ZMod p))⁻¹) ^ 2)) :=
    Good.sum _ _ _ fun t ht => by
      have := mem_Icc.1 ht
      exact C.good_Dsq_reg this.1 (by omega) (by omega)
  have g := gn.mul gs
  refine (g.congr' ?_).congr ?_
  · simp only [one_div]
  · unfold E2
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => by ring

end CatalanCore.Uniform.Content.Smith
