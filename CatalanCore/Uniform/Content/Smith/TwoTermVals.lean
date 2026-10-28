module

public import CatalanCore.Uniform.Content.Smith.TwoTerm

@[expose] public section

/-!
# Pole-load prefixes `V`, `W` of a two-term frame with two singular indices `k < p`

`TTCfg` bundles the hypotheses of the corrected PoleData condition.  For `A < N`:

  `V(A) = [k ≤ A]·v_k + [p ≤ A]`,   `W(A) = -[k ≤ A]·v_k² + [p ≤ A]`,   `v_k = -q/j`.
-/

open Finset CatalanCore CatalanCore.Arith.Hybrid CatalanCore.Arith.Hybrid.Periodic

namespace CatalanCore.Uniform.Content.Smith

variable {p : ℕ} [Fact p.Prime] {Fr : Frame} {q o N k j : ℕ}

/-- The corrected PoleData hypotheses for a two-term frame with singular indices `k`, `p` below
`N ≤ p + k`.  The condition `p² ∤ q t - o` (`1 ≤ t < N`) is the corrected one. -/
structure TTCfg (Fr : Frame) (p q o N k j : ℕ) [Fact p.Prime] : Prop where
  tt : TwoTermData Fr q o
  sg : TTSing p q o N k j
  hsq : ∀ t, 1 ≤ t → t < N → ¬ p ^ 2 ∣ q * t - o
  hnm : Fr.norm ∈ CatalanCore.S p
  hnm0 : red p Fr.norm ≠ 0

lemma TTCfg.hN (C : TTCfg Fr p q o N k j) : N ≤ p * p := by
  have := C.sg.hNk; have := C.sg.hkp; have := (Fact.out : p.Prime).two_le
  nlinarith

/-- The `Periodic.PoleData` of the configuration. -/
noncomputable def TTCfg.D (C : TTCfg Fr p q o N k j) : Periodic.PoleData Fr p N :=
  twoTermPoleData C.tt C.hN C.hsq C.hnm C.hnm0

lemma ratCast_k {C : TTCfg Fr p q o N k j} : (q : ℚ) * k - o = j * p := by
  have h : ((q * k : ℕ) : ℚ) = ((j * p + o : ℕ) : ℚ) := by rw [C.sg.hk]
  push_cast at h; linarith

lemma TTCfg.dv_k (C : TTCfg Fr p q o N k j) : C.D.dv k = vk p q j := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hj0 : (j : ℚ) ≠ 0 := by exact_mod_cast C.sg.hj0.ne'
  have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast C.sg.hk0.ne'
  have hΔ : (p : ℚ) * Fr.Delta k = (p : ℚ) * ((k : ℚ))⁻¹ - (q : ℚ) / j := by
    rw [C.tt.delta_eq k C.sg.hk0, ratCast_k (C := C)]
    field_simp
  have g1 := (Good.inv (Good.natCast (ℓ := p) k) C.sg.k_ne).ell_mul
  have g2 := (Good.natCast (ℓ := p) q).div (Good.natCast (ℓ := p) j) (C.sg.j_ne C.tt)
  have g := g1.sub g2
  show red p ((p : ℚ) * Fr.Delta k) = _
  rw [hΔ, g.2]
  unfold vk; ring

lemma TTCfg.sv_k (C : TTCfg Fr p q o N k j) : C.D.sv k = -(vk p q j) ^ 2 := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hj0 : (j : ℚ) ≠ 0 := by exact_mod_cast C.sg.hj0.ne'
  have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast C.sg.hk0.ne'
  have hD : (p : ℚ) ^ 2 * Fr.Dsq k = (p : ℚ) * ((p : ℚ) * ((k : ℚ))⁻¹ ^ 2) - ((q : ℚ) / j) ^ 2 := by
    rw [C.tt.dsq_eq k C.sg.hk0, ratCast_k (C := C)]
    field_simp
  have g0 := (Good.inv (Good.natCast (ℓ := p) k) C.sg.k_ne).pow' 2
  have g1 := (g0.ell_mul).ell_mul
  have g2 := ((Good.natCast (ℓ := p) q).div (Good.natCast (ℓ := p) j) (C.sg.j_ne C.tt)).pow' 2
  have g := g1.sub g2
  show red p ((p : ℚ) ^ 2 * Fr.Dsq k) = _
  rw [hD, g.2]
  unfold vk; ring

lemma not_dvd_qp_sub {Fr : Frame} (T : TwoTermData Fr q o) (hqp : q < p) :
    ¬ p ∣ q * p - o := by
  intro h
  have hoq : o ≤ q * p := by have := T.o_lt; nlinarith
  have h2 : p ∣ q * p - (q * p - o) := Nat.dvd_sub (dvd_mul_left p q) h
  rw [Nat.sub_sub_self hoq] at h2
  have := Nat.le_of_dvd T.o_pos h2
  have := T.o_lt; omega

lemma TTCfg.dv_p (C : TTCfg Fr p q o N k j) : C.D.dv p = 1 := by
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

lemma TTCfg.sv_p (C : TTCfg Fr p q o N k j) : C.D.sv p = 1 := by
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

lemma TTCfg.k_lt_p (C : TTCfg Fr p q o N k j) : k < p := C.sg.hkp

/-- Prefix values of the pole loads: `dv`. -/
lemma TTCfg.dv_val (C : TTCfg Fr p q o N k j) {t : ℕ} (ht : 1 ≤ t) (htN : t < N) :
    C.D.dv t = (if t = k then vk p q j else 0) + (if t = p then 1 else 0) := by
  by_cases h1 : t = k
  · have h2 : t ≠ p := by have := C.sg.hkp; omega
    subst h1
    rw [if_pos rfl, if_neg h2, add_zero]; exact C.dv_k
  · by_cases h2 : t = p
    · subst h2
      rw [if_neg h1, if_pos rfl, zero_add]; exact C.dv_p
    · rw [if_neg h1, if_neg h2, add_zero]
      refine C.D.dv_zero ht htN ?_
      intro hs
      exact (C.sg.sing_iff C.tt ht htN).1 hs |>.elim h1 h2

lemma TTCfg.sv_val (C : TTCfg Fr p q o N k j) {t : ℕ} (ht : 1 ≤ t) (htN : t < N) :
    C.D.sv t = (if t = k then -(vk p q j) ^ 2 else 0) + (if t = p then 1 else 0) := by
  by_cases h1 : t = k
  · have h2 : t ≠ p := by have := C.sg.hkp; omega
    subst h1
    rw [if_pos rfl, if_neg h2, add_zero]; exact C.sv_k
  · by_cases h2 : t = p
    · subst h2
      rw [if_neg h1, if_pos rfl, zero_add]; exact C.sv_p
    · rw [if_neg h1, if_neg h2, add_zero]
      refine C.D.sv_zero ht htN ?_
      intro hs
      exact (C.sg.sing_iff C.tt ht htN).1 hs |>.elim h1 h2

/-- **The pole-load prefix** `V(A) = [k ≤ A] v_k + [p ≤ A]` for `A < N`. -/
lemma TTCfg.V_val (C : TTCfg Fr p q o N k j) {A : ℕ} (hA : A < N) :
    C.D.V A = (if k ≤ A then vk p q j else 0) + (if p ≤ A then 1 else 0) := by
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).pos
  unfold Periodic.PoleData.V
  rw [Finset.sum_congr rfl (fun t ht => C.dv_val (mem_Icc.1 ht).1
    (by have := (mem_Icc.1 ht).2; omega)), Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [mem_Icc]
  have hk1 : 1 ≤ k := C.sg.hk0
  by_cases h1 : k ≤ A <;> by_cases h2 : p ≤ A <;> simp [h1, h2, hk1, hp1]

lemma TTCfg.W_val (C : TTCfg Fr p q o N k j) {A : ℕ} (hA : A < N) :
    C.D.W A = (if k ≤ A then -(vk p q j) ^ 2 else 0) + (if p ≤ A then 1 else 0) := by
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).pos
  unfold Periodic.PoleData.W
  rw [Finset.sum_congr rfl (fun t ht => C.sv_val (mem_Icc.1 ht).1
    (by have := (mem_Icc.1 ht).2; omega)), Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [mem_Icc]
  have hk1 : 1 ≤ k := C.sg.hk0
  by_cases h1 : k ≤ A <;> by_cases h2 : p ≤ A <;> simp [h1, h2, hk1, hp1]

end CatalanCore.Uniform.Content.Smith
