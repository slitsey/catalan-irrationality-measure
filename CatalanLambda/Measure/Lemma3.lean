import CatalanLambda.Assembly
import CatalanLambda.Measure.Irrational

/-!
# Lemma 3 (primes dividing the denominator)

Let `ℓ ≡ 3 (4)`, `ℓ ≥ 7`, `K = (ℓ+1)/4`, `K + 1 ≤ h ≤ ℓ - 1`, `r ∈ ℚ`, `e ≥ 1`, `e ≠ 2`, and
`u = ℓ^e r` an `ℓ`-adic unit.  Then `P_h(r) ≠ 0`.

Proof: scale the rows of `D (r I + M0) D` by `ℓ^e` (low) and `ℓ^{e-2}` (high).  Modulo `ℓ` the
matrix is block triangular with diagonal blocks `u I` and `I` (`e = 1`) or `u I` (`e ≥ 3`).
-/

open Finset Matrix

namespace CatalanLambda.Measure

open CatalanLambda

section L3
variable {ℓ : ℕ} [Fact ℓ.Prime] {K : ℕ}

/-- scaling exponents for the row scaling -/
def exI (K m e : ℕ) : Fin K ⊕ Fin m → ℕ := Sum.elim (fun _ => e) (fun _ => e - 2)

/-- the column scaling `D` in block form -/
def dqI (ℓ K m : ℕ) : Fin K ⊕ Fin m → ℚ := Sum.elim (fun _ => 1) (fun _ => (ℓ : ℚ))

/-- the target matrix modulo `ℓ` -/
noncomputable def Ymat (ℓ K m e : ℕ) [Fact ℓ.Prime] (ub : ZMod ℓ) :
    Matrix (Fin K ⊕ Fin m) (Fin K ⊕ Fin m) (ZMod ℓ) :=
  Matrix.fromBlocks (ub • (1 : Matrix (Fin K) (Fin K) (ZMod ℓ))) 0
    ((if e = 1 then (1 : ZMod ℓ) else 0) • (Bm ℓ K m)ᵀ)
    ((if e = 1 then (1 : ZMod ℓ) else ub) • (1 : Matrix (Fin m) (Fin m) (ZMod ℓ)))

lemma det_Ymat (m e : ℕ) (ub : ZMod ℓ) (hub : ub ≠ 0) :
    (Ymat ℓ K m e ub).det ≠ 0 := by
  unfold Ymat
  rw [Matrix.det_fromBlocks_zero₁₂, Matrix.det_smul, Matrix.det_smul]
  simp only [Matrix.det_one, mul_one, Fintype.card_fin]
  refine mul_ne_zero (pow_ne_zero _ hub) (pow_ne_zero _ ?_)
  split_ifs
  · exact one_ne_zero
  · exact hub

lemma Dq_eq_dqI {h m : ℕ} (hKm : K + m = h) (i : Fin K ⊕ Fin m) :
    Dq ℓ K ((eq' K m h hKm i : Fin h) : ℕ) = dqI ℓ K m i := by
  rcases i with a | c
  · have ha := a.2
    simp only [eq'_inl, Dq, if_pos ha, dqI, Sum.elim_inl]
  · have hc := c.2
    simp only [eq'_inr, Dq, if_neg (show ¬ (K + (c : ℕ) < K) by omega), dqI, Sum.elim_inr]

lemma Nq_sub_split {h m : ℕ} (hKm : K + m = h) (r : ℚ) (i j : Fin K ⊕ Fin m) :
    (Nq ℓ K h r).submatrix (eq' K m h hKm) (eq' K m h hKm) i j =
      (Nq ℓ K h 0).submatrix (eq' K m h hKm) (eq' K m h hKm) i j +
        (if i = j then dqI ℓ K m i ^ 2 * r else 0) := by
  simp only [Matrix.submatrix_apply, Nq, Matrix.of_apply, Dq_eq_dqI hKm]
  by_cases hij : i = j
  · subst hij
    simp only [if_true]
    ring
  · have : eq' K m h hKm i ≠ eq' K m h hKm j := fun e => hij ((eq' K m h hKm).injective e)
    simp only [if_neg this, if_neg hij]
    ring

lemma good_lpow_zero {k : ℕ} (hk : 1 ≤ k) : Good ℓ ((ℓ : ℚ) ^ k) 0 := by
  have := (Good.natCast (ℓ := ℓ) ℓ).pow' k
  rw [ZMod.natCast_self, zero_pow (by omega)] at this
  simpa using this

lemma good_lpow_one : Good ℓ ((ℓ : ℚ) ^ 0) 1 := by
  simpa using (Good.one (ℓ := ℓ))

theorem NS_good (hlK : ℓ + 1 = 4 * K) {h m : ℕ} (hKm : K + m = h) (hhl : h ≤ ℓ) {r : ℚ} {e : ℕ}
    (he1 : 1 ≤ e) (he2 : e ≠ 2) (hu : (ℓ : ℚ) ^ e * r ∈ S ℓ) (i j : Fin K ⊕ Fin m) :
    Good ℓ ((ℓ : ℚ) ^ (exI K m e i) *
        (Nq ℓ K h r).submatrix (eq' K m h hKm) (eq' K m h hKm) i j)
      (Ymat ℓ K m e (red ℓ ((ℓ : ℚ) ^ e * r)) i j) := by
  have hZ := entries_good hlK hKm hhl (Good.zero (ℓ := ℓ)) i j
  have hgu : Good ℓ ((ℓ : ℚ) ^ e * r) (red ℓ ((ℓ : ℚ) ^ e * r)) := ⟨hu, rfl⟩
  rw [Nq_sub_split hKm r i j, mul_add]
  rcases i with a | c <;> rcases j with b | d
  · -- low-low
    have g1 := (good_lpow_zero (ℓ := ℓ) he1).mul hZ
    by_cases hab : a = b
    · subst hab
      have g2 : Good ℓ ((ℓ : ℚ) ^ e * ((if (Sum.inl a : Fin K ⊕ Fin m) = Sum.inl a then
          dqI ℓ K m (Sum.inl a) ^ 2 * r else 0))) (red ℓ ((ℓ : ℚ) ^ e * r)) := by
        simp only [if_true, dqI, Sum.elim_inl, one_pow, one_mul]; exact hgu
      have := g1.add g2
      simp only [exI, Sum.elim_inl, Ymat, Matrix.fromBlocks_apply₁₁, Matrix.smul_apply,
        Matrix.one_apply_eq, smul_eq_mul, mul_one, zero_mul, zero_add] at this ⊢
      exact this
    · have hne : (Sum.inl a : Fin K ⊕ Fin m) ≠ Sum.inl b := fun e' => hab (Sum.inl_injective e')
      have := g1.add (Good.zero (ℓ := ℓ))
      simp only [exI, Sum.elim_inl, if_neg hne, mul_zero, add_zero, Ymat,
        Matrix.fromBlocks_apply₁₁, Matrix.smul_apply, Matrix.one_apply_ne hab, smul_eq_mul,
        mul_zero, zero_mul] at this ⊢
      exact this
  · -- low-high
    have g1 := (good_lpow_zero (ℓ := ℓ) he1).mul hZ
    have := g1.add (Good.zero (ℓ := ℓ))
    simp only [exI, Sum.elim_inl, Sum.inl_ne_inr, if_false, mul_zero, add_zero, Ymat,
      Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, zero_mul] at this ⊢
    exact this
  · -- high-low
    rcases (show e = 1 ∨ 3 ≤ e by omega) with h1 | h3
    · subst h1
      have g1 := (good_lpow_one (ℓ := ℓ)).mul hZ
      have := g1.add (Good.zero (ℓ := ℓ))
      simp only [exI, Sum.elim_inr, Sum.inr_ne_inl, if_false, mul_zero, add_zero, Ymat,
        Matrix.fromBlocks_apply₂₁, Matrix.smul_apply, if_true, one_smul, one_mul, zero_mul] at this ⊢
      exact this
    · have g1 := (good_lpow_zero (ℓ := ℓ) (show 1 ≤ e - 2 by omega)).mul hZ
      have := g1.add (Good.zero (ℓ := ℓ))
      simp only [exI, Sum.elim_inr, Sum.inr_ne_inl, if_false, mul_zero, add_zero, Ymat,
        Matrix.fromBlocks_apply₂₁, Matrix.smul_apply, zero_mul] at this ⊢
      have hne1 : e ≠ 1 := by omega
      simp only [hne1, if_false, zero_smul]
      exact this
  · -- high-high
    rcases (show e = 1 ∨ 3 ≤ e by omega) with h1 | h3
    · subst h1
      have g1 := (good_lpow_one (ℓ := ℓ)).mul hZ
      by_cases hcd : c = d
      · subst hcd
        have g2 : Good ℓ ((ℓ : ℚ) ^ (1 - 2) * ((if (Sum.inr c : Fin K ⊕ Fin m) = Sum.inr c then
            dqI ℓ K m (Sum.inr c) ^ 2 * r else 0))) 0 := by
          simp only [if_true, dqI, Sum.elim_inr]
          have : (ℓ : ℚ) ^ (1 - 2) * ((ℓ : ℚ) ^ 2 * r) = (ℓ : ℚ) * ((ℓ : ℚ) ^ 1 * r) := by
            norm_num; ring
          rw [this]
          have := (Good.natCast (ℓ := ℓ) ℓ).mul hgu
          simpa using this
        have := g1.add g2
        simp only [exI, Sum.elim_inr, Ymat, Matrix.fromBlocks_apply₂₂, Matrix.smul_apply,
          Matrix.one_apply_eq, smul_eq_mul, mul_one, if_true, add_zero, Matrix.fromBlocks_apply₂₂,
          Matrix.one_apply] at this ⊢
        simpa using this
      · have hne : (Sum.inr c : Fin K ⊕ Fin m) ≠ Sum.inr d := fun e' => hcd (Sum.inr_injective e')
        have := g1.add (Good.zero (ℓ := ℓ))
        simp only [exI, Sum.elim_inr, if_neg hne, mul_zero, add_zero, Ymat,
          Matrix.fromBlocks_apply₂₂, Matrix.smul_apply, Matrix.one_apply_ne hcd, smul_eq_mul,
          mul_zero, Matrix.fromBlocks_apply₂₂, Matrix.one_apply, if_false] at this ⊢
        simpa using this
    · have g1 := (good_lpow_zero (ℓ := ℓ) (show 1 ≤ e - 2 by omega)).mul hZ
      by_cases hcd : c = d
      · subst hcd
        have g2 : Good ℓ ((ℓ : ℚ) ^ (e - 2) * ((if (Sum.inr c : Fin K ⊕ Fin m) = Sum.inr c then
            dqI ℓ K m (Sum.inr c) ^ 2 * r else 0))) (red ℓ ((ℓ : ℚ) ^ e * r)) := by
          simp only [if_true, dqI, Sum.elim_inr]
          have : (ℓ : ℚ) ^ (e - 2) * ((ℓ : ℚ) ^ 2 * r) = (ℓ : ℚ) ^ e * r := by
            rw [← mul_assoc, ← pow_add]; congr 2; omega
          rw [this]; exact hgu
        have := g1.add g2
        simp only [exI, Sum.elim_inr, Ymat, Matrix.fromBlocks_apply₂₂, Matrix.smul_apply,
          Matrix.one_apply_eq, smul_eq_mul, mul_one, zero_add] at this ⊢
        have hne1 : e ≠ 1 := by omega
        simp only [hne1, if_false]
        simpa using this
      · have hne : (Sum.inr c : Fin K ⊕ Fin m) ≠ Sum.inr d := fun e' => hcd (Sum.inr_injective e')
        have := g1.add (Good.zero (ℓ := ℓ))
        simp only [exI, Sum.elim_inr, if_neg hne, mul_zero, add_zero, Ymat,
          Matrix.fromBlocks_apply₂₂, Matrix.smul_apply, Matrix.one_apply_ne hcd, smul_eq_mul,
          mul_zero] at this ⊢
        simpa using this

/-- **Lemma 3.**  -/
theorem lemma3 (hlK : ℓ + 1 = 4 * K) {h : ℕ} (hh2 : h ≤ ℓ - 1)
    (hh1 : K + 1 ≤ h) {r : ℚ} {e : ℕ} (he1 : 1 ≤ e) (he2 : e ≠ 2)
    (hu : (ℓ : ℚ) ^ e * r ∈ S ℓ) (hu0 : red ℓ ((ℓ : ℚ) ^ e * r) ≠ 0) : P h r ≠ 0 := by
  intro hP
  obtain ⟨m, hm⟩ : ∃ m, K + m = h := ⟨h - K, by omega⟩
  have hℓpos : 0 < ℓ := (Fact.out : ℓ.Prime).pos
  let NS : Matrix (Fin K ⊕ Fin m) (Fin K ⊕ Fin m) ℚ := Matrix.of fun i j =>
    (ℓ : ℚ) ^ (exI K m e i) * (Nq ℓ K h r).submatrix (eq' K m h hm) (eq' K m h hm) i j
  have hNS : NS = Matrix.diagonal (fun i => (ℓ : ℚ) ^ (exI K m e i)) *
      (Nq ℓ K h r).submatrix (eq' K m h hm) (eq' K m h hm) := by
    ext i j; simp [NS, Matrix.diagonal_mul]
  have hdet0 : NS.det = 0 := by
    rw [hNS, Matrix.det_mul, Matrix.det_submatrix_equiv_self, det_Nq, hP, mul_zero, mul_zero]
  have key := red_det NS (Ymat ℓ K m e (red ℓ ((ℓ : ℚ) ^ e * r)))
    (fun i j => NS_good hlK hm (by omega) he1 he2 hu i j)
  rw [hdet0] at key
  have h0 : (Ymat ℓ K m e (red ℓ ((ℓ : ℚ) ^ e * r))).det = 0 := by
    have := key.2
    simpa [red] using this.symm
  exact det_Ymat m e _ hu0 h0

end L3

/-- **Lemma 3 for `p/q`.**  `ℓ ≡ 3 (4)`, `ℓ ≥ 7`, `gcd(p,q)=1`, `ℓ ∣ q` and not `ℓ² ∥ q`
imply `P_{(3ℓ-1)/4}(p/q) ≠ 0`. -/
theorem lemma3_pq (ℓ : ℕ) [Fact ℓ.Prime] (h3 : ℓ % 4 = 3) (h7 : 7 ≤ ℓ) (p : ℤ) (q : ℕ)
    (hq : 0 < q) (hcop : Nat.Coprime p.natAbs q) (hℓq : ℓ ∣ q)
    (hbad : ¬ (ℓ ^ 2 ∣ q ∧ ¬ ℓ ^ 3 ∣ q)) :
    CatalanLambda.P ((3 * ℓ - 1) / 4) ((p : ℚ) / q) ≠ 0 := by
  obtain ⟨K, hK⟩ : ∃ K, ℓ + 1 = 4 * K := ⟨(ℓ + 1) / 4, by omega⟩
  obtain ⟨e, d, hd, hqe⟩ := Nat.exists_eq_pow_mul_and_not_dvd hq.ne' ℓ (Fact.out : ℓ.Prime).ne_one
  have hℓp : ℓ.Prime := Fact.out
  have he1 : 1 ≤ e := by
    by_contra h0
    have : e = 0 := by omega
    subst this
    simp at hqe
    exact hd (hqe ▸ hℓq)
  have he2 : e ≠ 2 := by
    intro h2
    subst h2
    apply hbad
    refine ⟨⟨d, hqe⟩, fun h3' => hd ?_⟩
    rw [hqe] at h3'
    have : ℓ ^ 2 * ℓ ∣ ℓ ^ 2 * d := by rw [← pow_succ]; exact h3'
    exact (Nat.dvd_of_mul_dvd_mul_left (pow_pos hℓp.pos 2) this)
  have hdpos : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · subst h0; simp at hqe; omega
    · exact h0
  have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast hdpos.ne'
  have hℓQ : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓp.ne_zero
  have hueq : (ℓ : ℚ) ^ e * ((p : ℚ) / q) = (p : ℚ) / (d : ℚ) := by
    rw [hqe]; push_cast; field_simp
  have hu : (ℓ : ℚ) ^ e * ((p : ℚ) / q) ∈ S ℓ := by
    rw [hueq]
    have := den_dvd_natAbs p (d : ℤ)
    simp only [Int.natAbs_natCast] at this
    intro hdv
    exact hd (hdv.trans (by simpa using this))
  have hu0 : red ℓ ((ℓ : ℚ) ^ e * ((p : ℚ) / q)) ≠ 0 := by
    intro hred
    have g1 : Good ℓ ((ℓ : ℚ) ^ e * ((p : ℚ) / q) * d) (red ℓ ((ℓ : ℚ) ^ e * ((p : ℚ) / q)) * d) :=
      (show Good ℓ _ _ from ⟨hu, rfl⟩).mul (Good.natCast d)
    have e1 : (ℓ : ℚ) ^ e * ((p : ℚ) / q) * d = p := by rw [hueq]; field_simp
    rw [e1] at g1
    have g2 : Good ℓ (p : ℚ) (p : ZMod ℓ) := Good.intCast p
    have := g1.2.symm.trans g2.2
    rw [hred, zero_mul] at this
    have hpz : (p : ZMod ℓ) = 0 := this.symm
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hpz
    have h1 : ℓ ∣ p.natAbs := Int.natCast_dvd.1 hpz
    exact (Nat.Prime.one_lt hℓp).ne' (Nat.eq_one_of_dvd_coprimes hcop h1 hℓq)
  exact lemma3 (K := K) hK (by omega) (by omega) he1 he2 hu hu0
