module

public import CatalanFrames.P6.NV.Main
public import CatalanFrames.P6.Lemma3

/-!
# P6 nonvanishing: `P6.hasNV` (WP11)

`HasNV (PolyFamily.ofFrame p6Frame) rule (1/2) (1/2)` for the class `ℓ ≡ 1 (6)`, with the two
members `h ∈ {(ℓ-1)/2, (ℓ+1)/2}`.  Depends on `ThmA.unit_of_lt` (Theorem A unit statement).
-/

@[expose] public section

open Finset Matrix CatalanCore

namespace CatalanFrames.P6

open CatalanFrames.P6.NV

/-- the prime rule for P6: primes `ℓ ≡ 1 (6)`, bad when `ℓ² ∥ q`. -/
def rule : PrimeRule where
  m := 6
  r := 1
  hr := isUnit_one
  Bad := fun l q => l ^ 2 ∣ q ∧ ¬ l ^ 3 ∣ q
  weight := 1 / 2

lemma den_dvd_natAbs (p q : ℤ) : ((p : ℚ) / q).den ∣ q.natAbs := by
  have h := Rat.den_dvd p q
  rw [Rat.divInt_eq_div] at h
  exact Int.natCast_dvd.1 h

lemma Ppoly_eval (h : ℕ) (r : ℚ) : (p6Frame.Ppoly h).eval r = p6Frame.P h r := by
  unfold Frame.Ppoly Frame.P
  have := (Polynomial.evalRingHom r).map_det
    (Matrix.of fun a b : Fin h => (if a = b then (Polynomial.X : Polynomial ℚ) else 0) +
      Polynomial.C (p6Frame.Mn a b))
  rw [Polynomial.coe_evalRingHom] at this
  rw [this]
  congr 1
  ext a b
  by_cases hab : a = b
  · subst hab; simp [Frame.M, Frame.MRect]
  · simp [hab, Frame.M, Frame.MRect]

theorem nv_pq (ℓ : ℕ) [Fact ℓ.Prime] (h6 : ℓ % 6 = 1) (h13 : 13 ≤ ℓ) (p q : ℤ) (hq : 0 < q)
    (hcop : IsCoprime p q) (hbad : ¬ (ℓ ^ 2 ∣ q.natAbs ∧ ¬ ℓ ^ 3 ∣ q.natAbs)) :
    ∃ t : ℕ, ℓ = 6 * t + 1 ∧
      (p6Frame.P (3 * t) ((p : ℚ) / q) ≠ 0 ∨ p6Frame.P (3 * t + 1) ((p : ℚ) / q) ≠ 0) := by
  obtain ⟨t, ht⟩ : ∃ t, ℓ = 6 * t + 1 := ⟨ℓ / 6, by omega⟩
  have ht2 : 2 ≤ t := by omega
  refine ⟨t, ht, ?_⟩
  have hℓp : ℓ.Prime := Fact.out
  by_cases hℓq : ℓ ∣ q.natAbs
  · right
    have hq' : 0 < q.natAbs := Int.natAbs_pos.2 hq.ne'
    obtain ⟨e, d, hd, hqe⟩ :=
      Nat.exists_eq_pow_mul_and_not_dvd hq'.ne' ℓ hℓp.ne_one
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
    have hqQ : (q : ℚ) = ((q.natAbs : ℕ) : ℚ) := by
      have h := Int.natAbs_of_nonneg hq.le
      rw [← Int.cast_natCast (R := ℚ) q.natAbs, h]
    have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast hdpos.ne'
    have hℓQ : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓp.ne_zero
    have hueq : (ℓ : ℚ) ^ e * ((p : ℚ) / q) = (p : ℚ) / (d : ℚ) := by
      rw [hqQ, hqe]; push_cast; field_simp
    have hu : (ℓ : ℚ) ^ e * ((p : ℚ) / q) ∈ S ℓ := by
      rw [hueq]
      have := den_dvd_natAbs p (d : ℤ)
      simp only [Int.natAbs_natCast] at this
      intro hdv
      exact hd (hdv.trans (by simpa using this))
    have hcop' : Nat.Coprime p.natAbs q.natAbs := by
      simpa [Int.isCoprime_iff_gcd_eq_one, Int.gcd] using hcop
    have hu0 : red ℓ ((ℓ : ℚ) ^ e * ((p : ℚ) / q)) ≠ 0 := by
      intro hred
      have g1 : Good ℓ ((ℓ : ℚ) ^ e * ((p : ℚ) / q) * d)
          (red ℓ ((ℓ : ℚ) ^ e * ((p : ℚ) / q)) * d) :=
        (show Good ℓ _ _ from ⟨hu, rfl⟩).mul (Good.natCast d)
      have e1 : (ℓ : ℚ) ^ e * ((p : ℚ) / q) * d = p := by rw [hueq]; field_simp
      rw [e1] at g1
      have g2 : Good ℓ (p : ℚ) (p : ZMod ℓ) := Good.intCast p
      have := g1.2.symm.trans g2.2
      rw [hred, zero_mul] at this
      have hpz : (p : ZMod ℓ) = 0 := this.symm
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hpz
      have h1 : ℓ ∣ p.natAbs := Int.natCast_dvd.1 hpz
      exact hℓp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hcop' h1 hℓq)
    have := lemma3 ht (by omega) (n := t) le_rfl he1 he2 hu hu0
    rw [show 2 * t + 1 + t = 3 * t + 1 by ring] at this
    exact this
  · have hr : ((p : ℚ) / q) ∈ S ℓ := fun hdv => hℓq (hdv.trans (den_dvd_natAbs p q))
    exact nv_integral ht ht2 hr

theorem hasNV : HasNV (PolyFamily.ofFrame p6Frame) rule (1 / 2) (1 / 2) := by
  refine ⟨1, 13, ?_⟩
  intro l hp hl13 hlm p q hq hcop hbad
  haveI : Fact l.Prime := ⟨hp⟩
  have h6 : l % 6 = 1 := by
    have h1 : (l : ZMod 6) = 1 := hlm
    have : (l : ZMod 6) = ((1 : ℕ) : ZMod 6) := by rw [h1]; simp
    simpa using (ZMod.natCast_eq_natCast_iff' _ _ _).1 this
  obtain ⟨t, ht, h⟩ := nv_pq l h6 hl13 p q hq hcop hbad
  have hlR : (l : ℝ) = 6 * t + 1 := by exact_mod_cast ht
  rcases h with h | h
  · refine ⟨3 * t, trivial, ?_, ?_, ?_⟩
    · show (1 / 2 : ℝ) * l - 1 ≤ ((3 * t : ℕ) : ℝ)
      push_cast; rw [hlR]; linarith
    · show ((3 * t : ℕ) : ℝ) ≤ (1 / 2 : ℝ) * l + 1
      push_cast; rw [hlR]; linarith
    · show (p6Frame.Ppoly (3 * t)).eval ((p : ℚ) / q) ≠ 0
      rwa [Ppoly_eval]
  · refine ⟨3 * t + 1, trivial, ?_, ?_, ?_⟩
    · show (1 / 2 : ℝ) * l - 1 ≤ ((3 * t + 1 : ℕ) : ℝ)
      push_cast; rw [hlR]; linarith
    · show ((3 * t + 1 : ℕ) : ℝ) ≤ (1 / 2 : ℝ) * l + 1
      push_cast; rw [hlR]; linarith
    · show (p6Frame.Ppoly (3 * t + 1)).eval ((p : ℚ) / q) ≠ 0
      rwa [Ppoly_eval]

end CatalanFrames.P6
