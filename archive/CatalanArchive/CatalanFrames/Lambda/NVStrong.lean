module

public import CatalanFrames.Lambda.NV
public import CatalanCore.ThmA.NoCommonRoot
public import CatalanCore.ThmA.UnitOfLt
public import CatalanCore.Measure.Pinned
public import CatalanCore.NT.Rules
public import CatalanLambda.Main

/-!
# λ strong (κ = 0) nonvanishing: a free pair `h ∈ {H, H+1}`

For `ℓ ≡ 3 (mod 4)`, `K = (ℓ+1)/4`, `ℓ ∤ den r` and `K ≤ s ≤ ℓ-K-2`, one of `P_{ℓ-s}(r)`,
`P_{ℓ-s-1}(r)` is nonzero.  Legacy `key_det` reduces `P_h(r) = 0` to
`det(z + C_s C_sᵀ) = 0` over `𝔽_ℓ` with `s = ℓ - h`; `ThmA.unit_of_lt` (`u(K,s) ≠ 0`) and
Corollary kr forbid both.  Hence `HasNVPin lamFamily lamDvdRule (3/2) (7/2)`.
-/

@[expose] public section

open CatalanCore Matrix

namespace CatalanFrames.Lambda

lemma Cm_eq_Cmat (l K s : ℕ) [Fact l.Prime] :
    CatalanLambda.Cm l K s = ThmA.Cmat (ZMod l) K s := by
  ext a j
  simp only [CatalanLambda.Cm, ThmA.Cmat, Matrix.of_apply]
  ring_nf

lemma Cm_gram_eq (l K s : ℕ) [Fact l.Prime] :
    CatalanLambda.Cm l K s * (CatalanLambda.Cm l K s)ᵀ = ThmA.Nmat (ZMod l) K s := by
  rw [Cm_eq_Cmat]; rfl

/-- Free-pair nonvanishing for `s ∈ [K, ℓ-K-2]`. -/
theorem pair_nonvanishing_gen (ℓ K s : ℕ) [Fact ℓ.Prime] (h7 : 7 ≤ ℓ)
    (hK : ℓ + 1 = 4 * K) (hs1 : K ≤ s) (hs2 : s + K + 2 ≤ ℓ) (r : ℚ) (hr : ¬ ℓ ∣ r.den) :
    CatalanLambda.P (ℓ - s) r ≠ 0 ∨ CatalanLambda.P (ℓ - s - 1) r ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨c1, c2⟩ := hcon
  have hrS : r ∈ CatalanLambda.S ℓ := hr
  have k1 := CatalanLambda.key_det hK (by omega) (h := ℓ - s) (by omega) (by omega) hrS c1
  have k2 := CatalanLambda.key_det hK (by omega) (h := ℓ - s - 1) (by omega) (by omega) hrS c2
  have e1 : ℓ - (ℓ - s) = s := by omega
  have e2 : ℓ - (ℓ - s - 1) = s + 1 := by omega
  rw [e1, Cm_gram_eq] at k1
  rw [e2, Cm_gram_eq] at k2
  have hu : ThmA.uK (ZMod ℓ) K s ≠ 0 :=
    ThmA.unit_of_lt_proof K s (by omega) (by omega) (by omega)
  have hF : ∀ n : ℕ, 0 < n → n ≤ K + s + 1 → (n : ZMod ℓ) ≠ 0 :=
    fun n hn hle => (ThmA.charGt_zmod ℓ).ne hn (by omega)
  rcases ThmA.no_common_root_of_krylov K s hF hu
    (16 * CatalanLambda.red ℓ r + CatalanLambda.cc ℓ K) with h | h
  · exact h k1
  · exact h k2

/-- The rule: `ℓ ≡ 3 (mod 4)`, bad iff `ℓ ∣ q` (weight 1, `s = 2`). -/
abbrev lamDvdRule : PrimeRule := PrimeRule.ofDvd 4 3 isUnit_mod4_three

theorem lamDvdRule_s : lamDvdRule.s = 2 := by
  unfold PrimeRule.s lamDvdRule PrimeRule.ofDvd
  have : Nat.totient 4 = 2 := by decide
  simp [this]

theorem hasNVPin_lam : HasNVPin (PolyFamily.ofFrame lamFrame) lamDvdRule (3 / 2) (7 / 2) := by
  refine ⟨2, 100, fun l hl hmod N hN hN1 hN2 p q hq hcop hbad => ?_⟩
  have h3 : l % 4 = 3 := by
    have hm : (l : ZMod 4) = ((3 : ℕ) : ZMod 4) := by exact_mod_cast hmod
    have h := (ZMod.natCast_eq_natCast_iff' l 3 4).1 hm
    simpa using h
  haveI : Fact l.Prime := ⟨hl⟩
  lift q to ℕ using hq.le
  have hq0 : 0 < q := by exact_mod_cast hq
  simp only [Int.natAbs_natCast] at hbad
  have hbad' : ¬ l ∣ q := hbad
  have hr : ¬ l ∣ ((p : ℚ) / q).den := fun hd =>
    hbad' (hd.trans (by simpa using CatalanLambda.Measure.den_dvd_natAbs p q))
  have hN0 : (0 : ℝ) ≤ N := by linarith
  set H : ℕ := ⌈N⌉₊ with hH
  have hH1 : N ≤ H := Nat.le_ceil N
  have hH2 : (H : ℝ) < N + 1 := Nat.ceil_lt_add_one hN0
  have n1 : 2 * l ≤ 7 * H := by
    have : (2 * l : ℝ) ≤ 7 * H := by linarith
    exact_mod_cast this
  have n2 : 3 * H ≤ 2 * l + 2 := by
    have : (3 * H : ℝ) < 2 * l + 3 := by linarith
    have : 3 * H < 2 * l + 3 := by exact_mod_cast this
    omega
  have n3 : 150 ≤ l := by
    have : (150 : ℝ) ≤ l := by linarith
    exact_mod_cast this
  obtain ⟨K, hK⟩ : ∃ K, l + 1 = 4 * K := ⟨(l + 1) / 4, by omega⟩
  have e1 : l - (l - H - 1) = H + 1 := by omega
  have e2 : l - (l - H - 1) - 1 = H := by omega
  have key : ∀ n : ℕ, N ≤ (n : ℝ) → (n : ℝ) ≤ N + 2 → CatalanLambda.P n ((p : ℚ) / q) ≠ 0 →
      ∃ n : ℕ, True ∧ N ≤ (n : ℝ) ∧ (n : ℝ) ≤ N + 2 ∧
        (PolyFamily.ofFrame lamFrame).evalQ n ((p : ℚ) / q) ≠ 0 :=
    fun n h1 h2 hP => ⟨n, trivial, h1, h2, by rw [evalQ_eq]; exact hP⟩
  rcases pair_nonvanishing_gen l K (l - H - 1) (by omega) hK (by omega) (by omega) _ hr with h | h
  · rw [e1] at h
    exact key (H + 1) (by push_cast; linarith) (by push_cast; linarith) h
  · rw [e2] at h
    exact key H hH1 (by linarith) h

end CatalanFrames.Lambda
