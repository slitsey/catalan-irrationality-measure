module

public import CatalanArchive.CatalanFrames.LambdaMirror.NV
public import CatalanArchive.CatalanFrames.Lambda.NVStrong
public import CatalanArchive.CatalanLambda.Mirror.NVMain

/-!
# λ′ strong (κ = 0) nonvanishing: `HasNVPin mirFamily mirDvdRule (3/2) (7/2)`

Mirror of `CatalanFrames.Lambda.NVStrong`: `ℓ ≡ 1 (mod 4)`, `K = (ℓ+3)/4`; legacy mirror
`key_det` gives `det((cc - 16 red) + C_s C_sᵀ) = 0`, and `unit_of_lt` plus Corollary kr apply
verbatim for `s ∈ [K, ℓ-K-2]`.
-/

@[expose] public section

open CatalanCore Matrix

namespace CatalanFrames.LambdaMirror

open CatalanFrames.Lambda (Cm_gram_eq)

theorem pair_nonvanishing_gen (ℓ K s : ℕ) [Fact ℓ.Prime] (h13 : 13 ≤ ℓ)
    (hK : ℓ + 3 = 4 * K) (hs1 : K ≤ s) (hs2 : s + K + 2 ≤ ℓ) (r : ℚ) (hr : ¬ ℓ ∣ r.den) :
    CatalanLambda.Mirror.Pbar (ℓ - s) r ≠ 0 ∨ CatalanLambda.Mirror.Pbar (ℓ - s - 1) r ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨c1, c2⟩ := hcon
  have hrS : r ∈ CatalanLambda.S ℓ := hr
  have k1 := CatalanLambda.Mirror.key_det hK (by omega) (h := ℓ - s) (by omega) (by omega) hrS c1
  have k2 := CatalanLambda.Mirror.key_det hK (by omega) (h := ℓ - s - 1) (by omega) (by omega)
    hrS c2
  have e1 : ℓ - (ℓ - s) = s := by omega
  have e2 : ℓ - (ℓ - s - 1) = s + 1 := by omega
  rw [e1, Cm_gram_eq] at k1
  rw [e2, Cm_gram_eq] at k2
  have hu : ThmA.uK (ZMod ℓ) K s ≠ 0 :=
    ThmA.unit_of_lt_proof K s (by omega) (by omega) (by omega)
  have hF : ∀ n : ℕ, 0 < n → n ≤ K + s + 1 → (n : ZMod ℓ) ≠ 0 :=
    fun n hn hle => (ThmA.charGt_zmod ℓ).ne hn (by omega)
  rcases ThmA.no_common_root_of_krylov K s hF hu
    (CatalanLambda.cc ℓ K - 16 * CatalanLambda.red ℓ r) with h | h
  · exact h k1
  · exact h k2

abbrev mirDvdRule : PrimeRule := PrimeRule.ofDvd 4 1 isUnit_mod4_one

theorem mirDvdRule_s : mirDvdRule.s = 2 := by
  unfold PrimeRule.s mirDvdRule PrimeRule.ofDvd
  have : Nat.totient 4 = 2 := by decide
  simp [this]

theorem hasNVPin_mir : HasNVPin (PolyFamily.ofFrame mirFrame) mirDvdRule (3 / 2) (7 / 2) := by
  refine ⟨2, 100, fun l hl hmod N hN hN1 hN2 p q hq hcop hbad => ?_⟩
  have h1 : l % 4 = 1 := by
    have hm : (l : ZMod 4) = ((1 : ℕ) : ZMod 4) := by
      have : (l : ZMod 4) = 1 := hmod
      simpa using this
    have h := (ZMod.natCast_eq_natCast_iff' l 1 4).1 hm
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
  obtain ⟨K, hK⟩ : ∃ K, l + 3 = 4 * K := ⟨(l + 3) / 4, by omega⟩
  have e1 : l - (l - H - 1) = H + 1 := by omega
  have e2 : l - (l - H - 1) - 1 = H := by omega
  have key : ∀ n : ℕ, N ≤ (n : ℝ) → (n : ℝ) ≤ N + 2 →
      CatalanLambda.Mirror.Pbar n ((p : ℚ) / q) ≠ 0 →
      ∃ n : ℕ, True ∧ N ≤ (n : ℝ) ∧ (n : ℝ) ≤ N + 2 ∧
        (PolyFamily.ofFrame mirFrame).evalQ n ((p : ℚ) / q) ≠ 0 :=
    fun n h1 h2 hP => ⟨n, trivial, h1, h2, by rw [evalQ_eq]; exact hP⟩
  rcases pair_nonvanishing_gen l K (l - H - 1) (by omega) hK (by omega) (by omega) _ hr with h | h
  · rw [e1] at h
    exact key (H + 1) (by push_cast; linarith) (by push_cast; linarith) h
  · rw [e2] at h
    exact key H hH1 (by linarith) h

end CatalanFrames.LambdaMirror
