module

public import CatalanFrames.Lambda.NV
public import CatalanCore.ThmA.NoCommonRoot
public import CatalanCore.ThmA.CC
public import CatalanLambda.Main

/-!
# λ strong nonvanishing: `HasNV (ofFrame lamFrame) lamRule (3/4) (3/4)`

For `ℓ ≡ 3 (mod 4)`, `K = (ℓ+1)/4`, `ℓ ∤ den r`, one of `P_{ℓ-K}(r)`, `P_{ℓ-K-1}(r)` is nonzero.
The legacy `key_det` turns `P_h(r) = 0` into `det(z + C_s C_sᵀ) = 0` over `𝔽_ℓ` with `s = ℓ - h`;
for `s = K, K+1` the Lemma CC shortcut `u(K,K) ≠ 0` and Corollary kr forbid both.
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

theorem pair_nonvanishing (ℓ K : ℕ) [Fact ℓ.Prime] (h3 : ℓ % 4 = 3) (h7 : 7 ≤ ℓ)
    (hK : ℓ + 1 = 4 * K) (r : ℚ) (hr : ¬ ℓ ∣ r.den) :
    CatalanLambda.P (ℓ - K) r ≠ 0 ∨ CatalanLambda.P (ℓ - K - 1) r ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨c1, c2⟩ := hcon
  have hrS : r ∈ CatalanLambda.S ℓ := hr
  have k1 := CatalanLambda.key_det hK (by omega) (h := ℓ - K) (by omega) (by omega) hrS c1
  have k2 := CatalanLambda.key_det hK (by omega) (h := ℓ - K - 1) (by omega) (by omega)
    hrS c2
  have e1 : ℓ - (ℓ - K) = K := by omega
  have e2 : ℓ - (ℓ - K - 1) = K + 1 := by omega
  rw [e1, Cm_gram_eq] at k1
  rw [e2, Cm_gram_eq] at k2
  have hu : ThmA.uK (ZMod ℓ) K K ≠ 0 :=
    ThmA.uK_ne_zero_CC ℓ K K h3 h7 (by omega) (Or.inl rfl)
  have hF : ∀ n : ℕ, 0 < n → n ≤ K + K + 1 → (n : ZMod ℓ) ≠ 0 :=
    fun n hn hle => (ThmA.charGt_zmod ℓ).ne hn (by omega)
  rcases ThmA.no_common_root_of_krylov K K hF hu
    (16 * CatalanLambda.red ℓ r + CatalanLambda.cc ℓ K) with h | h
  · exact h k1
  · exact h k2

theorem hasNV_strong : HasNV (PolyFamily.ofFrame lamFrame) lamRule (3 / 4) (3 / 4) := by
  refine ⟨2, 7, fun l hl hl7 hmod p q hq hcop hbad => ?_⟩
  have h3 : l % 4 = 3 := by
    have h := (ZMod.natCast_eq_natCast_iff' l 3 4).1 (by exact_mod_cast (hmod : (l : ZMod 4) = 3))
    simpa using h
  haveI : Fact l.Prime := ⟨hl⟩
  lift q to ℕ using hq.le
  have hq0 : 0 < q := by exact_mod_cast hq
  have hcop' : Nat.Coprime p.natAbs q := by
    have := Int.isCoprime_iff_gcd_eq_one.1 hcop
    simpa [Int.gcd] using this
  simp only [Int.natAbs_natCast] at hbad
  obtain ⟨K, hK⟩ : ∃ K, l + 1 = 4 * K := ⟨(l + 1) / 4, by omega⟩
  have key : ∀ n : ℕ, l - K - 1 ≤ n → n ≤ l - K → CatalanLambda.P n ((p : ℚ) / q) ≠ 0 →
      ∃ n : ℕ, True ∧ 3 / 4 * (l : ℝ) - 2 ≤ (n : ℝ) ∧ (n : ℝ) ≤ 3 / 4 * (l : ℝ) + 2 ∧
        (PolyFamily.ofFrame lamFrame).evalQ n ((p : ℚ) / q) ≠ 0 := by
    intro n h1 h2 hP
    refine ⟨n, trivial, ?_, ?_, by rw [evalQ_eq]; exact hP⟩
    · have : 3 * l ≤ 4 * n + 8 := by omega
      have : (3 * l : ℝ) ≤ 4 * n + 8 := by exact_mod_cast this
      linarith
    · have : 4 * n ≤ 3 * l + 1 := by omega
      have : (4 * n : ℝ) ≤ 3 * l + 1 := by exact_mod_cast this
      linarith
  by_cases hdv : l ∣ q
  · refine key (l - K) (by omega) le_rfl ?_
    have e : (3 * l - 1) / 4 = l - K := by omega
    have := CatalanLambda.Measure.lemma3_pq l h3 hl7 p q hq0 hcop' hdv hbad
    rwa [e] at this
  · have hr : ¬ l ∣ ((p : ℚ) / q).den := fun hd =>
      hdv (hd.trans (by simpa using CatalanLambda.Measure.den_dvd_natAbs p q))
    rcases pair_nonvanishing l K h3 hl7 hK _ hr with h | h
    · exact key _ (by omega) le_rfl h
    · exact key _ le_rfl (by omega) h

end CatalanFrames.Lambda
