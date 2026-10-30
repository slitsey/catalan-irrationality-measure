import CatalanCore.Uniform.Bank.Lambda.TwoTerm
import CatalanCore.Uniform.Bank.Lambda.PrimeNormalisation
import CatalanCore.Uniform.Content.Wire.M3Windows
import CatalanCore.Uniform.Content.BankShared.Reindex
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Lambda
open CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Uniform
open CatalanCore.Arith.Hybrid.ChainClasses
open CatalanCore.Uniform.Content.Smith CatalanCore.Uniform.Content.Wire
open CatalanCore.Uniform.Content.BankShared

/-- All two-term poles in the compact one-level band are simple. -/
noncomputable def pipelinePoleData (a p N : ℕ) [Fact p.Prime]
    (ha : a = 1 ∨ a = 3) (hN : 4 * N < p * p) :
    Periodic.PoleData (pipelineFrame a ha) p N :=
  twoTermPoleData (pipeline_twoTerm a ha) (by omega)
    (fun t ht htN => by
      intro hd
      have hpos : 0 < 4 * t - (4 - a) := by omega
      have hle := Nat.le_of_dvd hpos hd
      have hlt : 4 * t - (4 - a) < p * p := by omega
      nlinarith [pow_two p])
    (by change (1 : ℚ) ∈ S p; exact (S p).one_mem)
    (by change red p (1 : ℚ) ≠ 0; rw [(Good.one (ℓ := p)).eq]; exact one_ne_zero)

/-- An explicit cut-free M3 window on the actual one-fifth geometry. -/
theorem FL_m3_valid (a p r A B : ℕ) (ha : a = 1 ∨ a = 3)
    (hr : r % 2 = 0) (hsq : 4 * (r + 2 * FL.borderSize r) < p * p)
    (hRA : r ≤ A) (hAB : A ≤ B) (hBN : B ≤ r + 2 * FL.borderSize r)
    (hBp : B ≤ r + p) (hmax : max A (r + 2 * FL.borderSize r - p) ≤ B)
    (hcut : ∀ x y : ℕ, A ≤ x → x < B → A ≤ y → y < B →
      NoCut (Cut p r (ttSing p 4 (4 - a))) (min (x : ℤ) y) (max (x : ℤ) y)) :
    m3dValid FL (pipelineFrame a ha) (fun _ _ => A) (fun _ _ => B) r p := by
  refine ⟨FL_hyb hr, fun [hpf : Fact p.Prime] => ?_⟩
  rw [geometry_k_eq_borderSize]
  exact ⟨pipelinePoleData a p _ ha hsq, by omega, hRA, hAB, hBN, hBp, hmax, hcut⟩

/-- The M3 price transports unchanged to either normalized sign. -/
theorem lambda_m3_gle (sgn : Bool) (depth : ℕ)
    (i : (FL.family (pipeline sgn) depth).ι)
    (hi : (FL.family (pipeline sgn) depth).Adm i)
    (p : ℕ) [Fact p.Prime] (hp29 : 29 ≤ p) (A B : ℕ)
    (hv : m3dValid FL (pipeline sgn) (fun _ _ => A) (fun _ _ => B) i.1 p) :
    GLE p (2 * i.1 + (2 * FL.borderSize i.1 -
      (B - max A (i.1 + 2 * FL.borderSize i.1 - p))))
      ((FL.family (lambdaFrame sgn) depth).Q i) := by
  have h := (m3dLayer FL (pipeline sgn) depth (fun _ _ => A) (fun _ _ => B)).gle i hi p hv
  simp only [m3dLayer, zero_mul, add_zero, m3dBase, geometry_k_eq_borderSize] at h
  exact lambda_family_gle_of_pipeline sgn depth i p hp29 _ h

/-- Integer residue gaps, including negative gap indices, provide the M3 cut condition. -/
theorem lambda_m3_gap_cut (a p r A B : ℕ) [Fact p.Prime]
    (ha : a = 1 ∨ a = 3) (hp29 : 29 ≤ p) (hodd : p % 2 = 1)
    (n0 n1 n3 : ℤ)
    (h0 : n0 * p ≤ (A : ℤ) ∧ (B : ℤ) ≤ (n0 + 1) * p)
    (h1 : n1 * p + (pole4 a p + 1 : ℕ) ≤ (A : ℤ) ∧
      (B : ℤ) ≤ (n1 + 1) * p + (pole4 a p + 1 : ℕ))
    (h3 : (r : ℤ) + n3 * p ≤ (A : ℤ) ∧ (B : ℤ) ≤ r + (n3 + 1) * p) :
    ∀ x y : ℕ, A ≤ x → x < B → A ≤ y → y < B →
      NoCut (Cut p r (ttSing p 4 (4 - a))) (min (x : ℤ) y) (max (x : ℤ) y) := by
  have hpp : p.Prime := Fact.out
  have hcopN : Nat.Coprime p 4 := by
    have h4 : ¬ p ∣ 4 := by
      intro hd
      have hle := Nat.le_of_dvd (by norm_num : 0 < 4) hd
      omega
    exact (Nat.Prime.coprime_iff_not_dvd hpp).2 h4
  have hcop : IsCoprime (p : ℤ) 4 := Nat.isCoprime_iff_coprime.2 hcopN
  have hk : (p : ℤ) ∣ 4 * (pole4 a p + 1 : ℕ) - (4 - a : ℕ) := by
    obtain ⟨hj, he, hk0, hkp, hj0⟩ := one_based_pole4 a p ha hp29 hodd
    refine ⟨root4 a p, ?_⟩
    have heZ : (4 : ℤ) * (pole4 a p + 1 : ℕ) =
        (root4 a p : ℤ) * p + (4 - a : ℕ) := by exact_mod_cast he
    linarith
  exact nocut_twoTerm_window p 4 (4 - a) r A B (pole4 a p + 1) (by omega)
    hk hcop n0 n1 n3 h0 h1 h3

#print axioms FL_m3_valid
#print axioms lambda_m3_gle
#print axioms lambda_m3_gap_cut
def m3Lower (r m p k n0 n1 n3 : ℕ) : ℕ :=
  max (max (n0 * p) (n1 * p + k)) (max (r + n3 * p) (max r (r + 2 * m - p)))
def m3Upper (r m p k n0 n1 n3 : ℕ) : ℕ :=
  min (min ((n0 + 1) * p) ((n1 + 1) * p + k))
    (min (r + (n3 + 1) * p) (min (r + 2 * m) (r + p)))

/-- Any three residue gaps give a runnable M3 supplier, including an empty intersection. -/
theorem lambda_m3_general (sgn : Bool) (depth : ℕ)
    (i : (FL.family (pipeline sgn) depth).ι)
    (hi : (FL.family (pipeline sgn) depth).Adm i) (hr : i.1 % 2 = 0)
    (p : ℕ) [Fact p.Prime] (hp29 : 29 ≤ p) (hodd : p % 2 = 1)
    (hsq : 4 * (i.1 + 2 * FL.borderSize i.1) < p * p)
    (hmp : FL.borderSize i.1 ≤ p) (n0 n1 n3 : ℕ) :
    ∃ n : ℕ, GLE p n ((FL.family (lambdaFrame sgn) depth).Q i) ∧
      (n : ℤ) ≤ ((2 * i.1 + 2 * FL.borderSize i.1 : ℕ) : ℤ) -
        ((m3Upper i.1 (FL.borderSize i.1) p (pole4 (pipelineNum sgn) p + 1) n0 n1 n3 -
          m3Lower i.1 (FL.borderSize i.1) p (pole4 (pipelineNum sgn) p + 1) n0 n1 n3 : ℕ) : ℤ) := by
  let r := i.1
  let m := FL.borderSize r
  let k := pole4 (pipelineNum sgn) p + 1
  let A := m3Lower r m p k n0 n1 n3
  let B := m3Upper r m p k n0 n1 n3
  have F1 : r ≤ A := by dsimp [A, m3Lower]; omega
  have F2 : r + 2 * m - p ≤ A := by dsimp [A, m3Lower]; omega
  have F3 : n0 * p ≤ A := by dsimp [A, m3Lower]; omega
  have F4 : n1 * p + k ≤ A := by dsimp [A, m3Lower]; omega
  have F5 : r + n3 * p ≤ A := by dsimp [A, m3Lower]; omega
  have G1 : B ≤ (n0 + 1) * p := by dsimp [B, m3Upper]; omega
  have G2 : B ≤ (n1 + 1) * p + k := by dsimp [B, m3Upper]; omega
  have G3 : B ≤ r + (n3 + 1) * p := by dsimp [B, m3Upper]; omega
  have G4 : B ≤ r + 2 * m := by dsimp [B, m3Upper]; omega
  have G5 : B ≤ r + p := by dsimp [B, m3Upper]; omega
  by_cases hAB : A ≤ B
  · have hcut := lambda_m3_gap_cut (pipelineNum sgn) p r A B
      (pipelineNum_valid sgn) hp29 hodd n0 n1 n3
      (by exact_mod_cast (show n0 * p ≤ A ∧ B ≤ (n0 + 1) * p from ⟨F3, G1⟩))
      (by exact_mod_cast (show n1 * p + k ≤ A ∧ B ≤ (n1 + 1) * p + k from ⟨F4, G2⟩))
      (by exact_mod_cast (show r + n3 * p ≤ A ∧ B ≤ r + (n3 + 1) * p from ⟨F5, G3⟩))
    have hv := FL_m3_valid (pipelineNum sgn) p r A B (pipelineNum_valid sgn) hr hsq
      F1 hAB G4 G5 (max_le hAB (F2.trans hAB)) hcut
    have hg := lambda_m3_gle sgn depth i hi p hp29 A B hv
    refine ⟨_, hg, ?_⟩
    change ((2 * r + (2 * m - (B - max A (r + 2 * m - p))) : ℕ) : ℤ) ≤
      ((2 * r + 2 * m : ℕ) : ℤ) - ((B - A : ℕ) : ℤ)
    rw [max_eq_left F2]
    omega
  · let A0 := max r (r + 2 * m - p)
    have h0r : r ≤ A0 := le_max_left _ _
    have h0N : A0 ≤ r + 2 * m := max_le (by omega) (by omega)
    have h0p : A0 ≤ r + p := max_le (by omega) (by dsimp [m, r] at *; omega)
    have h0max : max A0 (r + 2 * m - p) ≤ A0 := max_le le_rfl (le_max_right _ _)
    have hv := FL_m3_valid (pipelineNum sgn) p r A0 A0 (pipelineNum_valid sgn) hr hsq
      h0r le_rfl h0N h0p h0max (by intro x y hax hxb hay hyb; omega)
    have hg := lambda_m3_gle sgn depth i hi p hp29 A0 A0 hv
    refine ⟨_, hg, ?_⟩
    change ((2 * r + (2 * m - (A0 - max A0 (r + 2 * m - p))) : ℕ) : ℤ) ≤
      ((2 * r + 2 * m : ℕ) : ℤ) - ((B - A : ℕ) : ℤ)
    rw [max_eq_left (le_max_right r (r + 2 * m - p))]
    omega

#print axioms lambda_m3_general
end CatalanCore.Uniform.Bank.Lambda
