module

public import CatalanFrames.HybCommon.Trop
public import CatalanFrames.HybGen.FamilySum
public import CatalanFrames.HybGen.GoodClassBand

@[expose] public section

/-! # Parity bridge for the modulus-four tropical instance

Prepared alongside the original API. All dual estimates below are thin
specializations of HybGen; no old table or certificate is changed.
-/

open Filter CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid

namespace CatalanFrames.HybCommon.GenericTropBridge

variable {Fr : Frame} {I : HybInst Fr} {o : ℕ}

lemma XG_eq (r p : ℕ) : XG I r p = HybGen.XGm I r (r / 8) p := rfl
lemma WG_eq (r p : ℕ) : WG I r p = HybGen.WGm I r (r / 8) p := rfl

lemma D1x (r p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) :
    XG I r p ≤ 2 * r + 2 * (r / 8) - min ((r / 8) % p) (p - (r / 8) % p) :=
  HybGen.XGm_D1x I r (r / 8) p hp h2

lemma D2 (T : TropFacts I o) (r p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p)
    (hl : r / 4 < p) (hu : p ≤ r) :
    ∃ u L : ℕ, I.cd.kq p + p ≤ u + r ∧ u ≤ r ∧ L ≤ u ∧ L ≤ 2 * (r / 8) ∧
      XG I r p ≤ 2 * (r - u) + 2 * (r / 8) + L :=
  HybGen.XGm_D2 T.toLevelFacts r (r / 8) p hp h5 (by omega) hu
    ((XG_kq_le T p hp h5).trans hu)

lemma D45 (T : TropFacts I o) (r p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (hr : r < p) :
    XG I r p ≤ 2 * (r - I.cd.kq p) + 2 * (r / 8) + (2 * (r / 8) - (p - r)) :=
  HybGen.XGm_D45 T.toLevelFacts r (r / 8) p hp h5 hr (by omega)

lemma D6 (T : TropFacts I o) (r p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p)
    (hN : r + 2 * (r / 8) ≤ p) (hk : r ≤ I.cd.kq p) :
    XG I r p ≤ 2 * (r / 8) - (I.cd.kq p - r) :=
  HybGen.XGm_D6 T.toLevelFacts r (r / 8) p hp h5 hN hk

/-- The modulus-four dictionary is a thin instance on good primes only. -/
lemma band_j1 (T : TropFacts I o) :
    HybGen.GoodClassBand (cJ1 o) (fun p => 5 ≤ p) I.cd.kq 4 1 0 3 := by
  intro p hp h5 hc
  have hm := mod_j1 T hc
  have ho3 : o ≤ 3 := by rcases T.ho with rfl | rfl <;> omega
  have hmod : (p + o) % 4 = 0 := by
    rcases T.ho with rfl | rfl <;> omega
  have hdiv := Nat.div_add_mod (p + o) 4
  rw [T.kq1 p hp h5 hm]
  omega

lemma band_j3 (T : TropFacts I o) :
    HybGen.GoodClassBand (cJ3 o) (fun p => 5 ≤ p) I.cd.kq 4 3 0 3 := by
  intro p hp h5 hc
  have hm := mod_j3 T hc
  have ho3 : o ≤ 3 := by rcases T.ho with rfl | rfl <;> omega
  have hmod : (3 * p + o) % 4 = 0 := by
    rcases T.ho with rfl | rfl <;> omega
  have hdiv := Nat.div_add_mod (3 * p + o) 4
  rw [T.kq3 p hp h5 hm]
  omega

/-- Offset changes only permute the two modulus-four class assignments. -/
lemma class_swap : cJ1 1 = cJ3 3 ∧ cJ3 1 = cJ1 3 := by decide

/-- The old floor-sized family is an instance of the generic window theorem.
Unlike the thirds admissibility window, this uses m=floor(r/8), not ceil(r/8). -/
theorem class_sum_floor {M : ℕ} [NeZero M] {c : ZMod M} (hc : IsUnit c)
    (I : HybInst Fr) (s : ℝ) (hs : 0 < s)
    (ll : List Piece) (hl : Chain s ll)
    (hcover : ∀ᶠ r : ℕ in atTop, ∀ P ∈ ll, Covers c (WG I r) r P)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop,
      clsSum M c (WG I r) 0 ⌊lastEnd s ll * r⌋₊ ≤
        (r : ℝ)^2 * (((9 / 4 : ℝ) * s + listInt ll) / (M.totient : ℝ) + ε) := by
  have hw (r m : ℕ) (hm : m = r / 8) : (m : ℝ) ≤ (1 / 8 : ℝ) * r + 0 := by
    subst m
    have hq : 8 * (r / 8) ≤ r := Nat.mul_div_le r 8
    have hqR : (8 : ℝ) * (r / 8 : ℕ) ≤ r := by exact_mod_cast hq
    nlinarith
  have hcovers : ∀ᶠ r : ℕ in atTop, ∀ m, m = r / 8 →
      ∀ P ∈ ll, Covers c (HybGen.WGm I r m) r P := by
    filter_upwards [hcover] with r hr
    intro m hm
    subst m
    exact hr
  have hh := HybGen.class_sum_of_affine_window hc I (fun r m => m = r / 8)
    (1 / 8) 0 s (by norm_num) hs hw ll hl hcovers hε
  filter_upwards [hh] with r hr
  convert hr (r / 8) rfl using 1 <;> first | rfl | norm_num

#print axioms class_sum_floor
#print axioms D2
#print axioms D45
#print axioms D6

end CatalanFrames.HybCommon.GenericTropBridge
