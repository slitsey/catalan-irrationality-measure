import CatalanCore.Uniform.Bank.Lambda.CommonMinorRealize
import CatalanCore.Uniform.Bank.Lambda.Boundary
import CatalanCore.Uniform.Bank.Lambda.Band
import CatalanCore.Uniform.Bank.Lambda.RankSource.C3S20
import CatalanCore.Uniform.Bank.Lambda.RankPalette.C3T29
import CatalanCore.Uniform.Bank.Lambda.RankPalette.C3T32
import CatalanCore.Uniform.Bank.Lambda.RankPalette.C3T33
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Lambda.RankFibre
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.RankProducer
open CatalanCore.Uniform.Bank.Chi3Rank RankSource RankData
open scoped Classical

theorem C3S20_run0 (a p Bnd : ℕ) [Fact p.Prime] (hp4 : ¬ p ∣ 4)
    (hc : ∀ j, (D4 a).c j ∈ S p) (hpq : ∀ j, ¬ p ∣ (D4 a).q j)
    (hp3 : 3 ≤ p) (hbd : ∀ j, (D4 a).q j * Bnd + (D4 a).u j ≤ p ^ 2)
    (r m x : ℕ) (s : Finset (Fin r)) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 0) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 10 * m ≤ r + 5) (hm2 : r ≤ 10 * m + 5) (hrp : r ≤ 5 * p)
    (hleft : 8 * r ≤ 5 * p)
    (hright : 5 * p ≤ 24 * r)
    (hlo : (1 : ℤ) * x ≥ (0 : ℤ) * r + (0 : ℤ) * p + 4)
    (hhi : (1 : ℤ) * x ≤ (1 : ℤ) * r + (0 : ℤ) * p - 4)
    (k : ℕ) (ha : a = 1 ∨ a = 3) (hk : k < p) (hroot : 4 * k + a = 3 * p)
    (hgood : x ∉ deletedResidues r p s) (hden : ¬ p ∣ C3T29_den) :
    C3T29.Ok ∧ C3T29.Integral p ∧
      Realizes ((D4 a).poleSplit Bnd hc hpq hp3 hbd)
        (rowsOf r m s) (colsOf r m s) (x : ZMod p) C3T29 := by
  refine ⟨C3T29_ok, C3T29_integral p hden, ?_⟩
  apply realizes_commonMinor_D4 a p Bnd hp4 hc hpq hp3 hbd r m s k 3 x 0
    hk (by omega) hxp
    (C3S20_run0_bit r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi a k ha hroot)
    C3T29
  · exact C3S20_run0_R r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact C3S20_run0_C r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact kept_of_not_deleted r p s x hxp hgood
  · exact C3T29_palette.1
  · exact fun d hd => (C3T29_palette.2 d hd).1

theorem C3S20_run1 (a p Bnd : ℕ) [Fact p.Prime] (hp4 : ¬ p ∣ 4)
    (hc : ∀ j, (D4 a).c j ∈ S p) (hpq : ∀ j, ¬ p ∣ (D4 a).q j)
    (hp3 : 3 ≤ p) (hbd : ∀ j, (D4 a).q j * Bnd + (D4 a).u j ≤ p ^ 2)
    (r m x : ℕ) (s : Finset (Fin r)) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 1) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 10 * m ≤ r + 5) (hm2 : r ≤ 10 * m + 5) (hrp : r ≤ 5 * p)
    (hleft : 8 * r ≤ 5 * p)
    (hright : 5 * p ≤ 24 * r)
    (hlo : (1 : ℤ) * x ≥ (0 : ℤ) * r + (0 : ℤ) * p + 4)
    (hhi : (1 : ℤ) * x ≤ (1 : ℤ) * r + (0 : ℤ) * p - 4)
    (k : ℕ) (ha : a = 1 ∨ a = 3) (hk : k < p) (hroot : 4 * k + a = 3 * p)
    (hgood : x ∉ deletedResidues r p s) (hden : ¬ p ∣ C3T29_den) :
    C3T29.Ok ∧ C3T29.Integral p ∧
      Realizes ((D4 a).poleSplit Bnd hc hpq hp3 hbd)
        (rowsOf r m s) (colsOf r m s) (x : ZMod p) C3T29 := by
  refine ⟨C3T29_ok, C3T29_integral p hden, ?_⟩
  apply realizes_commonMinor_D4 a p Bnd hp4 hc hpq hp3 hbd r m s k 3 x 0
    hk (by omega) hxp
    (C3S20_run1_bit r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi a k ha hroot)
    C3T29
  · exact C3S20_run1_R r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact C3S20_run1_C r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact kept_of_not_deleted r p s x hxp hgood
  · exact C3T29_palette.1
  · exact fun d hd => (C3T29_palette.2 d hd).1

theorem C3S20_run2 (a p Bnd : ℕ) [Fact p.Prime] (hp4 : ¬ p ∣ 4)
    (hc : ∀ j, (D4 a).c j ∈ S p) (hpq : ∀ j, ¬ p ∣ (D4 a).q j)
    (hp3 : 3 ≤ p) (hbd : ∀ j, (D4 a).q j * Bnd + (D4 a).u j ≤ p ^ 2)
    (r m x : ℕ) (s : Finset (Fin r)) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 0) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 10 * m ≤ r + 5) (hm2 : r ≤ 10 * m + 5) (hrp : r ≤ 5 * p)
    (hleft : 8 * r ≤ 5 * p)
    (hright : 5 * p ≤ 24 * r)
    (hlo : (1 : ℤ) * x ≥ (1 : ℤ) * r + (0 : ℤ) * p + 4)
    (hhi : (5 : ℤ) * x ≤ (6 : ℤ) * r + (0 : ℤ) * p - 20)
    (k : ℕ) (ha : a = 1 ∨ a = 3) (hk : k < p) (hroot : 4 * k + a = 3 * p)
    (hgood : x ∉ deletedResidues r p s) (hden : ¬ p ∣ C3T32_den) :
    C3T32.Ok ∧ C3T32.Integral p ∧
      Realizes ((D4 a).poleSplit Bnd hc hpq hp3 hbd)
        (rowsOf r m s) (colsOf r m s) (x : ZMod p) C3T32 := by
  refine ⟨C3T32_ok, C3T32_integral p hden, ?_⟩
  apply realizes_commonMinor_D4 a p Bnd hp4 hc hpq hp3 hbd r m s k 3 x 0
    hk (by omega) hxp
    (C3S20_run2_bit r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi a k ha hroot)
    C3T32
  · exact C3S20_run2_R r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact C3S20_run2_C r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact kept_of_not_deleted r p s x hxp hgood
  · exact C3T32_palette.1
  · exact fun d hd => (C3T32_palette.2 d hd).1

theorem C3S20_run3 (a p Bnd : ℕ) [Fact p.Prime] (hp4 : ¬ p ∣ 4)
    (hc : ∀ j, (D4 a).c j ∈ S p) (hpq : ∀ j, ¬ p ∣ (D4 a).q j)
    (hp3 : 3 ≤ p) (hbd : ∀ j, (D4 a).q j * Bnd + (D4 a).u j ≤ p ^ 2)
    (r m x : ℕ) (s : Finset (Fin r)) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 1) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 10 * m ≤ r + 5) (hm2 : r ≤ 10 * m + 5) (hrp : r ≤ 5 * p)
    (hleft : 8 * r ≤ 5 * p)
    (hright : 5 * p ≤ 24 * r)
    (hlo : (1 : ℤ) * x ≥ (1 : ℤ) * r + (0 : ℤ) * p + 4)
    (hhi : (5 : ℤ) * x ≤ (6 : ℤ) * r + (0 : ℤ) * p - 20)
    (k : ℕ) (ha : a = 1 ∨ a = 3) (hk : k < p) (hroot : 4 * k + a = 3 * p)
    (hgood : x ∉ deletedResidues r p s) (hden : ¬ p ∣ C3T33_den) :
    C3T33.Ok ∧ C3T33.Integral p ∧
      Realizes ((D4 a).poleSplit Bnd hc hpq hp3 hbd)
        (rowsOf r m s) (colsOf r m s) (x : ZMod p) C3T33 := by
  refine ⟨C3T33_ok, C3T33_integral p hden, ?_⟩
  apply realizes_commonMinor_D4 a p Bnd hp4 hc hpq hp3 hbd r m s k 3 x 0
    hk (by omega) hxp
    (C3S20_run3_bit r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi a k ha hroot)
    C3T33
  · exact C3S20_run3_R r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact C3S20_run3_C r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact kept_of_not_deleted r p s x hxp hgood
  · exact C3T33_palette.1
  · exact fun d hd => (C3T33_palette.2 d hd).1

noncomputable def C3S20_test0 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p) : Prop :=
  x.val % 2 = 0 ∧ 4 ≤ x.val ∧
    (0 : ℤ) * r + (0 : ℤ) * p + 4 ≤ (1 : ℤ) * x.val ∧
    (1 : ℤ) * x.val ≤ (1 : ℤ) * r + (0 : ℤ) * p - 4 ∧
    x.val ∉ deletedResidues r p s
noncomputable def C3S20_test1 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p) : Prop :=
  x.val % 2 = 1 ∧ 4 ≤ x.val ∧
    (0 : ℤ) * r + (0 : ℤ) * p + 4 ≤ (1 : ℤ) * x.val ∧
    (1 : ℤ) * x.val ≤ (1 : ℤ) * r + (0 : ℤ) * p - 4 ∧
    x.val ∉ deletedResidues r p s
noncomputable def C3S20_test2 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p) : Prop :=
  x.val % 2 = 0 ∧ 4 ≤ x.val ∧
    (1 : ℤ) * r + (0 : ℤ) * p + 4 ≤ (1 : ℤ) * x.val ∧
    (5 : ℤ) * x.val ≤ (6 : ℤ) * r + (0 : ℤ) * p - 20 ∧
    x.val ∉ deletedResidues r p s
noncomputable def C3S20_test3 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p) : Prop :=
  x.val % 2 = 1 ∧ 4 ≤ x.val ∧
    (1 : ℤ) * r + (0 : ℤ) * p + 4 ≤ (1 : ℤ) * x.val ∧
    (5 : ℤ) * x.val ≤ (6 : ℤ) * r + (0 : ℤ) * p - 20 ∧
    x.val ∉ deletedResidues r p s

noncomputable def C3S20_assignment (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : a = 1 ∨ a = 3) (hp29 : 29 ≤ p) (hp4 : ¬ p ∣ 4)
    (hrp : r ≤ 5 * p) (hm1 : 10 * m ≤ r + 5) : ZMod p → FibreCert := fun x =>
  if C3S20_test0 r p s x then C3T29 else
  if C3S20_test1 r p s x then C3T29 else
  if C3S20_test2 r p s x then C3T32 else
  if C3S20_test3 r p s x then C3T33 else
  trivCert (lambdaPoleSplit a p r m ha hp29 hp4 hrp hm1) (rowsOf r m s) (colsOf r m s) x

theorem C3S20_assignment_valid (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : a = 1 ∨ a = 3) (hp29 : 29 ≤ p) (hp4 : ¬ p ∣ 4)
    (hrp : r ≤ 5 * p) (hm1 : 10 * m ≤ r + 5)
    (hr : r % 2 = 0) (hp : p % 2 = 1) (hm2 : r ≤ 10 * m + 5)
    (hleft : 8 * r ≤ 5 * p)
    (hright : 5 * p ≤ 24 * r)
    (k : ℕ) (hk : k < p) (hroot : 4 * k + a = 3 * p)
    (hden : ∀ N ∈ ([C3T29_den, C3T32_den, C3T33_den] : List ℕ), ¬ p ∣ N) (x : ZMod p) :
    (C3S20_assignment a p r m s ha hp29 hp4 hrp hm1 x).Ok ∧
    (C3S20_assignment a p r m s ha hp29 hp4 hrp hm1 x).Integral p ∧
    Realizes (lambdaPoleSplit a p r m ha hp29 hp4 hrp hm1)
      (rowsOf r m s) (colsOf r m s) x
      (C3S20_assignment a p r m s ha hp29 hp4 hrp hm1 x) := by
  have hxp : x.val < p := ZMod.val_lt x
  unfold C3S20_assignment
  split_ifs with h0 h1 h2 h3
  · obtain ⟨hpar, hx, hlo, hhi, hgood⟩ := h0
    have h := C3S20_run0 a p (r + 2 * m) hp4 (D4_coeff_mem a p)
      (D4_den_units a p hp4) (by omega) (D4_band a r m p ha hp29 hrp hm1)
      r m x.val s hr hp hpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
      k ha hk hroot hgood (hden C3T29_den (by simp))
    simpa only [lambdaPoleSplit, ZMod.natCast_zmod_val] using h
  · obtain ⟨hpar, hx, hlo, hhi, hgood⟩ := h1
    have h := C3S20_run1 a p (r + 2 * m) hp4 (D4_coeff_mem a p)
      (D4_den_units a p hp4) (by omega) (D4_band a r m p ha hp29 hrp hm1)
      r m x.val s hr hp hpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
      k ha hk hroot hgood (hden C3T29_den (by simp))
    simpa only [lambdaPoleSplit, ZMod.natCast_zmod_val] using h
  · obtain ⟨hpar, hx, hlo, hhi, hgood⟩ := h2
    have h := C3S20_run2 a p (r + 2 * m) hp4 (D4_coeff_mem a p)
      (D4_den_units a p hp4) (by omega) (D4_band a r m p ha hp29 hrp hm1)
      r m x.val s hr hp hpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
      k ha hk hroot hgood (hden C3T32_den (by simp))
    simpa only [lambdaPoleSplit, ZMod.natCast_zmod_val] using h
  · obtain ⟨hpar, hx, hlo, hhi, hgood⟩ := h3
    have h := C3S20_run3 a p (r + 2 * m) hp4 (D4_coeff_mem a p)
      (D4_den_units a p hp4) (by omega) (D4_band a r m p ha hp29 hrp hm1)
      r m x.val s hr hp hpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
      k ha hk hroot hgood (hden C3T33_den (by simp))
    simpa only [lambdaPoleSplit, ZMod.natCast_zmod_val] using h
  · exact ⟨FibreCert.triv_ok _ _ _ _, FibreCert.triv_integral _ _ _ _,
      trivCert_realizes _ _ _ _⟩

private theorem C3S20_disjoint0_2 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p)
    (hleft : 8 * r ≤ 5 * p)
    (hright : 5 * p ≤ 24 * r) :
    ¬ (C3S20_test0 r p s x ∧ C3S20_test2 r p s x) := by
  rintro ⟨⟨hpar0, hx0, hlo0, hhi0, hgood0⟩, ⟨hpar1, hx1, hlo1, hhi1, hgood1⟩⟩
  omega

private theorem C3S20_disjoint1_3 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p)
    (hleft : 8 * r ≤ 5 * p)
    (hright : 5 * p ≤ 24 * r) :
    ¬ (C3S20_test1 r p s x ∧ C3S20_test3 r p s x) := by
  rintro ⟨⟨hpar0, hx0, hlo0, hhi0, hgood0⟩, ⟨hpar1, hx1, hlo1, hhi1, hgood1⟩⟩
  omega

theorem C3S20_assignment_on_run0 (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : a = 1 ∨ a = 3) (hp29 : 29 ≤ p) (hp4 : ¬ p ∣ 4)
    (hrp : r ≤ 5 * p) (hm1 : 10 * m ≤ r + 5)
    (hleft : 8 * r ≤ 5 * p)
    (hright : 5 * p ≤ 24 * r) (x : ZMod p)
    (hi : C3S20_test0 r p s x) :
    C3S20_assignment a p r m s ha hp29 hp4 hrp hm1 x = C3T29 := by
  simp only [C3S20_assignment, if_pos hi]

theorem C3S20_assignment_on_run1 (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : a = 1 ∨ a = 3) (hp29 : 29 ≤ p) (hp4 : ¬ p ∣ 4)
    (hrp : r ≤ 5 * p) (hm1 : 10 * m ≤ r + 5)
    (hleft : 8 * r ≤ 5 * p)
    (hright : 5 * p ≤ 24 * r) (x : ZMod p)
    (hi : C3S20_test1 r p s x) :
    C3S20_assignment a p r m s ha hp29 hp4 hrp hm1 x = C3T29 := by
  have hn0 : ¬ C3S20_test0 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  simp only [C3S20_assignment, if_neg hn0, if_pos hi]

theorem C3S20_assignment_on_run2 (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : a = 1 ∨ a = 3) (hp29 : 29 ≤ p) (hp4 : ¬ p ∣ 4)
    (hrp : r ≤ 5 * p) (hm1 : 10 * m ≤ r + 5)
    (hleft : 8 * r ≤ 5 * p)
    (hright : 5 * p ≤ 24 * r) (x : ZMod p)
    (hi : C3S20_test2 r p s x) :
    C3S20_assignment a p r m s ha hp29 hp4 hrp hm1 x = C3T32 := by
  have hn0 : ¬ C3S20_test0 r p s x := fun hj => C3S20_disjoint0_2 r p s x hleft hright ⟨hj, hi⟩
  have hn1 : ¬ C3S20_test1 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  simp only [C3S20_assignment, if_neg hn0, if_neg hn1, if_pos hi]

theorem C3S20_assignment_on_run3 (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : a = 1 ∨ a = 3) (hp29 : 29 ≤ p) (hp4 : ¬ p ∣ 4)
    (hrp : r ≤ 5 * p) (hm1 : 10 * m ≤ r + 5)
    (hleft : 8 * r ≤ 5 * p)
    (hright : 5 * p ≤ 24 * r) (x : ZMod p)
    (hi : C3S20_test3 r p s x) :
    C3S20_assignment a p r m s ha hp29 hp4 hrp hm1 x = C3T33 := by
  have hn0 : ¬ C3S20_test0 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  have hn1 : ¬ C3S20_test1 r p s x := fun hj => C3S20_disjoint1_3 r p s x hleft hright ⟨hj, hi⟩
  have hn2 : ¬ C3S20_test2 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  simp only [C3S20_assignment, if_neg hn0, if_neg hn1, if_neg hn2, if_pos hi]

#print axioms C3S20_assignment_valid
#print axioms C3S20_assignment_on_run0

#print axioms C3S20_run0
end CatalanCore.Uniform.Bank.Lambda.RankFibre
