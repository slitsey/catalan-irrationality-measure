import CatalanCore.Uniform.Bank.Sevenths.CommonMinorRealize
import CatalanCore.Uniform.Content.RankProducer.Boundary
import CatalanCore.Uniform.Bank.Sevenths.Band
import CatalanCore.Uniform.Bank.Sevenths.RankSource.C1S19
import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C1
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankFibre
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.RankProducer
open CatalanCore.Uniform.Content.RankProducer.Geometry RankSource RankData
open scoped Classical

theorem C1S19_run0 (a p Bnd : ℕ) [Fact p.Prime] (hp7 : ¬ p ∣ 7)
    (hc : ∀ j, (D7Frame a).c j ∈ S p) (hpq : ∀ j, ¬ p ∣ (D7Frame a).q j)
    (hp3 : 3 ≤ p) (hbd : ∀ j, (D7Frame a).q j * Bnd + (D7Frame a).u j ≤ p ^ 2)
    (r m x : ℕ) (s : Finset (Fin r)) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 0) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 12 * m ≤ r + 6) (hm2 : r ≤ 12 * m + 6) (hrp : r ≤ 6 * p)
    (hleft : 1 * r ≤ 1 * p)
    (hright : 48 * p ≤ 49 * r)
    (hlo : (1 : ℤ) * x ≥ (0 : ℤ) * r + (0 : ℤ) * p + 4)
    (hhi : (7 : ℤ) * x ≤ (0 : ℤ) * r + (1 : ℤ) * p - 28)
    (k : ℕ) (ha : 1 ≤ a ∧ a ≤ 6) (hk : k < p) (hroot : 7 * k + a = 1 * p)
    (hgood : x ∉ deletedResidues r p s) (hden : ¬ p ∣ C1T33_den) :
    C1T33.Ok ∧ C1T33.Integral p ∧
      Realizes ((D7Frame a).poleSplit Bnd hc hpq hp3 hbd)
        (rowsOf r m s) (colsOf r m s) (x : ZMod p) C1T33 := by
  refine ⟨C1T33_ok, C1T33_integral p hden, ?_⟩
  apply realizes_commonMinor_D7Frame a p Bnd hp7 hc hpq hp3 hbd r m s k 1 x 0
    hk (by omega) hxp
    (C1S19_run0_bit r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi a k ha hroot)
    C1T33
  · exact C1S19_run0_R r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact C1S19_run0_C r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact kept_of_not_deleted r p s x hxp hgood
  · exact C1T33_palette.1
  · exact fun d hd => (C1T33_palette.2 d hd).1

theorem C1S19_run1 (a p Bnd : ℕ) [Fact p.Prime] (hp7 : ¬ p ∣ 7)
    (hc : ∀ j, (D7Frame a).c j ∈ S p) (hpq : ∀ j, ¬ p ∣ (D7Frame a).q j)
    (hp3 : 3 ≤ p) (hbd : ∀ j, (D7Frame a).q j * Bnd + (D7Frame a).u j ≤ p ^ 2)
    (r m x : ℕ) (s : Finset (Fin r)) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 1) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 12 * m ≤ r + 6) (hm2 : r ≤ 12 * m + 6) (hrp : r ≤ 6 * p)
    (hleft : 1 * r ≤ 1 * p)
    (hright : 48 * p ≤ 49 * r)
    (hlo : (1 : ℤ) * x ≥ (0 : ℤ) * r + (0 : ℤ) * p + 4)
    (hhi : (7 : ℤ) * x ≤ (0 : ℤ) * r + (1 : ℤ) * p - 28)
    (k : ℕ) (ha : 1 ≤ a ∧ a ≤ 6) (hk : k < p) (hroot : 7 * k + a = 1 * p)
    (hgood : x ∉ deletedResidues r p s) (hden : ¬ p ∣ C1T34_den) :
    C1T34.Ok ∧ C1T34.Integral p ∧
      Realizes ((D7Frame a).poleSplit Bnd hc hpq hp3 hbd)
        (rowsOf r m s) (colsOf r m s) (x : ZMod p) C1T34 := by
  refine ⟨C1T34_ok, C1T34_integral p hden, ?_⟩
  apply realizes_commonMinor_D7Frame a p Bnd hp7 hc hpq hp3 hbd r m s k 1 x 0
    hk (by omega) hxp
    (C1S19_run1_bit r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi a k ha hroot)
    C1T34
  · exact C1S19_run1_R r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact C1S19_run1_C r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact kept_of_not_deleted r p s x hxp hgood
  · exact C1T34_palette.1
  · exact fun d hd => (C1T34_palette.2 d hd).1

theorem C1S19_run2 (a p Bnd : ℕ) [Fact p.Prime] (hp7 : ¬ p ∣ 7)
    (hc : ∀ j, (D7Frame a).c j ∈ S p) (hpq : ∀ j, ¬ p ∣ (D7Frame a).q j)
    (hp3 : 3 ≤ p) (hbd : ∀ j, (D7Frame a).q j * Bnd + (D7Frame a).u j ≤ p ^ 2)
    (r m x : ℕ) (s : Finset (Fin r)) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 0) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 12 * m ≤ r + 6) (hm2 : r ≤ 12 * m + 6) (hrp : r ≤ 6 * p)
    (hleft : 1 * r ≤ 1 * p)
    (hright : 48 * p ≤ 49 * r)
    (hlo : (7 : ℤ) * x ≥ (0 : ℤ) * r + (1 : ℤ) * p + 28)
    (hhi : (6 : ℤ) * x ≤ (7 : ℤ) * r + (-6 : ℤ) * p - 24)
    (k : ℕ) (ha : 1 ≤ a ∧ a ≤ 6) (hk : k < p) (hroot : 7 * k + a = 1 * p)
    (hgood : x ∉ deletedResidues r p s) (hden : ¬ p ∣ C1T29_den) :
    C1T29.Ok ∧ C1T29.Integral p ∧
      Realizes ((D7Frame a).poleSplit Bnd hc hpq hp3 hbd)
        (rowsOf r m s) (colsOf r m s) (x : ZMod p) C1T29 := by
  refine ⟨C1T29_ok, C1T29_integral p hden, ?_⟩
  apply realizes_commonMinor_D7Frame a p Bnd hp7 hc hpq hp3 hbd r m s k 1 x 1
    hk (by omega) hxp
    (C1S19_run2_bit r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi a k ha hroot)
    C1T29
  · exact C1S19_run2_R r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact C1S19_run2_C r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact kept_of_not_deleted r p s x hxp hgood
  · exact C1T29_palette.1
  · exact fun d hd => (C1T29_palette.2 d hd).1

theorem C1S19_run3 (a p Bnd : ℕ) [Fact p.Prime] (hp7 : ¬ p ∣ 7)
    (hc : ∀ j, (D7Frame a).c j ∈ S p) (hpq : ∀ j, ¬ p ∣ (D7Frame a).q j)
    (hp3 : 3 ≤ p) (hbd : ∀ j, (D7Frame a).q j * Bnd + (D7Frame a).u j ≤ p ^ 2)
    (r m x : ℕ) (s : Finset (Fin r)) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 1) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 12 * m ≤ r + 6) (hm2 : r ≤ 12 * m + 6) (hrp : r ≤ 6 * p)
    (hleft : 1 * r ≤ 1 * p)
    (hright : 48 * p ≤ 49 * r)
    (hlo : (7 : ℤ) * x ≥ (0 : ℤ) * r + (1 : ℤ) * p + 28)
    (hhi : (6 : ℤ) * x ≤ (7 : ℤ) * r + (-6 : ℤ) * p - 24)
    (k : ℕ) (ha : 1 ≤ a ∧ a ≤ 6) (hk : k < p) (hroot : 7 * k + a = 1 * p)
    (hgood : x ∉ deletedResidues r p s) (hden : ¬ p ∣ C1T30_den) :
    C1T30.Ok ∧ C1T30.Integral p ∧
      Realizes ((D7Frame a).poleSplit Bnd hc hpq hp3 hbd)
        (rowsOf r m s) (colsOf r m s) (x : ZMod p) C1T30 := by
  refine ⟨C1T30_ok, C1T30_integral p hden, ?_⟩
  apply realizes_commonMinor_D7Frame a p Bnd hp7 hc hpq hp3 hbd r m s k 1 x 1
    hk (by omega) hxp
    (C1S19_run3_bit r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi a k ha hroot)
    C1T30
  · exact C1S19_run3_R r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact C1S19_run3_C r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact kept_of_not_deleted r p s x hxp hgood
  · exact C1T30_palette.1
  · exact fun d hd => (C1T30_palette.2 d hd).1

theorem C1S19_run4 (a p Bnd : ℕ) [Fact p.Prime] (hp7 : ¬ p ∣ 7)
    (hc : ∀ j, (D7Frame a).c j ∈ S p) (hpq : ∀ j, ¬ p ∣ (D7Frame a).q j)
    (hp3 : 3 ≤ p) (hbd : ∀ j, (D7Frame a).q j * Bnd + (D7Frame a).u j ≤ p ^ 2)
    (r m x : ℕ) (s : Finset (Fin r)) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 0) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 12 * m ≤ r + 6) (hm2 : r ≤ 12 * m + 6) (hrp : r ≤ 6 * p)
    (hleft : 1 * r ≤ 1 * p)
    (hright : 48 * p ≤ 49 * r)
    (hlo : (6 : ℤ) * x ≥ (7 : ℤ) * r + (-6 : ℤ) * p + 24)
    (hhi : (1 : ℤ) * x ≤ (1 : ℤ) * r + (0 : ℤ) * p - 4)
    (k : ℕ) (ha : 1 ≤ a ∧ a ≤ 6) (hk : k < p) (hroot : 7 * k + a = 1 * p)
    (hgood : x ∉ deletedResidues r p s) (hden : ¬ p ∣ C1T32_den) :
    C1T32.Ok ∧ C1T32.Integral p ∧
      Realizes ((D7Frame a).poleSplit Bnd hc hpq hp3 hbd)
        (rowsOf r m s) (colsOf r m s) (x : ZMod p) C1T32 := by
  refine ⟨C1T32_ok, C1T32_integral p hden, ?_⟩
  apply realizes_commonMinor_D7Frame a p Bnd hp7 hc hpq hp3 hbd r m s k 1 x 1
    hk (by omega) hxp
    (C1S19_run4_bit r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi a k ha hroot)
    C1T32
  · exact C1S19_run4_R r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact C1S19_run4_C r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact kept_of_not_deleted r p s x hxp hgood
  · exact C1T32_palette.1
  · exact fun d hd => (C1T32_palette.2 d hd).1

theorem C1S19_run5 (a p Bnd : ℕ) [Fact p.Prime] (hp7 : ¬ p ∣ 7)
    (hc : ∀ j, (D7Frame a).c j ∈ S p) (hpq : ∀ j, ¬ p ∣ (D7Frame a).q j)
    (hp3 : 3 ≤ p) (hbd : ∀ j, (D7Frame a).q j * Bnd + (D7Frame a).u j ≤ p ^ 2)
    (r m x : ℕ) (s : Finset (Fin r)) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 1) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 12 * m ≤ r + 6) (hm2 : r ≤ 12 * m + 6) (hrp : r ≤ 6 * p)
    (hleft : 1 * r ≤ 1 * p)
    (hright : 48 * p ≤ 49 * r)
    (hlo : (6 : ℤ) * x ≥ (7 : ℤ) * r + (-6 : ℤ) * p + 24)
    (hhi : (1 : ℤ) * x ≤ (1 : ℤ) * r + (0 : ℤ) * p - 4)
    (k : ℕ) (ha : 1 ≤ a ∧ a ≤ 6) (hk : k < p) (hroot : 7 * k + a = 1 * p)
    (hgood : x ∉ deletedResidues r p s) (hden : ¬ p ∣ C1T32_den) :
    C1T32.Ok ∧ C1T32.Integral p ∧
      Realizes ((D7Frame a).poleSplit Bnd hc hpq hp3 hbd)
        (rowsOf r m s) (colsOf r m s) (x : ZMod p) C1T32 := by
  refine ⟨C1T32_ok, C1T32_integral p hden, ?_⟩
  apply realizes_commonMinor_D7Frame a p Bnd hp7 hc hpq hp3 hbd r m s k 1 x 1
    hk (by omega) hxp
    (C1S19_run5_bit r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi a k ha hroot)
    C1T32
  · exact C1S19_run5_R r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact C1S19_run5_C r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact kept_of_not_deleted r p s x hxp hgood
  · exact C1T32_palette.1
  · exact fun d hd => (C1T32_palette.2 d hd).1

theorem C1S19_run6 (a p Bnd : ℕ) [Fact p.Prime] (hp7 : ¬ p ∣ 7)
    (hc : ∀ j, (D7Frame a).c j ∈ S p) (hpq : ∀ j, ¬ p ∣ (D7Frame a).q j)
    (hp3 : 3 ≤ p) (hbd : ∀ j, (D7Frame a).q j * Bnd + (D7Frame a).u j ≤ p ^ 2)
    (r m x : ℕ) (s : Finset (Fin r)) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 0) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 12 * m ≤ r + 6) (hm2 : r ≤ 12 * m + 6) (hrp : r ≤ 6 * p)
    (hleft : 1 * r ≤ 1 * p)
    (hright : 48 * p ≤ 49 * r)
    (hlo : (1 : ℤ) * x ≥ (1 : ℤ) * r + (0 : ℤ) * p + 4)
    (hhi : (1 : ℤ) * x ≤ (0 : ℤ) * r + (1 : ℤ) * p - 4)
    (k : ℕ) (ha : 1 ≤ a ∧ a ≤ 6) (hk : k < p) (hroot : 7 * k + a = 1 * p)
    (hgood : x ∉ deletedResidues r p s) (hden : ¬ p ∣ C1T35_den) :
    C1T35.Ok ∧ C1T35.Integral p ∧
      Realizes ((D7Frame a).poleSplit Bnd hc hpq hp3 hbd)
        (rowsOf r m s) (colsOf r m s) (x : ZMod p) C1T35 := by
  refine ⟨C1T35_ok, C1T35_integral p hden, ?_⟩
  apply realizes_commonMinor_D7Frame a p Bnd hp7 hc hpq hp3 hbd r m s k 1 x 1
    hk (by omega) hxp
    (C1S19_run6_bit r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi a k ha hroot)
    C1T35
  · exact C1S19_run6_R r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact C1S19_run6_C r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact kept_of_not_deleted r p s x hxp hgood
  · exact C1T35_palette.1
  · exact fun d hd => (C1T35_palette.2 d hd).1

theorem C1S19_run7 (a p Bnd : ℕ) [Fact p.Prime] (hp7 : ¬ p ∣ 7)
    (hc : ∀ j, (D7Frame a).c j ∈ S p) (hpq : ∀ j, ¬ p ∣ (D7Frame a).q j)
    (hp3 : 3 ≤ p) (hbd : ∀ j, (D7Frame a).q j * Bnd + (D7Frame a).u j ≤ p ^ 2)
    (r m x : ℕ) (s : Finset (Fin r)) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 1) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 12 * m ≤ r + 6) (hm2 : r ≤ 12 * m + 6) (hrp : r ≤ 6 * p)
    (hleft : 1 * r ≤ 1 * p)
    (hright : 48 * p ≤ 49 * r)
    (hlo : (1 : ℤ) * x ≥ (1 : ℤ) * r + (0 : ℤ) * p + 4)
    (hhi : (1 : ℤ) * x ≤ (0 : ℤ) * r + (1 : ℤ) * p - 4)
    (k : ℕ) (ha : 1 ≤ a ∧ a ≤ 6) (hk : k < p) (hroot : 7 * k + a = 1 * p)
    (hgood : x ∉ deletedResidues r p s) (hden : ¬ p ∣ C1T36_den) :
    C1T36.Ok ∧ C1T36.Integral p ∧
      Realizes ((D7Frame a).poleSplit Bnd hc hpq hp3 hbd)
        (rowsOf r m s) (colsOf r m s) (x : ZMod p) C1T36 := by
  refine ⟨C1T36_ok, C1T36_integral p hden, ?_⟩
  apply realizes_commonMinor_D7Frame a p Bnd hp7 hc hpq hp3 hbd r m s k 1 x 1
    hk (by omega) hxp
    (C1S19_run7_bit r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi a k ha hroot)
    C1T36
  · exact C1S19_run7_R r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact C1S19_run7_C r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact kept_of_not_deleted r p s x hxp hgood
  · exact C1T36_palette.1
  · exact fun d hd => (C1T36_palette.2 d hd).1

noncomputable def C1S19_test0 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p) : Prop :=
  x.val % 2 = 0 ∧ 4 ≤ x.val ∧
    (0 : ℤ) * r + (0 : ℤ) * p + 4 ≤ (1 : ℤ) * x.val ∧
    (7 : ℤ) * x.val ≤ (0 : ℤ) * r + (1 : ℤ) * p - 28 ∧
    x.val ∉ deletedResidues r p s
noncomputable def C1S19_test1 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p) : Prop :=
  x.val % 2 = 1 ∧ 4 ≤ x.val ∧
    (0 : ℤ) * r + (0 : ℤ) * p + 4 ≤ (1 : ℤ) * x.val ∧
    (7 : ℤ) * x.val ≤ (0 : ℤ) * r + (1 : ℤ) * p - 28 ∧
    x.val ∉ deletedResidues r p s
noncomputable def C1S19_test2 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p) : Prop :=
  x.val % 2 = 0 ∧ 4 ≤ x.val ∧
    (0 : ℤ) * r + (1 : ℤ) * p + 28 ≤ (7 : ℤ) * x.val ∧
    (6 : ℤ) * x.val ≤ (7 : ℤ) * r + (-6 : ℤ) * p - 24 ∧
    x.val ∉ deletedResidues r p s
noncomputable def C1S19_test3 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p) : Prop :=
  x.val % 2 = 1 ∧ 4 ≤ x.val ∧
    (0 : ℤ) * r + (1 : ℤ) * p + 28 ≤ (7 : ℤ) * x.val ∧
    (6 : ℤ) * x.val ≤ (7 : ℤ) * r + (-6 : ℤ) * p - 24 ∧
    x.val ∉ deletedResidues r p s
noncomputable def C1S19_test4 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p) : Prop :=
  x.val % 2 = 0 ∧ 4 ≤ x.val ∧
    (7 : ℤ) * r + (-6 : ℤ) * p + 24 ≤ (6 : ℤ) * x.val ∧
    (1 : ℤ) * x.val ≤ (1 : ℤ) * r + (0 : ℤ) * p - 4 ∧
    x.val ∉ deletedResidues r p s
noncomputable def C1S19_test5 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p) : Prop :=
  x.val % 2 = 1 ∧ 4 ≤ x.val ∧
    (7 : ℤ) * r + (-6 : ℤ) * p + 24 ≤ (6 : ℤ) * x.val ∧
    (1 : ℤ) * x.val ≤ (1 : ℤ) * r + (0 : ℤ) * p - 4 ∧
    x.val ∉ deletedResidues r p s
noncomputable def C1S19_test6 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p) : Prop :=
  x.val % 2 = 0 ∧ 4 ≤ x.val ∧
    (1 : ℤ) * r + (0 : ℤ) * p + 4 ≤ (1 : ℤ) * x.val ∧
    (1 : ℤ) * x.val ≤ (0 : ℤ) * r + (1 : ℤ) * p - 4 ∧
    x.val ∉ deletedResidues r p s
noncomputable def C1S19_test7 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p) : Prop :=
  x.val % 2 = 1 ∧ 4 ≤ x.val ∧
    (1 : ℤ) * r + (0 : ℤ) * p + 4 ≤ (1 : ℤ) * x.val ∧
    (1 : ℤ) * x.val ≤ (0 : ℤ) * r + (1 : ℤ) * p - 4 ∧
    x.val ∉ deletedResidues r p s

noncomputable def C1S19_assignment (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : 1 ≤ a ∧ a ≤ 6) (hp64 : 64 ≤ p) (hp7 : ¬ p ∣ 7)
    (hrp : r ≤ 6 * p) (hm1 : 12 * m ≤ r + 6) : ZMod p → FibreCert := fun x =>
  if C1S19_test0 r p s x then C1T33 else
  if C1S19_test1 r p s x then C1T34 else
  if C1S19_test2 r p s x then C1T29 else
  if C1S19_test3 r p s x then C1T30 else
  if C1S19_test4 r p s x then C1T32 else
  if C1S19_test5 r p s x then C1T32 else
  if C1S19_test6 r p s x then C1T35 else
  if C1S19_test7 r p s x then C1T36 else
  trivCert (seventhsPoleSplit a p r m ha hp64 hp7 hrp hm1) (rowsOf r m s) (colsOf r m s) x

theorem C1S19_assignment_valid (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : 1 ≤ a ∧ a ≤ 6) (hp64 : 64 ≤ p) (hp7 : ¬ p ∣ 7)
    (hrp : r ≤ 6 * p) (hm1 : 12 * m ≤ r + 6)
    (hr : r % 2 = 0) (hp : p % 2 = 1) (hm2 : r ≤ 12 * m + 6)
    (hleft : 1 * r ≤ 1 * p)
    (hright : 48 * p ≤ 49 * r)
    (k : ℕ) (hk : k < p) (hroot : 7 * k + a = 1 * p)
    (hden : ∀ N ∈ ([C1T29_den, C1T30_den, C1T32_den, C1T33_den, C1T34_den, C1T35_den, C1T36_den] : List ℕ), ¬ p ∣ N) (x : ZMod p) :
    (C1S19_assignment a p r m s ha hp64 hp7 hrp hm1 x).Ok ∧
    (C1S19_assignment a p r m s ha hp64 hp7 hrp hm1 x).Integral p ∧
    Realizes (seventhsPoleSplit a p r m ha hp64 hp7 hrp hm1)
      (rowsOf r m s) (colsOf r m s) x
      (C1S19_assignment a p r m s ha hp64 hp7 hrp hm1 x) := by
  have hxp : x.val < p := ZMod.val_lt x
  unfold C1S19_assignment
  split_ifs with h0 h1 h2 h3 h4 h5 h6 h7
  · obtain ⟨hpar, hx, hlo, hhi, hgood⟩ := h0
    have h := C1S19_run0 a p (r + 2 * m) hp7 (D7Frame_coeff_mem a p)
      (D7Frame_den_units a p hp7) (by omega) (D7Frame_band a r m p ha hp64 hrp hm1)
      r m x.val s hr hp hpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
      k ha hk hroot hgood (hden C1T33_den (by simp))
    simpa only [seventhsPoleSplit, ZMod.natCast_zmod_val] using h
  · obtain ⟨hpar, hx, hlo, hhi, hgood⟩ := h1
    have h := C1S19_run1 a p (r + 2 * m) hp7 (D7Frame_coeff_mem a p)
      (D7Frame_den_units a p hp7) (by omega) (D7Frame_band a r m p ha hp64 hrp hm1)
      r m x.val s hr hp hpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
      k ha hk hroot hgood (hden C1T34_den (by simp))
    simpa only [seventhsPoleSplit, ZMod.natCast_zmod_val] using h
  · obtain ⟨hpar, hx, hlo, hhi, hgood⟩ := h2
    have h := C1S19_run2 a p (r + 2 * m) hp7 (D7Frame_coeff_mem a p)
      (D7Frame_den_units a p hp7) (by omega) (D7Frame_band a r m p ha hp64 hrp hm1)
      r m x.val s hr hp hpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
      k ha hk hroot hgood (hden C1T29_den (by simp))
    simpa only [seventhsPoleSplit, ZMod.natCast_zmod_val] using h
  · obtain ⟨hpar, hx, hlo, hhi, hgood⟩ := h3
    have h := C1S19_run3 a p (r + 2 * m) hp7 (D7Frame_coeff_mem a p)
      (D7Frame_den_units a p hp7) (by omega) (D7Frame_band a r m p ha hp64 hrp hm1)
      r m x.val s hr hp hpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
      k ha hk hroot hgood (hden C1T30_den (by simp))
    simpa only [seventhsPoleSplit, ZMod.natCast_zmod_val] using h
  · obtain ⟨hpar, hx, hlo, hhi, hgood⟩ := h4
    have h := C1S19_run4 a p (r + 2 * m) hp7 (D7Frame_coeff_mem a p)
      (D7Frame_den_units a p hp7) (by omega) (D7Frame_band a r m p ha hp64 hrp hm1)
      r m x.val s hr hp hpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
      k ha hk hroot hgood (hden C1T32_den (by simp))
    simpa only [seventhsPoleSplit, ZMod.natCast_zmod_val] using h
  · obtain ⟨hpar, hx, hlo, hhi, hgood⟩ := h5
    have h := C1S19_run5 a p (r + 2 * m) hp7 (D7Frame_coeff_mem a p)
      (D7Frame_den_units a p hp7) (by omega) (D7Frame_band a r m p ha hp64 hrp hm1)
      r m x.val s hr hp hpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
      k ha hk hroot hgood (hden C1T32_den (by simp))
    simpa only [seventhsPoleSplit, ZMod.natCast_zmod_val] using h
  · obtain ⟨hpar, hx, hlo, hhi, hgood⟩ := h6
    have h := C1S19_run6 a p (r + 2 * m) hp7 (D7Frame_coeff_mem a p)
      (D7Frame_den_units a p hp7) (by omega) (D7Frame_band a r m p ha hp64 hrp hm1)
      r m x.val s hr hp hpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
      k ha hk hroot hgood (hden C1T35_den (by simp))
    simpa only [seventhsPoleSplit, ZMod.natCast_zmod_val] using h
  · obtain ⟨hpar, hx, hlo, hhi, hgood⟩ := h7
    have h := C1S19_run7 a p (r + 2 * m) hp7 (D7Frame_coeff_mem a p)
      (D7Frame_den_units a p hp7) (by omega) (D7Frame_band a r m p ha hp64 hrp hm1)
      r m x.val s hr hp hpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
      k ha hk hroot hgood (hden C1T36_den (by simp))
    simpa only [seventhsPoleSplit, ZMod.natCast_zmod_val] using h
  · exact ⟨FibreCert.triv_ok _ _ _ _, FibreCert.triv_integral _ _ _ _,
      trivCert_realizes _ _ _ _⟩

private theorem C1S19_disjoint0_2 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p)
    (hleft : 1 * r ≤ 1 * p)
    (hright : 48 * p ≤ 49 * r) :
    ¬ (C1S19_test0 r p s x ∧ C1S19_test2 r p s x) := by
  rintro ⟨⟨hpar0, hx0, hlo0, hhi0, hgood0⟩, ⟨hpar1, hx1, hlo1, hhi1, hgood1⟩⟩
  omega

private theorem C1S19_disjoint0_4 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p)
    (hleft : 1 * r ≤ 1 * p)
    (hright : 48 * p ≤ 49 * r) :
    ¬ (C1S19_test0 r p s x ∧ C1S19_test4 r p s x) := by
  rintro ⟨⟨hpar0, hx0, hlo0, hhi0, hgood0⟩, ⟨hpar1, hx1, hlo1, hhi1, hgood1⟩⟩
  omega

private theorem C1S19_disjoint0_6 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p)
    (hleft : 1 * r ≤ 1 * p)
    (hright : 48 * p ≤ 49 * r) :
    ¬ (C1S19_test0 r p s x ∧ C1S19_test6 r p s x) := by
  rintro ⟨⟨hpar0, hx0, hlo0, hhi0, hgood0⟩, ⟨hpar1, hx1, hlo1, hhi1, hgood1⟩⟩
  omega

private theorem C1S19_disjoint1_3 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p)
    (hleft : 1 * r ≤ 1 * p)
    (hright : 48 * p ≤ 49 * r) :
    ¬ (C1S19_test1 r p s x ∧ C1S19_test3 r p s x) := by
  rintro ⟨⟨hpar0, hx0, hlo0, hhi0, hgood0⟩, ⟨hpar1, hx1, hlo1, hhi1, hgood1⟩⟩
  omega

private theorem C1S19_disjoint1_5 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p)
    (hleft : 1 * r ≤ 1 * p)
    (hright : 48 * p ≤ 49 * r) :
    ¬ (C1S19_test1 r p s x ∧ C1S19_test5 r p s x) := by
  rintro ⟨⟨hpar0, hx0, hlo0, hhi0, hgood0⟩, ⟨hpar1, hx1, hlo1, hhi1, hgood1⟩⟩
  omega

private theorem C1S19_disjoint1_7 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p)
    (hleft : 1 * r ≤ 1 * p)
    (hright : 48 * p ≤ 49 * r) :
    ¬ (C1S19_test1 r p s x ∧ C1S19_test7 r p s x) := by
  rintro ⟨⟨hpar0, hx0, hlo0, hhi0, hgood0⟩, ⟨hpar1, hx1, hlo1, hhi1, hgood1⟩⟩
  omega

private theorem C1S19_disjoint2_4 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p)
    (hleft : 1 * r ≤ 1 * p)
    (hright : 48 * p ≤ 49 * r) :
    ¬ (C1S19_test2 r p s x ∧ C1S19_test4 r p s x) := by
  rintro ⟨⟨hpar0, hx0, hlo0, hhi0, hgood0⟩, ⟨hpar1, hx1, hlo1, hhi1, hgood1⟩⟩
  omega

private theorem C1S19_disjoint2_6 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p)
    (hleft : 1 * r ≤ 1 * p)
    (hright : 48 * p ≤ 49 * r) :
    ¬ (C1S19_test2 r p s x ∧ C1S19_test6 r p s x) := by
  rintro ⟨⟨hpar0, hx0, hlo0, hhi0, hgood0⟩, ⟨hpar1, hx1, hlo1, hhi1, hgood1⟩⟩
  omega

private theorem C1S19_disjoint3_5 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p)
    (hleft : 1 * r ≤ 1 * p)
    (hright : 48 * p ≤ 49 * r) :
    ¬ (C1S19_test3 r p s x ∧ C1S19_test5 r p s x) := by
  rintro ⟨⟨hpar0, hx0, hlo0, hhi0, hgood0⟩, ⟨hpar1, hx1, hlo1, hhi1, hgood1⟩⟩
  omega

private theorem C1S19_disjoint3_7 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p)
    (hleft : 1 * r ≤ 1 * p)
    (hright : 48 * p ≤ 49 * r) :
    ¬ (C1S19_test3 r p s x ∧ C1S19_test7 r p s x) := by
  rintro ⟨⟨hpar0, hx0, hlo0, hhi0, hgood0⟩, ⟨hpar1, hx1, hlo1, hhi1, hgood1⟩⟩
  omega

private theorem C1S19_disjoint4_6 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p)
    (hleft : 1 * r ≤ 1 * p)
    (hright : 48 * p ≤ 49 * r) :
    ¬ (C1S19_test4 r p s x ∧ C1S19_test6 r p s x) := by
  rintro ⟨⟨hpar0, hx0, hlo0, hhi0, hgood0⟩, ⟨hpar1, hx1, hlo1, hhi1, hgood1⟩⟩
  omega

private theorem C1S19_disjoint5_7 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p)
    (hleft : 1 * r ≤ 1 * p)
    (hright : 48 * p ≤ 49 * r) :
    ¬ (C1S19_test5 r p s x ∧ C1S19_test7 r p s x) := by
  rintro ⟨⟨hpar0, hx0, hlo0, hhi0, hgood0⟩, ⟨hpar1, hx1, hlo1, hhi1, hgood1⟩⟩
  omega

theorem C1S19_assignment_on_run0 (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : 1 ≤ a ∧ a ≤ 6) (hp64 : 64 ≤ p) (hp7 : ¬ p ∣ 7)
    (hrp : r ≤ 6 * p) (hm1 : 12 * m ≤ r + 6)
    (hleft : 1 * r ≤ 1 * p)
    (hright : 48 * p ≤ 49 * r) (x : ZMod p)
    (hi : C1S19_test0 r p s x) :
    C1S19_assignment a p r m s ha hp64 hp7 hrp hm1 x = C1T33 := by
  simp only [C1S19_assignment, if_pos hi]

theorem C1S19_assignment_on_run1 (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : 1 ≤ a ∧ a ≤ 6) (hp64 : 64 ≤ p) (hp7 : ¬ p ∣ 7)
    (hrp : r ≤ 6 * p) (hm1 : 12 * m ≤ r + 6)
    (hleft : 1 * r ≤ 1 * p)
    (hright : 48 * p ≤ 49 * r) (x : ZMod p)
    (hi : C1S19_test1 r p s x) :
    C1S19_assignment a p r m s ha hp64 hp7 hrp hm1 x = C1T34 := by
  have hn0 : ¬ C1S19_test0 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  simp only [C1S19_assignment, if_neg hn0, if_pos hi]

theorem C1S19_assignment_on_run2 (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : 1 ≤ a ∧ a ≤ 6) (hp64 : 64 ≤ p) (hp7 : ¬ p ∣ 7)
    (hrp : r ≤ 6 * p) (hm1 : 12 * m ≤ r + 6)
    (hleft : 1 * r ≤ 1 * p)
    (hright : 48 * p ≤ 49 * r) (x : ZMod p)
    (hi : C1S19_test2 r p s x) :
    C1S19_assignment a p r m s ha hp64 hp7 hrp hm1 x = C1T29 := by
  have hn0 : ¬ C1S19_test0 r p s x := fun hj => C1S19_disjoint0_2 r p s x hleft hright ⟨hj, hi⟩
  have hn1 : ¬ C1S19_test1 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  simp only [C1S19_assignment, if_neg hn0, if_neg hn1, if_pos hi]

theorem C1S19_assignment_on_run3 (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : 1 ≤ a ∧ a ≤ 6) (hp64 : 64 ≤ p) (hp7 : ¬ p ∣ 7)
    (hrp : r ≤ 6 * p) (hm1 : 12 * m ≤ r + 6)
    (hleft : 1 * r ≤ 1 * p)
    (hright : 48 * p ≤ 49 * r) (x : ZMod p)
    (hi : C1S19_test3 r p s x) :
    C1S19_assignment a p r m s ha hp64 hp7 hrp hm1 x = C1T30 := by
  have hn0 : ¬ C1S19_test0 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  have hn1 : ¬ C1S19_test1 r p s x := fun hj => C1S19_disjoint1_3 r p s x hleft hright ⟨hj, hi⟩
  have hn2 : ¬ C1S19_test2 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  simp only [C1S19_assignment, if_neg hn0, if_neg hn1, if_neg hn2, if_pos hi]

theorem C1S19_assignment_on_run4 (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : 1 ≤ a ∧ a ≤ 6) (hp64 : 64 ≤ p) (hp7 : ¬ p ∣ 7)
    (hrp : r ≤ 6 * p) (hm1 : 12 * m ≤ r + 6)
    (hleft : 1 * r ≤ 1 * p)
    (hright : 48 * p ≤ 49 * r) (x : ZMod p)
    (hi : C1S19_test4 r p s x) :
    C1S19_assignment a p r m s ha hp64 hp7 hrp hm1 x = C1T32 := by
  have hn0 : ¬ C1S19_test0 r p s x := fun hj => C1S19_disjoint0_4 r p s x hleft hright ⟨hj, hi⟩
  have hn1 : ¬ C1S19_test1 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  have hn2 : ¬ C1S19_test2 r p s x := fun hj => C1S19_disjoint2_4 r p s x hleft hright ⟨hj, hi⟩
  have hn3 : ¬ C1S19_test3 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  simp only [C1S19_assignment, if_neg hn0, if_neg hn1, if_neg hn2, if_neg hn3, if_pos hi]

theorem C1S19_assignment_on_run5 (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : 1 ≤ a ∧ a ≤ 6) (hp64 : 64 ≤ p) (hp7 : ¬ p ∣ 7)
    (hrp : r ≤ 6 * p) (hm1 : 12 * m ≤ r + 6)
    (hleft : 1 * r ≤ 1 * p)
    (hright : 48 * p ≤ 49 * r) (x : ZMod p)
    (hi : C1S19_test5 r p s x) :
    C1S19_assignment a p r m s ha hp64 hp7 hrp hm1 x = C1T32 := by
  have hn0 : ¬ C1S19_test0 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  have hn1 : ¬ C1S19_test1 r p s x := fun hj => C1S19_disjoint1_5 r p s x hleft hright ⟨hj, hi⟩
  have hn2 : ¬ C1S19_test2 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  have hn3 : ¬ C1S19_test3 r p s x := fun hj => C1S19_disjoint3_5 r p s x hleft hright ⟨hj, hi⟩
  have hn4 : ¬ C1S19_test4 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  simp only [C1S19_assignment, if_neg hn0, if_neg hn1, if_neg hn2, if_neg hn3, if_neg hn4, if_pos hi]

theorem C1S19_assignment_on_run6 (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : 1 ≤ a ∧ a ≤ 6) (hp64 : 64 ≤ p) (hp7 : ¬ p ∣ 7)
    (hrp : r ≤ 6 * p) (hm1 : 12 * m ≤ r + 6)
    (hleft : 1 * r ≤ 1 * p)
    (hright : 48 * p ≤ 49 * r) (x : ZMod p)
    (hi : C1S19_test6 r p s x) :
    C1S19_assignment a p r m s ha hp64 hp7 hrp hm1 x = C1T35 := by
  have hn0 : ¬ C1S19_test0 r p s x := fun hj => C1S19_disjoint0_6 r p s x hleft hright ⟨hj, hi⟩
  have hn1 : ¬ C1S19_test1 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  have hn2 : ¬ C1S19_test2 r p s x := fun hj => C1S19_disjoint2_6 r p s x hleft hright ⟨hj, hi⟩
  have hn3 : ¬ C1S19_test3 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  have hn4 : ¬ C1S19_test4 r p s x := fun hj => C1S19_disjoint4_6 r p s x hleft hright ⟨hj, hi⟩
  have hn5 : ¬ C1S19_test5 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  simp only [C1S19_assignment, if_neg hn0, if_neg hn1, if_neg hn2, if_neg hn3, if_neg hn4, if_neg hn5, if_pos hi]

theorem C1S19_assignment_on_run7 (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : 1 ≤ a ∧ a ≤ 6) (hp64 : 64 ≤ p) (hp7 : ¬ p ∣ 7)
    (hrp : r ≤ 6 * p) (hm1 : 12 * m ≤ r + 6)
    (hleft : 1 * r ≤ 1 * p)
    (hright : 48 * p ≤ 49 * r) (x : ZMod p)
    (hi : C1S19_test7 r p s x) :
    C1S19_assignment a p r m s ha hp64 hp7 hrp hm1 x = C1T36 := by
  have hn0 : ¬ C1S19_test0 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  have hn1 : ¬ C1S19_test1 r p s x := fun hj => C1S19_disjoint1_7 r p s x hleft hright ⟨hj, hi⟩
  have hn2 : ¬ C1S19_test2 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  have hn3 : ¬ C1S19_test3 r p s x := fun hj => C1S19_disjoint3_7 r p s x hleft hright ⟨hj, hi⟩
  have hn4 : ¬ C1S19_test4 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  have hn5 : ¬ C1S19_test5 r p s x := fun hj => C1S19_disjoint5_7 r p s x hleft hright ⟨hj, hi⟩
  have hn6 : ¬ C1S19_test6 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  simp only [C1S19_assignment, if_neg hn0, if_neg hn1, if_neg hn2, if_neg hn3, if_neg hn4, if_neg hn5, if_neg hn6, if_pos hi]

#print axioms C1S19_assignment_valid
#print axioms C1S19_assignment_on_run0

#print axioms C1S19_run0
end CatalanCore.Uniform.Bank.Sevenths.RankFibre
