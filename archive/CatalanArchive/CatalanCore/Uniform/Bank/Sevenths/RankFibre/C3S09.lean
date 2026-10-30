import CatalanCore.Uniform.Bank.Sevenths.CommonMinorRealize
import CatalanCore.Uniform.Content.RankProducer.Boundary
import CatalanCore.Uniform.Bank.Sevenths.Band
import CatalanCore.Uniform.Bank.Sevenths.RankSource.C3S09
import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C3
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankFibre
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.RankProducer
open CatalanCore.Uniform.Content.RankProducer.Geometry RankSource RankData
open scoped Classical

theorem C3S09_run0 (a p Bnd : ℕ) [Fact p.Prime] (hp7 : ¬ p ∣ 7)
    (hc : ∀ j, (D7Frame a).c j ∈ S p) (hpq : ∀ j, ¬ p ∣ (D7Frame a).q j)
    (hp3 : 3 ≤ p) (hbd : ∀ j, (D7Frame a).q j * Bnd + (D7Frame a).u j ≤ p ^ 2)
    (r m x : ℕ) (s : Finset (Fin r)) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 0) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 12 * m ≤ r + 6) (hm2 : r ≤ 12 * m + 6) (hrp : r ≤ 6 * p)
    (hleft : 1 * r ≤ 4 * p)
    (hright : 26 * p ≤ 7 * r)
    (hlo : (1 : ℤ) * x ≥ (0 : ℤ) * r + (0 : ℤ) * p + 4)
    (hhi : (6 : ℤ) * x ≤ (7 : ℤ) * r + (-24 : ℤ) * p - 24)
    (k : ℕ) (ha : 1 ≤ a ∧ a ≤ 6) (hk : k < p) (hroot : 7 * k + a = 5 * p)
    (hgood : x ∉ deletedResidues r p s) (hden : ¬ p ∣ C3T14_den) :
    C3T14.Ok ∧ C3T14.Integral p ∧
      Realizes ((D7Frame a).poleSplit Bnd hc hpq hp3 hbd)
        (rowsOf r m s) (colsOf r m s) (x : ZMod p) C3T14 := by
  refine ⟨C3T14_ok, C3T14_integral p hden, ?_⟩
  apply realizes_commonMinor_D7Frame a p Bnd hp7 hc hpq hp3 hbd r m s k 5 x 0
    hk (by omega) hxp
    (C3S09_run0_bit r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi a k ha hroot)
    C3T14
  · exact C3S09_run0_R r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact C3S09_run0_C r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact kept_of_not_deleted r p s x hxp hgood
  · exact C3T14_palette.1
  · exact fun d hd => (C3T14_palette.2 d hd).1

theorem C3S09_run1 (a p Bnd : ℕ) [Fact p.Prime] (hp7 : ¬ p ∣ 7)
    (hc : ∀ j, (D7Frame a).c j ∈ S p) (hpq : ∀ j, ¬ p ∣ (D7Frame a).q j)
    (hp3 : 3 ≤ p) (hbd : ∀ j, (D7Frame a).q j * Bnd + (D7Frame a).u j ≤ p ^ 2)
    (r m x : ℕ) (s : Finset (Fin r)) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 1) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 12 * m ≤ r + 6) (hm2 : r ≤ 12 * m + 6) (hrp : r ≤ 6 * p)
    (hleft : 1 * r ≤ 4 * p)
    (hright : 26 * p ≤ 7 * r)
    (hlo : (1 : ℤ) * x ≥ (0 : ℤ) * r + (0 : ℤ) * p + 4)
    (hhi : (6 : ℤ) * x ≤ (7 : ℤ) * r + (-24 : ℤ) * p - 24)
    (k : ℕ) (ha : 1 ≤ a ∧ a ≤ 6) (hk : k < p) (hroot : 7 * k + a = 5 * p)
    (hgood : x ∉ deletedResidues r p s) (hden : ¬ p ∣ C3T15_den) :
    C3T15.Ok ∧ C3T15.Integral p ∧
      Realizes ((D7Frame a).poleSplit Bnd hc hpq hp3 hbd)
        (rowsOf r m s) (colsOf r m s) (x : ZMod p) C3T15 := by
  refine ⟨C3T15_ok, C3T15_integral p hden, ?_⟩
  apply realizes_commonMinor_D7Frame a p Bnd hp7 hc hpq hp3 hbd r m s k 5 x 0
    hk (by omega) hxp
    (C3S09_run1_bit r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi a k ha hroot)
    C3T15
  · exact C3S09_run1_R r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact C3S09_run1_C r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact kept_of_not_deleted r p s x hxp hgood
  · exact C3T15_palette.1
  · exact fun d hd => (C3T15_palette.2 d hd).1

theorem C3S09_run2 (a p Bnd : ℕ) [Fact p.Prime] (hp7 : ¬ p ∣ 7)
    (hc : ∀ j, (D7Frame a).c j ∈ S p) (hpq : ∀ j, ¬ p ∣ (D7Frame a).q j)
    (hp3 : 3 ≤ p) (hbd : ∀ j, (D7Frame a).q j * Bnd + (D7Frame a).u j ≤ p ^ 2)
    (r m x : ℕ) (s : Finset (Fin r)) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 0) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 12 * m ≤ r + 6) (hm2 : r ≤ 12 * m + 6) (hrp : r ≤ 6 * p)
    (hleft : 1 * r ≤ 4 * p)
    (hright : 26 * p ≤ 7 * r)
    (hlo : (6 : ℤ) * x ≥ (7 : ℤ) * r + (-24 : ℤ) * p + 24)
    (hhi : (7 : ℤ) * x ≤ (0 : ℤ) * r + (5 : ℤ) * p - 28)
    (k : ℕ) (ha : 1 ≤ a ∧ a ≤ 6) (hk : k < p) (hroot : 7 * k + a = 5 * p)
    (hgood : x ∉ deletedResidues r p s) (hden : ¬ p ∣ C3T17_den) :
    C3T17.Ok ∧ C3T17.Integral p ∧
      Realizes ((D7Frame a).poleSplit Bnd hc hpq hp3 hbd)
        (rowsOf r m s) (colsOf r m s) (x : ZMod p) C3T17 := by
  refine ⟨C3T17_ok, C3T17_integral p hden, ?_⟩
  apply realizes_commonMinor_D7Frame a p Bnd hp7 hc hpq hp3 hbd r m s k 5 x 0
    hk (by omega) hxp
    (C3S09_run2_bit r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi a k ha hroot)
    C3T17
  · exact C3S09_run2_R r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact C3S09_run2_C r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact kept_of_not_deleted r p s x hxp hgood
  · exact C3T17_palette.1
  · exact fun d hd => (C3T17_palette.2 d hd).1

theorem C3S09_run3 (a p Bnd : ℕ) [Fact p.Prime] (hp7 : ¬ p ∣ 7)
    (hc : ∀ j, (D7Frame a).c j ∈ S p) (hpq : ∀ j, ¬ p ∣ (D7Frame a).q j)
    (hp3 : 3 ≤ p) (hbd : ∀ j, (D7Frame a).q j * Bnd + (D7Frame a).u j ≤ p ^ 2)
    (r m x : ℕ) (s : Finset (Fin r)) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 1) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 12 * m ≤ r + 6) (hm2 : r ≤ 12 * m + 6) (hrp : r ≤ 6 * p)
    (hleft : 1 * r ≤ 4 * p)
    (hright : 26 * p ≤ 7 * r)
    (hlo : (6 : ℤ) * x ≥ (7 : ℤ) * r + (-24 : ℤ) * p + 24)
    (hhi : (7 : ℤ) * x ≤ (0 : ℤ) * r + (5 : ℤ) * p - 28)
    (k : ℕ) (ha : 1 ≤ a ∧ a ≤ 6) (hk : k < p) (hroot : 7 * k + a = 5 * p)
    (hgood : x ∉ deletedResidues r p s) (hden : ¬ p ∣ C3T17_den) :
    C3T17.Ok ∧ C3T17.Integral p ∧
      Realizes ((D7Frame a).poleSplit Bnd hc hpq hp3 hbd)
        (rowsOf r m s) (colsOf r m s) (x : ZMod p) C3T17 := by
  refine ⟨C3T17_ok, C3T17_integral p hden, ?_⟩
  apply realizes_commonMinor_D7Frame a p Bnd hp7 hc hpq hp3 hbd r m s k 5 x 0
    hk (by omega) hxp
    (C3S09_run3_bit r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi a k ha hroot)
    C3T17
  · exact C3S09_run3_R r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact C3S09_run3_C r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact kept_of_not_deleted r p s x hxp hgood
  · exact C3T17_palette.1
  · exact fun d hd => (C3T17_palette.2 d hd).1

theorem C3S09_run4 (a p Bnd : ℕ) [Fact p.Prime] (hp7 : ¬ p ∣ 7)
    (hc : ∀ j, (D7Frame a).c j ∈ S p) (hpq : ∀ j, ¬ p ∣ (D7Frame a).q j)
    (hp3 : 3 ≤ p) (hbd : ∀ j, (D7Frame a).q j * Bnd + (D7Frame a).u j ≤ p ^ 2)
    (r m x : ℕ) (s : Finset (Fin r)) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 0) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 12 * m ≤ r + 6) (hm2 : r ≤ 12 * m + 6) (hrp : r ≤ 6 * p)
    (hleft : 1 * r ≤ 4 * p)
    (hright : 26 * p ≤ 7 * r)
    (hlo : (7 : ℤ) * x ≥ (0 : ℤ) * r + (5 : ℤ) * p + 28)
    (hhi : (1 : ℤ) * x ≤ (1 : ℤ) * r + (-3 : ℤ) * p - 4)
    (k : ℕ) (ha : 1 ≤ a ∧ a ≤ 6) (hk : k < p) (hroot : 7 * k + a = 5 * p)
    (hgood : x ∉ deletedResidues r p s) (hden : ¬ p ∣ C3T16_den) :
    C3T16.Ok ∧ C3T16.Integral p ∧
      Realizes ((D7Frame a).poleSplit Bnd hc hpq hp3 hbd)
        (rowsOf r m s) (colsOf r m s) (x : ZMod p) C3T16 := by
  refine ⟨C3T16_ok, C3T16_integral p hden, ?_⟩
  apply realizes_commonMinor_D7Frame a p Bnd hp7 hc hpq hp3 hbd r m s k 5 x 1
    hk (by omega) hxp
    (C3S09_run4_bit r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi a k ha hroot)
    C3T16
  · exact C3S09_run4_R r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact C3S09_run4_C r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact kept_of_not_deleted r p s x hxp hgood
  · exact C3T16_palette.1
  · exact fun d hd => (C3T16_palette.2 d hd).1

theorem C3S09_run5 (a p Bnd : ℕ) [Fact p.Prime] (hp7 : ¬ p ∣ 7)
    (hc : ∀ j, (D7Frame a).c j ∈ S p) (hpq : ∀ j, ¬ p ∣ (D7Frame a).q j)
    (hp3 : 3 ≤ p) (hbd : ∀ j, (D7Frame a).q j * Bnd + (D7Frame a).u j ≤ p ^ 2)
    (r m x : ℕ) (s : Finset (Fin r)) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 1) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 12 * m ≤ r + 6) (hm2 : r ≤ 12 * m + 6) (hrp : r ≤ 6 * p)
    (hleft : 1 * r ≤ 4 * p)
    (hright : 26 * p ≤ 7 * r)
    (hlo : (7 : ℤ) * x ≥ (0 : ℤ) * r + (5 : ℤ) * p + 28)
    (hhi : (1 : ℤ) * x ≤ (1 : ℤ) * r + (-3 : ℤ) * p - 4)
    (k : ℕ) (ha : 1 ≤ a ∧ a ≤ 6) (hk : k < p) (hroot : 7 * k + a = 5 * p)
    (hgood : x ∉ deletedResidues r p s) (hden : ¬ p ∣ C3T16_den) :
    C3T16.Ok ∧ C3T16.Integral p ∧
      Realizes ((D7Frame a).poleSplit Bnd hc hpq hp3 hbd)
        (rowsOf r m s) (colsOf r m s) (x : ZMod p) C3T16 := by
  refine ⟨C3T16_ok, C3T16_integral p hden, ?_⟩
  apply realizes_commonMinor_D7Frame a p Bnd hp7 hc hpq hp3 hbd r m s k 5 x 1
    hk (by omega) hxp
    (C3S09_run5_bit r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi a k ha hroot)
    C3T16
  · exact C3S09_run5_R r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact C3S09_run5_C r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact kept_of_not_deleted r p s x hxp hgood
  · exact C3T16_palette.1
  · exact fun d hd => (C3T16_palette.2 d hd).1

theorem C3S09_run6 (a p Bnd : ℕ) [Fact p.Prime] (hp7 : ¬ p ∣ 7)
    (hc : ∀ j, (D7Frame a).c j ∈ S p) (hpq : ∀ j, ¬ p ∣ (D7Frame a).q j)
    (hp3 : 3 ≤ p) (hbd : ∀ j, (D7Frame a).q j * Bnd + (D7Frame a).u j ≤ p ^ 2)
    (r m x : ℕ) (s : Finset (Fin r)) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 0) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 12 * m ≤ r + 6) (hm2 : r ≤ 12 * m + 6) (hrp : r ≤ 6 * p)
    (hleft : 1 * r ≤ 4 * p)
    (hright : 26 * p ≤ 7 * r)
    (hlo : (1 : ℤ) * x ≥ (1 : ℤ) * r + (-3 : ℤ) * p + 4)
    (hhi : (1 : ℤ) * x ≤ (0 : ℤ) * r + (1 : ℤ) * p - 4)
    (k : ℕ) (ha : 1 ≤ a ∧ a ≤ 6) (hk : k < p) (hroot : 7 * k + a = 5 * p)
    (hgood : x ∉ deletedResidues r p s) (hden : ¬ p ∣ C3T18_den) :
    C3T18.Ok ∧ C3T18.Integral p ∧
      Realizes ((D7Frame a).poleSplit Bnd hc hpq hp3 hbd)
        (rowsOf r m s) (colsOf r m s) (x : ZMod p) C3T18 := by
  refine ⟨C3T18_ok, C3T18_integral p hden, ?_⟩
  apply realizes_commonMinor_D7Frame a p Bnd hp7 hc hpq hp3 hbd r m s k 5 x 1
    hk (by omega) hxp
    (C3S09_run6_bit r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi a k ha hroot)
    C3T18
  · exact C3S09_run6_R r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact C3S09_run6_C r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact kept_of_not_deleted r p s x hxp hgood
  · exact C3T18_palette.1
  · exact fun d hd => (C3T18_palette.2 d hd).1

theorem C3S09_run7 (a p Bnd : ℕ) [Fact p.Prime] (hp7 : ¬ p ∣ 7)
    (hc : ∀ j, (D7Frame a).c j ∈ S p) (hpq : ∀ j, ¬ p ∣ (D7Frame a).q j)
    (hp3 : 3 ≤ p) (hbd : ∀ j, (D7Frame a).q j * Bnd + (D7Frame a).u j ≤ p ^ 2)
    (r m x : ℕ) (s : Finset (Fin r)) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 1) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 12 * m ≤ r + 6) (hm2 : r ≤ 12 * m + 6) (hrp : r ≤ 6 * p)
    (hleft : 1 * r ≤ 4 * p)
    (hright : 26 * p ≤ 7 * r)
    (hlo : (1 : ℤ) * x ≥ (1 : ℤ) * r + (-3 : ℤ) * p + 4)
    (hhi : (1 : ℤ) * x ≤ (0 : ℤ) * r + (1 : ℤ) * p - 4)
    (k : ℕ) (ha : 1 ≤ a ∧ a ≤ 6) (hk : k < p) (hroot : 7 * k + a = 5 * p)
    (hgood : x ∉ deletedResidues r p s) (hden : ¬ p ∣ C3T19_den) :
    C3T19.Ok ∧ C3T19.Integral p ∧
      Realizes ((D7Frame a).poleSplit Bnd hc hpq hp3 hbd)
        (rowsOf r m s) (colsOf r m s) (x : ZMod p) C3T19 := by
  refine ⟨C3T19_ok, C3T19_integral p hden, ?_⟩
  apply realizes_commonMinor_D7Frame a p Bnd hp7 hc hpq hp3 hbd r m s k 5 x 1
    hk (by omega) hxp
    (C3S09_run7_bit r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi a k ha hroot)
    C3T19
  · exact C3S09_run7_R r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact C3S09_run7_C r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact kept_of_not_deleted r p s x hxp hgood
  · exact C3T19_palette.1
  · exact fun d hd => (C3T19_palette.2 d hd).1

noncomputable def C3S09_test0 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p) : Prop :=
  x.val % 2 = 0 ∧ 4 ≤ x.val ∧
    (0 : ℤ) * r + (0 : ℤ) * p + 4 ≤ (1 : ℤ) * x.val ∧
    (6 : ℤ) * x.val ≤ (7 : ℤ) * r + (-24 : ℤ) * p - 24 ∧
    x.val ∉ deletedResidues r p s
noncomputable def C3S09_test1 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p) : Prop :=
  x.val % 2 = 1 ∧ 4 ≤ x.val ∧
    (0 : ℤ) * r + (0 : ℤ) * p + 4 ≤ (1 : ℤ) * x.val ∧
    (6 : ℤ) * x.val ≤ (7 : ℤ) * r + (-24 : ℤ) * p - 24 ∧
    x.val ∉ deletedResidues r p s
noncomputable def C3S09_test2 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p) : Prop :=
  x.val % 2 = 0 ∧ 4 ≤ x.val ∧
    (7 : ℤ) * r + (-24 : ℤ) * p + 24 ≤ (6 : ℤ) * x.val ∧
    (7 : ℤ) * x.val ≤ (0 : ℤ) * r + (5 : ℤ) * p - 28 ∧
    x.val ∉ deletedResidues r p s
noncomputable def C3S09_test3 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p) : Prop :=
  x.val % 2 = 1 ∧ 4 ≤ x.val ∧
    (7 : ℤ) * r + (-24 : ℤ) * p + 24 ≤ (6 : ℤ) * x.val ∧
    (7 : ℤ) * x.val ≤ (0 : ℤ) * r + (5 : ℤ) * p - 28 ∧
    x.val ∉ deletedResidues r p s
noncomputable def C3S09_test4 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p) : Prop :=
  x.val % 2 = 0 ∧ 4 ≤ x.val ∧
    (0 : ℤ) * r + (5 : ℤ) * p + 28 ≤ (7 : ℤ) * x.val ∧
    (1 : ℤ) * x.val ≤ (1 : ℤ) * r + (-3 : ℤ) * p - 4 ∧
    x.val ∉ deletedResidues r p s
noncomputable def C3S09_test5 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p) : Prop :=
  x.val % 2 = 1 ∧ 4 ≤ x.val ∧
    (0 : ℤ) * r + (5 : ℤ) * p + 28 ≤ (7 : ℤ) * x.val ∧
    (1 : ℤ) * x.val ≤ (1 : ℤ) * r + (-3 : ℤ) * p - 4 ∧
    x.val ∉ deletedResidues r p s
noncomputable def C3S09_test6 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p) : Prop :=
  x.val % 2 = 0 ∧ 4 ≤ x.val ∧
    (1 : ℤ) * r + (-3 : ℤ) * p + 4 ≤ (1 : ℤ) * x.val ∧
    (1 : ℤ) * x.val ≤ (0 : ℤ) * r + (1 : ℤ) * p - 4 ∧
    x.val ∉ deletedResidues r p s
noncomputable def C3S09_test7 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p) : Prop :=
  x.val % 2 = 1 ∧ 4 ≤ x.val ∧
    (1 : ℤ) * r + (-3 : ℤ) * p + 4 ≤ (1 : ℤ) * x.val ∧
    (1 : ℤ) * x.val ≤ (0 : ℤ) * r + (1 : ℤ) * p - 4 ∧
    x.val ∉ deletedResidues r p s

noncomputable def C3S09_assignment (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : 1 ≤ a ∧ a ≤ 6) (hp64 : 64 ≤ p) (hp7 : ¬ p ∣ 7)
    (hrp : r ≤ 6 * p) (hm1 : 12 * m ≤ r + 6) : ZMod p → FibreCert := fun x =>
  if C3S09_test0 r p s x then C3T14 else
  if C3S09_test1 r p s x then C3T15 else
  if C3S09_test2 r p s x then C3T17 else
  if C3S09_test3 r p s x then C3T17 else
  if C3S09_test4 r p s x then C3T16 else
  if C3S09_test5 r p s x then C3T16 else
  if C3S09_test6 r p s x then C3T18 else
  if C3S09_test7 r p s x then C3T19 else
  trivCert (seventhsPoleSplit a p r m ha hp64 hp7 hrp hm1) (rowsOf r m s) (colsOf r m s) x

theorem C3S09_assignment_valid (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : 1 ≤ a ∧ a ≤ 6) (hp64 : 64 ≤ p) (hp7 : ¬ p ∣ 7)
    (hrp : r ≤ 6 * p) (hm1 : 12 * m ≤ r + 6)
    (hr : r % 2 = 0) (hp : p % 2 = 1) (hm2 : r ≤ 12 * m + 6)
    (hleft : 1 * r ≤ 4 * p)
    (hright : 26 * p ≤ 7 * r)
    (k : ℕ) (hk : k < p) (hroot : 7 * k + a = 5 * p)
    (hden : ∀ N ∈ ([C3T14_den, C3T15_den, C3T16_den, C3T17_den, C3T18_den, C3T19_den] : List ℕ), ¬ p ∣ N) (x : ZMod p) :
    (C3S09_assignment a p r m s ha hp64 hp7 hrp hm1 x).Ok ∧
    (C3S09_assignment a p r m s ha hp64 hp7 hrp hm1 x).Integral p ∧
    Realizes (seventhsPoleSplit a p r m ha hp64 hp7 hrp hm1)
      (rowsOf r m s) (colsOf r m s) x
      (C3S09_assignment a p r m s ha hp64 hp7 hrp hm1 x) := by
  have hxp : x.val < p := ZMod.val_lt x
  unfold C3S09_assignment
  split_ifs with h0 h1 h2 h3 h4 h5 h6 h7
  · obtain ⟨hpar, hx, hlo, hhi, hgood⟩ := h0
    have h := C3S09_run0 a p (r + 2 * m) hp7 (D7Frame_coeff_mem a p)
      (D7Frame_den_units a p hp7) (by omega) (D7Frame_band a r m p ha hp64 hrp hm1)
      r m x.val s hr hp hpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
      k ha hk hroot hgood (hden C3T14_den (by simp))
    simpa only [seventhsPoleSplit, ZMod.natCast_zmod_val] using h
  · obtain ⟨hpar, hx, hlo, hhi, hgood⟩ := h1
    have h := C3S09_run1 a p (r + 2 * m) hp7 (D7Frame_coeff_mem a p)
      (D7Frame_den_units a p hp7) (by omega) (D7Frame_band a r m p ha hp64 hrp hm1)
      r m x.val s hr hp hpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
      k ha hk hroot hgood (hden C3T15_den (by simp))
    simpa only [seventhsPoleSplit, ZMod.natCast_zmod_val] using h
  · obtain ⟨hpar, hx, hlo, hhi, hgood⟩ := h2
    have h := C3S09_run2 a p (r + 2 * m) hp7 (D7Frame_coeff_mem a p)
      (D7Frame_den_units a p hp7) (by omega) (D7Frame_band a r m p ha hp64 hrp hm1)
      r m x.val s hr hp hpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
      k ha hk hroot hgood (hden C3T17_den (by simp))
    simpa only [seventhsPoleSplit, ZMod.natCast_zmod_val] using h
  · obtain ⟨hpar, hx, hlo, hhi, hgood⟩ := h3
    have h := C3S09_run3 a p (r + 2 * m) hp7 (D7Frame_coeff_mem a p)
      (D7Frame_den_units a p hp7) (by omega) (D7Frame_band a r m p ha hp64 hrp hm1)
      r m x.val s hr hp hpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
      k ha hk hroot hgood (hden C3T17_den (by simp))
    simpa only [seventhsPoleSplit, ZMod.natCast_zmod_val] using h
  · obtain ⟨hpar, hx, hlo, hhi, hgood⟩ := h4
    have h := C3S09_run4 a p (r + 2 * m) hp7 (D7Frame_coeff_mem a p)
      (D7Frame_den_units a p hp7) (by omega) (D7Frame_band a r m p ha hp64 hrp hm1)
      r m x.val s hr hp hpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
      k ha hk hroot hgood (hden C3T16_den (by simp))
    simpa only [seventhsPoleSplit, ZMod.natCast_zmod_val] using h
  · obtain ⟨hpar, hx, hlo, hhi, hgood⟩ := h5
    have h := C3S09_run5 a p (r + 2 * m) hp7 (D7Frame_coeff_mem a p)
      (D7Frame_den_units a p hp7) (by omega) (D7Frame_band a r m p ha hp64 hrp hm1)
      r m x.val s hr hp hpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
      k ha hk hroot hgood (hden C3T16_den (by simp))
    simpa only [seventhsPoleSplit, ZMod.natCast_zmod_val] using h
  · obtain ⟨hpar, hx, hlo, hhi, hgood⟩ := h6
    have h := C3S09_run6 a p (r + 2 * m) hp7 (D7Frame_coeff_mem a p)
      (D7Frame_den_units a p hp7) (by omega) (D7Frame_band a r m p ha hp64 hrp hm1)
      r m x.val s hr hp hpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
      k ha hk hroot hgood (hden C3T18_den (by simp))
    simpa only [seventhsPoleSplit, ZMod.natCast_zmod_val] using h
  · obtain ⟨hpar, hx, hlo, hhi, hgood⟩ := h7
    have h := C3S09_run7 a p (r + 2 * m) hp7 (D7Frame_coeff_mem a p)
      (D7Frame_den_units a p hp7) (by omega) (D7Frame_band a r m p ha hp64 hrp hm1)
      r m x.val s hr hp hpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
      k ha hk hroot hgood (hden C3T19_den (by simp))
    simpa only [seventhsPoleSplit, ZMod.natCast_zmod_val] using h
  · exact ⟨FibreCert.triv_ok _ _ _ _, FibreCert.triv_integral _ _ _ _,
      trivCert_realizes _ _ _ _⟩

private theorem C3S09_disjoint0_2 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p)
    (hleft : 1 * r ≤ 4 * p)
    (hright : 26 * p ≤ 7 * r) :
    ¬ (C3S09_test0 r p s x ∧ C3S09_test2 r p s x) := by
  rintro ⟨⟨hpar0, hx0, hlo0, hhi0, hgood0⟩, ⟨hpar1, hx1, hlo1, hhi1, hgood1⟩⟩
  omega

private theorem C3S09_disjoint0_4 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p)
    (hleft : 1 * r ≤ 4 * p)
    (hright : 26 * p ≤ 7 * r) :
    ¬ (C3S09_test0 r p s x ∧ C3S09_test4 r p s x) := by
  rintro ⟨⟨hpar0, hx0, hlo0, hhi0, hgood0⟩, ⟨hpar1, hx1, hlo1, hhi1, hgood1⟩⟩
  omega

private theorem C3S09_disjoint0_6 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p)
    (hleft : 1 * r ≤ 4 * p)
    (hright : 26 * p ≤ 7 * r) :
    ¬ (C3S09_test0 r p s x ∧ C3S09_test6 r p s x) := by
  rintro ⟨⟨hpar0, hx0, hlo0, hhi0, hgood0⟩, ⟨hpar1, hx1, hlo1, hhi1, hgood1⟩⟩
  omega

private theorem C3S09_disjoint1_3 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p)
    (hleft : 1 * r ≤ 4 * p)
    (hright : 26 * p ≤ 7 * r) :
    ¬ (C3S09_test1 r p s x ∧ C3S09_test3 r p s x) := by
  rintro ⟨⟨hpar0, hx0, hlo0, hhi0, hgood0⟩, ⟨hpar1, hx1, hlo1, hhi1, hgood1⟩⟩
  omega

private theorem C3S09_disjoint1_5 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p)
    (hleft : 1 * r ≤ 4 * p)
    (hright : 26 * p ≤ 7 * r) :
    ¬ (C3S09_test1 r p s x ∧ C3S09_test5 r p s x) := by
  rintro ⟨⟨hpar0, hx0, hlo0, hhi0, hgood0⟩, ⟨hpar1, hx1, hlo1, hhi1, hgood1⟩⟩
  omega

private theorem C3S09_disjoint1_7 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p)
    (hleft : 1 * r ≤ 4 * p)
    (hright : 26 * p ≤ 7 * r) :
    ¬ (C3S09_test1 r p s x ∧ C3S09_test7 r p s x) := by
  rintro ⟨⟨hpar0, hx0, hlo0, hhi0, hgood0⟩, ⟨hpar1, hx1, hlo1, hhi1, hgood1⟩⟩
  omega

private theorem C3S09_disjoint2_4 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p)
    (hleft : 1 * r ≤ 4 * p)
    (hright : 26 * p ≤ 7 * r) :
    ¬ (C3S09_test2 r p s x ∧ C3S09_test4 r p s x) := by
  rintro ⟨⟨hpar0, hx0, hlo0, hhi0, hgood0⟩, ⟨hpar1, hx1, hlo1, hhi1, hgood1⟩⟩
  omega

private theorem C3S09_disjoint2_6 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p)
    (hleft : 1 * r ≤ 4 * p)
    (hright : 26 * p ≤ 7 * r) :
    ¬ (C3S09_test2 r p s x ∧ C3S09_test6 r p s x) := by
  rintro ⟨⟨hpar0, hx0, hlo0, hhi0, hgood0⟩, ⟨hpar1, hx1, hlo1, hhi1, hgood1⟩⟩
  omega

private theorem C3S09_disjoint3_5 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p)
    (hleft : 1 * r ≤ 4 * p)
    (hright : 26 * p ≤ 7 * r) :
    ¬ (C3S09_test3 r p s x ∧ C3S09_test5 r p s x) := by
  rintro ⟨⟨hpar0, hx0, hlo0, hhi0, hgood0⟩, ⟨hpar1, hx1, hlo1, hhi1, hgood1⟩⟩
  omega

private theorem C3S09_disjoint3_7 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p)
    (hleft : 1 * r ≤ 4 * p)
    (hright : 26 * p ≤ 7 * r) :
    ¬ (C3S09_test3 r p s x ∧ C3S09_test7 r p s x) := by
  rintro ⟨⟨hpar0, hx0, hlo0, hhi0, hgood0⟩, ⟨hpar1, hx1, hlo1, hhi1, hgood1⟩⟩
  omega

private theorem C3S09_disjoint4_6 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p)
    (hleft : 1 * r ≤ 4 * p)
    (hright : 26 * p ≤ 7 * r) :
    ¬ (C3S09_test4 r p s x ∧ C3S09_test6 r p s x) := by
  rintro ⟨⟨hpar0, hx0, hlo0, hhi0, hgood0⟩, ⟨hpar1, hx1, hlo1, hhi1, hgood1⟩⟩
  omega

private theorem C3S09_disjoint5_7 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p)
    (hleft : 1 * r ≤ 4 * p)
    (hright : 26 * p ≤ 7 * r) :
    ¬ (C3S09_test5 r p s x ∧ C3S09_test7 r p s x) := by
  rintro ⟨⟨hpar0, hx0, hlo0, hhi0, hgood0⟩, ⟨hpar1, hx1, hlo1, hhi1, hgood1⟩⟩
  omega

theorem C3S09_assignment_on_run0 (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : 1 ≤ a ∧ a ≤ 6) (hp64 : 64 ≤ p) (hp7 : ¬ p ∣ 7)
    (hrp : r ≤ 6 * p) (hm1 : 12 * m ≤ r + 6)
    (hleft : 1 * r ≤ 4 * p)
    (hright : 26 * p ≤ 7 * r) (x : ZMod p)
    (hi : C3S09_test0 r p s x) :
    C3S09_assignment a p r m s ha hp64 hp7 hrp hm1 x = C3T14 := by
  simp only [C3S09_assignment, if_pos hi]

theorem C3S09_assignment_on_run1 (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : 1 ≤ a ∧ a ≤ 6) (hp64 : 64 ≤ p) (hp7 : ¬ p ∣ 7)
    (hrp : r ≤ 6 * p) (hm1 : 12 * m ≤ r + 6)
    (hleft : 1 * r ≤ 4 * p)
    (hright : 26 * p ≤ 7 * r) (x : ZMod p)
    (hi : C3S09_test1 r p s x) :
    C3S09_assignment a p r m s ha hp64 hp7 hrp hm1 x = C3T15 := by
  have hn0 : ¬ C3S09_test0 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  simp only [C3S09_assignment, if_neg hn0, if_pos hi]

theorem C3S09_assignment_on_run2 (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : 1 ≤ a ∧ a ≤ 6) (hp64 : 64 ≤ p) (hp7 : ¬ p ∣ 7)
    (hrp : r ≤ 6 * p) (hm1 : 12 * m ≤ r + 6)
    (hleft : 1 * r ≤ 4 * p)
    (hright : 26 * p ≤ 7 * r) (x : ZMod p)
    (hi : C3S09_test2 r p s x) :
    C3S09_assignment a p r m s ha hp64 hp7 hrp hm1 x = C3T17 := by
  have hn0 : ¬ C3S09_test0 r p s x := fun hj => C3S09_disjoint0_2 r p s x hleft hright ⟨hj, hi⟩
  have hn1 : ¬ C3S09_test1 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  simp only [C3S09_assignment, if_neg hn0, if_neg hn1, if_pos hi]

theorem C3S09_assignment_on_run3 (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : 1 ≤ a ∧ a ≤ 6) (hp64 : 64 ≤ p) (hp7 : ¬ p ∣ 7)
    (hrp : r ≤ 6 * p) (hm1 : 12 * m ≤ r + 6)
    (hleft : 1 * r ≤ 4 * p)
    (hright : 26 * p ≤ 7 * r) (x : ZMod p)
    (hi : C3S09_test3 r p s x) :
    C3S09_assignment a p r m s ha hp64 hp7 hrp hm1 x = C3T17 := by
  have hn0 : ¬ C3S09_test0 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  have hn1 : ¬ C3S09_test1 r p s x := fun hj => C3S09_disjoint1_3 r p s x hleft hright ⟨hj, hi⟩
  have hn2 : ¬ C3S09_test2 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  simp only [C3S09_assignment, if_neg hn0, if_neg hn1, if_neg hn2, if_pos hi]

theorem C3S09_assignment_on_run4 (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : 1 ≤ a ∧ a ≤ 6) (hp64 : 64 ≤ p) (hp7 : ¬ p ∣ 7)
    (hrp : r ≤ 6 * p) (hm1 : 12 * m ≤ r + 6)
    (hleft : 1 * r ≤ 4 * p)
    (hright : 26 * p ≤ 7 * r) (x : ZMod p)
    (hi : C3S09_test4 r p s x) :
    C3S09_assignment a p r m s ha hp64 hp7 hrp hm1 x = C3T16 := by
  have hn0 : ¬ C3S09_test0 r p s x := fun hj => C3S09_disjoint0_4 r p s x hleft hright ⟨hj, hi⟩
  have hn1 : ¬ C3S09_test1 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  have hn2 : ¬ C3S09_test2 r p s x := fun hj => C3S09_disjoint2_4 r p s x hleft hright ⟨hj, hi⟩
  have hn3 : ¬ C3S09_test3 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  simp only [C3S09_assignment, if_neg hn0, if_neg hn1, if_neg hn2, if_neg hn3, if_pos hi]

theorem C3S09_assignment_on_run5 (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : 1 ≤ a ∧ a ≤ 6) (hp64 : 64 ≤ p) (hp7 : ¬ p ∣ 7)
    (hrp : r ≤ 6 * p) (hm1 : 12 * m ≤ r + 6)
    (hleft : 1 * r ≤ 4 * p)
    (hright : 26 * p ≤ 7 * r) (x : ZMod p)
    (hi : C3S09_test5 r p s x) :
    C3S09_assignment a p r m s ha hp64 hp7 hrp hm1 x = C3T16 := by
  have hn0 : ¬ C3S09_test0 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  have hn1 : ¬ C3S09_test1 r p s x := fun hj => C3S09_disjoint1_5 r p s x hleft hright ⟨hj, hi⟩
  have hn2 : ¬ C3S09_test2 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  have hn3 : ¬ C3S09_test3 r p s x := fun hj => C3S09_disjoint3_5 r p s x hleft hright ⟨hj, hi⟩
  have hn4 : ¬ C3S09_test4 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  simp only [C3S09_assignment, if_neg hn0, if_neg hn1, if_neg hn2, if_neg hn3, if_neg hn4, if_pos hi]

theorem C3S09_assignment_on_run6 (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : 1 ≤ a ∧ a ≤ 6) (hp64 : 64 ≤ p) (hp7 : ¬ p ∣ 7)
    (hrp : r ≤ 6 * p) (hm1 : 12 * m ≤ r + 6)
    (hleft : 1 * r ≤ 4 * p)
    (hright : 26 * p ≤ 7 * r) (x : ZMod p)
    (hi : C3S09_test6 r p s x) :
    C3S09_assignment a p r m s ha hp64 hp7 hrp hm1 x = C3T18 := by
  have hn0 : ¬ C3S09_test0 r p s x := fun hj => C3S09_disjoint0_6 r p s x hleft hright ⟨hj, hi⟩
  have hn1 : ¬ C3S09_test1 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  have hn2 : ¬ C3S09_test2 r p s x := fun hj => C3S09_disjoint2_6 r p s x hleft hright ⟨hj, hi⟩
  have hn3 : ¬ C3S09_test3 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  have hn4 : ¬ C3S09_test4 r p s x := fun hj => C3S09_disjoint4_6 r p s x hleft hright ⟨hj, hi⟩
  have hn5 : ¬ C3S09_test5 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  simp only [C3S09_assignment, if_neg hn0, if_neg hn1, if_neg hn2, if_neg hn3, if_neg hn4, if_neg hn5, if_pos hi]

theorem C3S09_assignment_on_run7 (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : 1 ≤ a ∧ a ≤ 6) (hp64 : 64 ≤ p) (hp7 : ¬ p ∣ 7)
    (hrp : r ≤ 6 * p) (hm1 : 12 * m ≤ r + 6)
    (hleft : 1 * r ≤ 4 * p)
    (hright : 26 * p ≤ 7 * r) (x : ZMod p)
    (hi : C3S09_test7 r p s x) :
    C3S09_assignment a p r m s ha hp64 hp7 hrp hm1 x = C3T19 := by
  have hn0 : ¬ C3S09_test0 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  have hn1 : ¬ C3S09_test1 r p s x := fun hj => C3S09_disjoint1_7 r p s x hleft hright ⟨hj, hi⟩
  have hn2 : ¬ C3S09_test2 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  have hn3 : ¬ C3S09_test3 r p s x := fun hj => C3S09_disjoint3_7 r p s x hleft hright ⟨hj, hi⟩
  have hn4 : ¬ C3S09_test4 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  have hn5 : ¬ C3S09_test5 r p s x := fun hj => C3S09_disjoint5_7 r p s x hleft hright ⟨hj, hi⟩
  have hn6 : ¬ C3S09_test6 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  simp only [C3S09_assignment, if_neg hn0, if_neg hn1, if_neg hn2, if_neg hn3, if_neg hn4, if_neg hn5, if_neg hn6, if_pos hi]

#print axioms C3S09_assignment_valid
#print axioms C3S09_assignment_on_run0

#print axioms C3S09_run0
end CatalanCore.Uniform.Bank.Sevenths.RankFibre
