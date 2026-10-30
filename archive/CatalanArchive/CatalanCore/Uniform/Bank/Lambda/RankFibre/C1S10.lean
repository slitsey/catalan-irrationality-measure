import CatalanCore.Uniform.Bank.Lambda.CommonMinorRealize
import CatalanCore.Uniform.Bank.Lambda.Boundary
import CatalanCore.Uniform.Bank.Lambda.Band
import CatalanCore.Uniform.Bank.Lambda.RankSource.C1S10
import CatalanCore.Uniform.Bank.Lambda.RankPalette.C1T14
import CatalanCore.Uniform.Bank.Lambda.RankPalette.C1T17
import CatalanCore.Uniform.Bank.Lambda.RankPalette.C1T18
import CatalanCore.Uniform.Bank.Lambda.RankPalette.C1T19
import CatalanCore.Uniform.Bank.Lambda.RankPalette.C1T20
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Lambda.RankFibre
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.RankProducer
open CatalanCore.Uniform.Bank.Chi3Rank RankSource RankData
open scoped Classical

theorem C1S10_run0 (a p Bnd : ℕ) [Fact p.Prime] (hp4 : ¬ p ∣ 4)
    (hc : ∀ j, (D4 a).c j ∈ S p) (hpq : ∀ j, ¬ p ∣ (D4 a).q j)
    (hp3 : 3 ≤ p) (hbd : ∀ j, (D4 a).q j * Bnd + (D4 a).u j ≤ p ^ 2)
    (r m x : ℕ) (s : Finset (Fin r)) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 0) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 10 * m ≤ r + 5) (hm2 : r ≤ 10 * m + 5) (hrp : r ≤ 5 * p)
    (hleft : 2 * r ≤ 5 * p)
    (hright : 9 * p ≤ 4 * r)
    (hlo : (1 : ℤ) * x ≥ (0 : ℤ) * r + (0 : ℤ) * p + 4)
    (hhi : (4 : ℤ) * x ≤ (0 : ℤ) * r + (1 : ℤ) * p - 16)
    (k : ℕ) (ha : a = 1 ∨ a = 3) (hk : k < p) (hroot : 4 * k + a = 1 * p)
    (hgood : x ∉ deletedResidues r p s) (hden : ¬ p ∣ C1T19_den) :
    C1T19.Ok ∧ C1T19.Integral p ∧
      Realizes ((D4 a).poleSplit Bnd hc hpq hp3 hbd)
        (rowsOf r m s) (colsOf r m s) (x : ZMod p) C1T19 := by
  refine ⟨C1T19_ok, C1T19_integral p hden, ?_⟩
  apply realizes_commonMinor_D4 a p Bnd hp4 hc hpq hp3 hbd r m s k 1 x 0
    hk (by omega) hxp
    (C1S10_run0_bit r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi a k ha hroot)
    C1T19
  · exact C1S10_run0_R r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact C1S10_run0_C r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact kept_of_not_deleted r p s x hxp hgood
  · exact C1T19_palette.1
  · exact fun d hd => (C1T19_palette.2 d hd).1

theorem C1S10_run1 (a p Bnd : ℕ) [Fact p.Prime] (hp4 : ¬ p ∣ 4)
    (hc : ∀ j, (D4 a).c j ∈ S p) (hpq : ∀ j, ¬ p ∣ (D4 a).q j)
    (hp3 : 3 ≤ p) (hbd : ∀ j, (D4 a).q j * Bnd + (D4 a).u j ≤ p ^ 2)
    (r m x : ℕ) (s : Finset (Fin r)) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 1) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 10 * m ≤ r + 5) (hm2 : r ≤ 10 * m + 5) (hrp : r ≤ 5 * p)
    (hleft : 2 * r ≤ 5 * p)
    (hright : 9 * p ≤ 4 * r)
    (hlo : (1 : ℤ) * x ≥ (0 : ℤ) * r + (0 : ℤ) * p + 4)
    (hhi : (4 : ℤ) * x ≤ (0 : ℤ) * r + (1 : ℤ) * p - 16)
    (k : ℕ) (ha : a = 1 ∨ a = 3) (hk : k < p) (hroot : 4 * k + a = 1 * p)
    (hgood : x ∉ deletedResidues r p s) (hden : ¬ p ∣ C1T19_den) :
    C1T19.Ok ∧ C1T19.Integral p ∧
      Realizes ((D4 a).poleSplit Bnd hc hpq hp3 hbd)
        (rowsOf r m s) (colsOf r m s) (x : ZMod p) C1T19 := by
  refine ⟨C1T19_ok, C1T19_integral p hden, ?_⟩
  apply realizes_commonMinor_D4 a p Bnd hp4 hc hpq hp3 hbd r m s k 1 x 0
    hk (by omega) hxp
    (C1S10_run1_bit r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi a k ha hroot)
    C1T19
  · exact C1S10_run1_R r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact C1S10_run1_C r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact kept_of_not_deleted r p s x hxp hgood
  · exact C1T19_palette.1
  · exact fun d hd => (C1T19_palette.2 d hd).1

theorem C1S10_run2 (a p Bnd : ℕ) [Fact p.Prime] (hp4 : ¬ p ∣ 4)
    (hc : ∀ j, (D4 a).c j ∈ S p) (hpq : ∀ j, ¬ p ∣ (D4 a).q j)
    (hp3 : 3 ≤ p) (hbd : ∀ j, (D4 a).q j * Bnd + (D4 a).u j ≤ p ^ 2)
    (r m x : ℕ) (s : Finset (Fin r)) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 0) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 10 * m ≤ r + 5) (hm2 : r ≤ 10 * m + 5) (hrp : r ≤ 5 * p)
    (hleft : 2 * r ≤ 5 * p)
    (hright : 9 * p ≤ 4 * r)
    (hlo : (4 : ℤ) * x ≥ (0 : ℤ) * r + (1 : ℤ) * p + 16)
    (hhi : (1 : ℤ) * x ≤ (1 : ℤ) * r + (-2 : ℤ) * p - 4)
    (k : ℕ) (ha : a = 1 ∨ a = 3) (hk : k < p) (hroot : 4 * k + a = 1 * p)
    (hgood : x ∉ deletedResidues r p s) (hden : ¬ p ∣ C1T14_den) :
    C1T14.Ok ∧ C1T14.Integral p ∧
      Realizes ((D4 a).poleSplit Bnd hc hpq hp3 hbd)
        (rowsOf r m s) (colsOf r m s) (x : ZMod p) C1T14 := by
  refine ⟨C1T14_ok, C1T14_integral p hden, ?_⟩
  apply realizes_commonMinor_D4 a p Bnd hp4 hc hpq hp3 hbd r m s k 1 x 1
    hk (by omega) hxp
    (C1S10_run2_bit r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi a k ha hroot)
    C1T14
  · exact C1S10_run2_R r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact C1S10_run2_C r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact kept_of_not_deleted r p s x hxp hgood
  · exact C1T14_palette.1
  · exact fun d hd => (C1T14_palette.2 d hd).1

theorem C1S10_run3 (a p Bnd : ℕ) [Fact p.Prime] (hp4 : ¬ p ∣ 4)
    (hc : ∀ j, (D4 a).c j ∈ S p) (hpq : ∀ j, ¬ p ∣ (D4 a).q j)
    (hp3 : 3 ≤ p) (hbd : ∀ j, (D4 a).q j * Bnd + (D4 a).u j ≤ p ^ 2)
    (r m x : ℕ) (s : Finset (Fin r)) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 1) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 10 * m ≤ r + 5) (hm2 : r ≤ 10 * m + 5) (hrp : r ≤ 5 * p)
    (hleft : 2 * r ≤ 5 * p)
    (hright : 9 * p ≤ 4 * r)
    (hlo : (4 : ℤ) * x ≥ (0 : ℤ) * r + (1 : ℤ) * p + 16)
    (hhi : (1 : ℤ) * x ≤ (1 : ℤ) * r + (-2 : ℤ) * p - 4)
    (k : ℕ) (ha : a = 1 ∨ a = 3) (hk : k < p) (hroot : 4 * k + a = 1 * p)
    (hgood : x ∉ deletedResidues r p s) (hden : ¬ p ∣ C1T14_den) :
    C1T14.Ok ∧ C1T14.Integral p ∧
      Realizes ((D4 a).poleSplit Bnd hc hpq hp3 hbd)
        (rowsOf r m s) (colsOf r m s) (x : ZMod p) C1T14 := by
  refine ⟨C1T14_ok, C1T14_integral p hden, ?_⟩
  apply realizes_commonMinor_D4 a p Bnd hp4 hc hpq hp3 hbd r m s k 1 x 1
    hk (by omega) hxp
    (C1S10_run3_bit r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi a k ha hroot)
    C1T14
  · exact C1S10_run3_R r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact C1S10_run3_C r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact kept_of_not_deleted r p s x hxp hgood
  · exact C1T14_palette.1
  · exact fun d hd => (C1T14_palette.2 d hd).1

theorem C1S10_run4 (a p Bnd : ℕ) [Fact p.Prime] (hp4 : ¬ p ∣ 4)
    (hc : ∀ j, (D4 a).c j ∈ S p) (hpq : ∀ j, ¬ p ∣ (D4 a).q j)
    (hp3 : 3 ≤ p) (hbd : ∀ j, (D4 a).q j * Bnd + (D4 a).u j ≤ p ^ 2)
    (r m x : ℕ) (s : Finset (Fin r)) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 0) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 10 * m ≤ r + 5) (hm2 : r ≤ 10 * m + 5) (hrp : r ≤ 5 * p)
    (hleft : 2 * r ≤ 5 * p)
    (hright : 9 * p ≤ 4 * r)
    (hlo : (1 : ℤ) * x ≥ (1 : ℤ) * r + (-2 : ℤ) * p + 4)
    (hhi : (5 : ℤ) * x ≤ (6 : ℤ) * r + (-10 : ℤ) * p - 20)
    (k : ℕ) (ha : a = 1 ∨ a = 3) (hk : k < p) (hroot : 4 * k + a = 1 * p)
    (hgood : x ∉ deletedResidues r p s) (hden : ¬ p ∣ C1T17_den) :
    C1T17.Ok ∧ C1T17.Integral p ∧
      Realizes ((D4 a).poleSplit Bnd hc hpq hp3 hbd)
        (rowsOf r m s) (colsOf r m s) (x : ZMod p) C1T17 := by
  refine ⟨C1T17_ok, C1T17_integral p hden, ?_⟩
  apply realizes_commonMinor_D4 a p Bnd hp4 hc hpq hp3 hbd r m s k 1 x 1
    hk (by omega) hxp
    (C1S10_run4_bit r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi a k ha hroot)
    C1T17
  · exact C1S10_run4_R r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact C1S10_run4_C r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact kept_of_not_deleted r p s x hxp hgood
  · exact C1T17_palette.1
  · exact fun d hd => (C1T17_palette.2 d hd).1

theorem C1S10_run5 (a p Bnd : ℕ) [Fact p.Prime] (hp4 : ¬ p ∣ 4)
    (hc : ∀ j, (D4 a).c j ∈ S p) (hpq : ∀ j, ¬ p ∣ (D4 a).q j)
    (hp3 : 3 ≤ p) (hbd : ∀ j, (D4 a).q j * Bnd + (D4 a).u j ≤ p ^ 2)
    (r m x : ℕ) (s : Finset (Fin r)) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 1) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 10 * m ≤ r + 5) (hm2 : r ≤ 10 * m + 5) (hrp : r ≤ 5 * p)
    (hleft : 2 * r ≤ 5 * p)
    (hright : 9 * p ≤ 4 * r)
    (hlo : (1 : ℤ) * x ≥ (1 : ℤ) * r + (-2 : ℤ) * p + 4)
    (hhi : (5 : ℤ) * x ≤ (6 : ℤ) * r + (-10 : ℤ) * p - 20)
    (k : ℕ) (ha : a = 1 ∨ a = 3) (hk : k < p) (hroot : 4 * k + a = 1 * p)
    (hgood : x ∉ deletedResidues r p s) (hden : ¬ p ∣ C1T18_den) :
    C1T18.Ok ∧ C1T18.Integral p ∧
      Realizes ((D4 a).poleSplit Bnd hc hpq hp3 hbd)
        (rowsOf r m s) (colsOf r m s) (x : ZMod p) C1T18 := by
  refine ⟨C1T18_ok, C1T18_integral p hden, ?_⟩
  apply realizes_commonMinor_D4 a p Bnd hp4 hc hpq hp3 hbd r m s k 1 x 1
    hk (by omega) hxp
    (C1S10_run5_bit r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi a k ha hroot)
    C1T18
  · exact C1S10_run5_R r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact C1S10_run5_C r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact kept_of_not_deleted r p s x hxp hgood
  · exact C1T18_palette.1
  · exact fun d hd => (C1T18_palette.2 d hd).1

theorem C1S10_run6 (a p Bnd : ℕ) [Fact p.Prime] (hp4 : ¬ p ∣ 4)
    (hc : ∀ j, (D4 a).c j ∈ S p) (hpq : ∀ j, ¬ p ∣ (D4 a).q j)
    (hp3 : 3 ≤ p) (hbd : ∀ j, (D4 a).q j * Bnd + (D4 a).u j ≤ p ^ 2)
    (r m x : ℕ) (s : Finset (Fin r)) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 0) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 10 * m ≤ r + 5) (hm2 : r ≤ 10 * m + 5) (hrp : r ≤ 5 * p)
    (hleft : 2 * r ≤ 5 * p)
    (hright : 9 * p ≤ 4 * r)
    (hlo : (5 : ℤ) * x ≥ (6 : ℤ) * r + (-10 : ℤ) * p + 20)
    (hhi : (1 : ℤ) * x ≤ (0 : ℤ) * r + (1 : ℤ) * p - 4)
    (k : ℕ) (ha : a = 1 ∨ a = 3) (hk : k < p) (hroot : 4 * k + a = 1 * p)
    (hgood : x ∉ deletedResidues r p s) (hden : ¬ p ∣ C1T20_den) :
    C1T20.Ok ∧ C1T20.Integral p ∧
      Realizes ((D4 a).poleSplit Bnd hc hpq hp3 hbd)
        (rowsOf r m s) (colsOf r m s) (x : ZMod p) C1T20 := by
  refine ⟨C1T20_ok, C1T20_integral p hden, ?_⟩
  apply realizes_commonMinor_D4 a p Bnd hp4 hc hpq hp3 hbd r m s k 1 x 1
    hk (by omega) hxp
    (C1S10_run6_bit r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi a k ha hroot)
    C1T20
  · exact C1S10_run6_R r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact C1S10_run6_C r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact kept_of_not_deleted r p s x hxp hgood
  · exact C1T20_palette.1
  · exact fun d hd => (C1T20_palette.2 d hd).1

theorem C1S10_run7 (a p Bnd : ℕ) [Fact p.Prime] (hp4 : ¬ p ∣ 4)
    (hc : ∀ j, (D4 a).c j ∈ S p) (hpq : ∀ j, ¬ p ∣ (D4 a).q j)
    (hp3 : 3 ≤ p) (hbd : ∀ j, (D4 a).q j * Bnd + (D4 a).u j ≤ p ^ 2)
    (r m x : ℕ) (s : Finset (Fin r)) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 1) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 10 * m ≤ r + 5) (hm2 : r ≤ 10 * m + 5) (hrp : r ≤ 5 * p)
    (hleft : 2 * r ≤ 5 * p)
    (hright : 9 * p ≤ 4 * r)
    (hlo : (5 : ℤ) * x ≥ (6 : ℤ) * r + (-10 : ℤ) * p + 20)
    (hhi : (1 : ℤ) * x ≤ (0 : ℤ) * r + (1 : ℤ) * p - 4)
    (k : ℕ) (ha : a = 1 ∨ a = 3) (hk : k < p) (hroot : 4 * k + a = 1 * p)
    (hgood : x ∉ deletedResidues r p s) (hden : ¬ p ∣ C1T20_den) :
    C1T20.Ok ∧ C1T20.Integral p ∧
      Realizes ((D4 a).poleSplit Bnd hc hpq hp3 hbd)
        (rowsOf r m s) (colsOf r m s) (x : ZMod p) C1T20 := by
  refine ⟨C1T20_ok, C1T20_integral p hden, ?_⟩
  apply realizes_commonMinor_D4 a p Bnd hp4 hc hpq hp3 hbd r m s k 1 x 1
    hk (by omega) hxp
    (C1S10_run7_bit r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi a k ha hroot)
    C1T20
  · exact C1S10_run7_R r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact C1S10_run7_C r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact kept_of_not_deleted r p s x hxp hgood
  · exact C1T20_palette.1
  · exact fun d hd => (C1T20_palette.2 d hd).1

noncomputable def C1S10_test0 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p) : Prop :=
  x.val % 2 = 0 ∧ 4 ≤ x.val ∧
    (0 : ℤ) * r + (0 : ℤ) * p + 4 ≤ (1 : ℤ) * x.val ∧
    (4 : ℤ) * x.val ≤ (0 : ℤ) * r + (1 : ℤ) * p - 16 ∧
    x.val ∉ deletedResidues r p s
noncomputable def C1S10_test1 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p) : Prop :=
  x.val % 2 = 1 ∧ 4 ≤ x.val ∧
    (0 : ℤ) * r + (0 : ℤ) * p + 4 ≤ (1 : ℤ) * x.val ∧
    (4 : ℤ) * x.val ≤ (0 : ℤ) * r + (1 : ℤ) * p - 16 ∧
    x.val ∉ deletedResidues r p s
noncomputable def C1S10_test2 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p) : Prop :=
  x.val % 2 = 0 ∧ 4 ≤ x.val ∧
    (0 : ℤ) * r + (1 : ℤ) * p + 16 ≤ (4 : ℤ) * x.val ∧
    (1 : ℤ) * x.val ≤ (1 : ℤ) * r + (-2 : ℤ) * p - 4 ∧
    x.val ∉ deletedResidues r p s
noncomputable def C1S10_test3 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p) : Prop :=
  x.val % 2 = 1 ∧ 4 ≤ x.val ∧
    (0 : ℤ) * r + (1 : ℤ) * p + 16 ≤ (4 : ℤ) * x.val ∧
    (1 : ℤ) * x.val ≤ (1 : ℤ) * r + (-2 : ℤ) * p - 4 ∧
    x.val ∉ deletedResidues r p s
noncomputable def C1S10_test4 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p) : Prop :=
  x.val % 2 = 0 ∧ 4 ≤ x.val ∧
    (1 : ℤ) * r + (-2 : ℤ) * p + 4 ≤ (1 : ℤ) * x.val ∧
    (5 : ℤ) * x.val ≤ (6 : ℤ) * r + (-10 : ℤ) * p - 20 ∧
    x.val ∉ deletedResidues r p s
noncomputable def C1S10_test5 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p) : Prop :=
  x.val % 2 = 1 ∧ 4 ≤ x.val ∧
    (1 : ℤ) * r + (-2 : ℤ) * p + 4 ≤ (1 : ℤ) * x.val ∧
    (5 : ℤ) * x.val ≤ (6 : ℤ) * r + (-10 : ℤ) * p - 20 ∧
    x.val ∉ deletedResidues r p s
noncomputable def C1S10_test6 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p) : Prop :=
  x.val % 2 = 0 ∧ 4 ≤ x.val ∧
    (6 : ℤ) * r + (-10 : ℤ) * p + 20 ≤ (5 : ℤ) * x.val ∧
    (1 : ℤ) * x.val ≤ (0 : ℤ) * r + (1 : ℤ) * p - 4 ∧
    x.val ∉ deletedResidues r p s
noncomputable def C1S10_test7 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p) : Prop :=
  x.val % 2 = 1 ∧ 4 ≤ x.val ∧
    (6 : ℤ) * r + (-10 : ℤ) * p + 20 ≤ (5 : ℤ) * x.val ∧
    (1 : ℤ) * x.val ≤ (0 : ℤ) * r + (1 : ℤ) * p - 4 ∧
    x.val ∉ deletedResidues r p s

noncomputable def C1S10_assignment (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : a = 1 ∨ a = 3) (hp29 : 29 ≤ p) (hp4 : ¬ p ∣ 4)
    (hrp : r ≤ 5 * p) (hm1 : 10 * m ≤ r + 5) : ZMod p → FibreCert := fun x =>
  if C1S10_test0 r p s x then C1T19 else
  if C1S10_test1 r p s x then C1T19 else
  if C1S10_test2 r p s x then C1T14 else
  if C1S10_test3 r p s x then C1T14 else
  if C1S10_test4 r p s x then C1T17 else
  if C1S10_test5 r p s x then C1T18 else
  if C1S10_test6 r p s x then C1T20 else
  if C1S10_test7 r p s x then C1T20 else
  trivCert (lambdaPoleSplit a p r m ha hp29 hp4 hrp hm1) (rowsOf r m s) (colsOf r m s) x

theorem C1S10_assignment_valid (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : a = 1 ∨ a = 3) (hp29 : 29 ≤ p) (hp4 : ¬ p ∣ 4)
    (hrp : r ≤ 5 * p) (hm1 : 10 * m ≤ r + 5)
    (hr : r % 2 = 0) (hp : p % 2 = 1) (hm2 : r ≤ 10 * m + 5)
    (hleft : 2 * r ≤ 5 * p)
    (hright : 9 * p ≤ 4 * r)
    (k : ℕ) (hk : k < p) (hroot : 4 * k + a = 1 * p)
    (hden : ∀ N ∈ ([C1T14_den, C1T17_den, C1T18_den, C1T19_den, C1T20_den] : List ℕ), ¬ p ∣ N) (x : ZMod p) :
    (C1S10_assignment a p r m s ha hp29 hp4 hrp hm1 x).Ok ∧
    (C1S10_assignment a p r m s ha hp29 hp4 hrp hm1 x).Integral p ∧
    Realizes (lambdaPoleSplit a p r m ha hp29 hp4 hrp hm1)
      (rowsOf r m s) (colsOf r m s) x
      (C1S10_assignment a p r m s ha hp29 hp4 hrp hm1 x) := by
  have hxp : x.val < p := ZMod.val_lt x
  unfold C1S10_assignment
  split_ifs with h0 h1 h2 h3 h4 h5 h6 h7
  · obtain ⟨hpar, hx, hlo, hhi, hgood⟩ := h0
    have h := C1S10_run0 a p (r + 2 * m) hp4 (D4_coeff_mem a p)
      (D4_den_units a p hp4) (by omega) (D4_band a r m p ha hp29 hrp hm1)
      r m x.val s hr hp hpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
      k ha hk hroot hgood (hden C1T19_den (by simp))
    simpa only [lambdaPoleSplit, ZMod.natCast_zmod_val] using h
  · obtain ⟨hpar, hx, hlo, hhi, hgood⟩ := h1
    have h := C1S10_run1 a p (r + 2 * m) hp4 (D4_coeff_mem a p)
      (D4_den_units a p hp4) (by omega) (D4_band a r m p ha hp29 hrp hm1)
      r m x.val s hr hp hpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
      k ha hk hroot hgood (hden C1T19_den (by simp))
    simpa only [lambdaPoleSplit, ZMod.natCast_zmod_val] using h
  · obtain ⟨hpar, hx, hlo, hhi, hgood⟩ := h2
    have h := C1S10_run2 a p (r + 2 * m) hp4 (D4_coeff_mem a p)
      (D4_den_units a p hp4) (by omega) (D4_band a r m p ha hp29 hrp hm1)
      r m x.val s hr hp hpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
      k ha hk hroot hgood (hden C1T14_den (by simp))
    simpa only [lambdaPoleSplit, ZMod.natCast_zmod_val] using h
  · obtain ⟨hpar, hx, hlo, hhi, hgood⟩ := h3
    have h := C1S10_run3 a p (r + 2 * m) hp4 (D4_coeff_mem a p)
      (D4_den_units a p hp4) (by omega) (D4_band a r m p ha hp29 hrp hm1)
      r m x.val s hr hp hpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
      k ha hk hroot hgood (hden C1T14_den (by simp))
    simpa only [lambdaPoleSplit, ZMod.natCast_zmod_val] using h
  · obtain ⟨hpar, hx, hlo, hhi, hgood⟩ := h4
    have h := C1S10_run4 a p (r + 2 * m) hp4 (D4_coeff_mem a p)
      (D4_den_units a p hp4) (by omega) (D4_band a r m p ha hp29 hrp hm1)
      r m x.val s hr hp hpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
      k ha hk hroot hgood (hden C1T17_den (by simp))
    simpa only [lambdaPoleSplit, ZMod.natCast_zmod_val] using h
  · obtain ⟨hpar, hx, hlo, hhi, hgood⟩ := h5
    have h := C1S10_run5 a p (r + 2 * m) hp4 (D4_coeff_mem a p)
      (D4_den_units a p hp4) (by omega) (D4_band a r m p ha hp29 hrp hm1)
      r m x.val s hr hp hpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
      k ha hk hroot hgood (hden C1T18_den (by simp))
    simpa only [lambdaPoleSplit, ZMod.natCast_zmod_val] using h
  · obtain ⟨hpar, hx, hlo, hhi, hgood⟩ := h6
    have h := C1S10_run6 a p (r + 2 * m) hp4 (D4_coeff_mem a p)
      (D4_den_units a p hp4) (by omega) (D4_band a r m p ha hp29 hrp hm1)
      r m x.val s hr hp hpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
      k ha hk hroot hgood (hden C1T20_den (by simp))
    simpa only [lambdaPoleSplit, ZMod.natCast_zmod_val] using h
  · obtain ⟨hpar, hx, hlo, hhi, hgood⟩ := h7
    have h := C1S10_run7 a p (r + 2 * m) hp4 (D4_coeff_mem a p)
      (D4_den_units a p hp4) (by omega) (D4_band a r m p ha hp29 hrp hm1)
      r m x.val s hr hp hpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
      k ha hk hroot hgood (hden C1T20_den (by simp))
    simpa only [lambdaPoleSplit, ZMod.natCast_zmod_val] using h
  · exact ⟨FibreCert.triv_ok _ _ _ _, FibreCert.triv_integral _ _ _ _,
      trivCert_realizes _ _ _ _⟩

private theorem C1S10_disjoint0_2 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p)
    (hleft : 2 * r ≤ 5 * p)
    (hright : 9 * p ≤ 4 * r) :
    ¬ (C1S10_test0 r p s x ∧ C1S10_test2 r p s x) := by
  rintro ⟨⟨hpar0, hx0, hlo0, hhi0, hgood0⟩, ⟨hpar1, hx1, hlo1, hhi1, hgood1⟩⟩
  omega

private theorem C1S10_disjoint0_4 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p)
    (hleft : 2 * r ≤ 5 * p)
    (hright : 9 * p ≤ 4 * r) :
    ¬ (C1S10_test0 r p s x ∧ C1S10_test4 r p s x) := by
  rintro ⟨⟨hpar0, hx0, hlo0, hhi0, hgood0⟩, ⟨hpar1, hx1, hlo1, hhi1, hgood1⟩⟩
  omega

private theorem C1S10_disjoint0_6 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p)
    (hleft : 2 * r ≤ 5 * p)
    (hright : 9 * p ≤ 4 * r) :
    ¬ (C1S10_test0 r p s x ∧ C1S10_test6 r p s x) := by
  rintro ⟨⟨hpar0, hx0, hlo0, hhi0, hgood0⟩, ⟨hpar1, hx1, hlo1, hhi1, hgood1⟩⟩
  omega

private theorem C1S10_disjoint1_3 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p)
    (hleft : 2 * r ≤ 5 * p)
    (hright : 9 * p ≤ 4 * r) :
    ¬ (C1S10_test1 r p s x ∧ C1S10_test3 r p s x) := by
  rintro ⟨⟨hpar0, hx0, hlo0, hhi0, hgood0⟩, ⟨hpar1, hx1, hlo1, hhi1, hgood1⟩⟩
  omega

private theorem C1S10_disjoint1_5 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p)
    (hleft : 2 * r ≤ 5 * p)
    (hright : 9 * p ≤ 4 * r) :
    ¬ (C1S10_test1 r p s x ∧ C1S10_test5 r p s x) := by
  rintro ⟨⟨hpar0, hx0, hlo0, hhi0, hgood0⟩, ⟨hpar1, hx1, hlo1, hhi1, hgood1⟩⟩
  omega

private theorem C1S10_disjoint1_7 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p)
    (hleft : 2 * r ≤ 5 * p)
    (hright : 9 * p ≤ 4 * r) :
    ¬ (C1S10_test1 r p s x ∧ C1S10_test7 r p s x) := by
  rintro ⟨⟨hpar0, hx0, hlo0, hhi0, hgood0⟩, ⟨hpar1, hx1, hlo1, hhi1, hgood1⟩⟩
  omega

private theorem C1S10_disjoint2_4 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p)
    (hleft : 2 * r ≤ 5 * p)
    (hright : 9 * p ≤ 4 * r) :
    ¬ (C1S10_test2 r p s x ∧ C1S10_test4 r p s x) := by
  rintro ⟨⟨hpar0, hx0, hlo0, hhi0, hgood0⟩, ⟨hpar1, hx1, hlo1, hhi1, hgood1⟩⟩
  omega

private theorem C1S10_disjoint2_6 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p)
    (hleft : 2 * r ≤ 5 * p)
    (hright : 9 * p ≤ 4 * r) :
    ¬ (C1S10_test2 r p s x ∧ C1S10_test6 r p s x) := by
  rintro ⟨⟨hpar0, hx0, hlo0, hhi0, hgood0⟩, ⟨hpar1, hx1, hlo1, hhi1, hgood1⟩⟩
  omega

private theorem C1S10_disjoint3_5 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p)
    (hleft : 2 * r ≤ 5 * p)
    (hright : 9 * p ≤ 4 * r) :
    ¬ (C1S10_test3 r p s x ∧ C1S10_test5 r p s x) := by
  rintro ⟨⟨hpar0, hx0, hlo0, hhi0, hgood0⟩, ⟨hpar1, hx1, hlo1, hhi1, hgood1⟩⟩
  omega

private theorem C1S10_disjoint3_7 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p)
    (hleft : 2 * r ≤ 5 * p)
    (hright : 9 * p ≤ 4 * r) :
    ¬ (C1S10_test3 r p s x ∧ C1S10_test7 r p s x) := by
  rintro ⟨⟨hpar0, hx0, hlo0, hhi0, hgood0⟩, ⟨hpar1, hx1, hlo1, hhi1, hgood1⟩⟩
  omega

private theorem C1S10_disjoint4_6 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p)
    (hleft : 2 * r ≤ 5 * p)
    (hright : 9 * p ≤ 4 * r) :
    ¬ (C1S10_test4 r p s x ∧ C1S10_test6 r p s x) := by
  rintro ⟨⟨hpar0, hx0, hlo0, hhi0, hgood0⟩, ⟨hpar1, hx1, hlo1, hhi1, hgood1⟩⟩
  omega

private theorem C1S10_disjoint5_7 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p)
    (hleft : 2 * r ≤ 5 * p)
    (hright : 9 * p ≤ 4 * r) :
    ¬ (C1S10_test5 r p s x ∧ C1S10_test7 r p s x) := by
  rintro ⟨⟨hpar0, hx0, hlo0, hhi0, hgood0⟩, ⟨hpar1, hx1, hlo1, hhi1, hgood1⟩⟩
  omega

theorem C1S10_assignment_on_run0 (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : a = 1 ∨ a = 3) (hp29 : 29 ≤ p) (hp4 : ¬ p ∣ 4)
    (hrp : r ≤ 5 * p) (hm1 : 10 * m ≤ r + 5)
    (hleft : 2 * r ≤ 5 * p)
    (hright : 9 * p ≤ 4 * r) (x : ZMod p)
    (hi : C1S10_test0 r p s x) :
    C1S10_assignment a p r m s ha hp29 hp4 hrp hm1 x = C1T19 := by
  simp only [C1S10_assignment, if_pos hi]

theorem C1S10_assignment_on_run1 (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : a = 1 ∨ a = 3) (hp29 : 29 ≤ p) (hp4 : ¬ p ∣ 4)
    (hrp : r ≤ 5 * p) (hm1 : 10 * m ≤ r + 5)
    (hleft : 2 * r ≤ 5 * p)
    (hright : 9 * p ≤ 4 * r) (x : ZMod p)
    (hi : C1S10_test1 r p s x) :
    C1S10_assignment a p r m s ha hp29 hp4 hrp hm1 x = C1T19 := by
  have hn0 : ¬ C1S10_test0 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  simp only [C1S10_assignment, if_neg hn0, if_pos hi]

theorem C1S10_assignment_on_run2 (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : a = 1 ∨ a = 3) (hp29 : 29 ≤ p) (hp4 : ¬ p ∣ 4)
    (hrp : r ≤ 5 * p) (hm1 : 10 * m ≤ r + 5)
    (hleft : 2 * r ≤ 5 * p)
    (hright : 9 * p ≤ 4 * r) (x : ZMod p)
    (hi : C1S10_test2 r p s x) :
    C1S10_assignment a p r m s ha hp29 hp4 hrp hm1 x = C1T14 := by
  have hn0 : ¬ C1S10_test0 r p s x := fun hj => C1S10_disjoint0_2 r p s x hleft hright ⟨hj, hi⟩
  have hn1 : ¬ C1S10_test1 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  simp only [C1S10_assignment, if_neg hn0, if_neg hn1, if_pos hi]

theorem C1S10_assignment_on_run3 (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : a = 1 ∨ a = 3) (hp29 : 29 ≤ p) (hp4 : ¬ p ∣ 4)
    (hrp : r ≤ 5 * p) (hm1 : 10 * m ≤ r + 5)
    (hleft : 2 * r ≤ 5 * p)
    (hright : 9 * p ≤ 4 * r) (x : ZMod p)
    (hi : C1S10_test3 r p s x) :
    C1S10_assignment a p r m s ha hp29 hp4 hrp hm1 x = C1T14 := by
  have hn0 : ¬ C1S10_test0 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  have hn1 : ¬ C1S10_test1 r p s x := fun hj => C1S10_disjoint1_3 r p s x hleft hright ⟨hj, hi⟩
  have hn2 : ¬ C1S10_test2 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  simp only [C1S10_assignment, if_neg hn0, if_neg hn1, if_neg hn2, if_pos hi]

theorem C1S10_assignment_on_run4 (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : a = 1 ∨ a = 3) (hp29 : 29 ≤ p) (hp4 : ¬ p ∣ 4)
    (hrp : r ≤ 5 * p) (hm1 : 10 * m ≤ r + 5)
    (hleft : 2 * r ≤ 5 * p)
    (hright : 9 * p ≤ 4 * r) (x : ZMod p)
    (hi : C1S10_test4 r p s x) :
    C1S10_assignment a p r m s ha hp29 hp4 hrp hm1 x = C1T17 := by
  have hn0 : ¬ C1S10_test0 r p s x := fun hj => C1S10_disjoint0_4 r p s x hleft hright ⟨hj, hi⟩
  have hn1 : ¬ C1S10_test1 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  have hn2 : ¬ C1S10_test2 r p s x := fun hj => C1S10_disjoint2_4 r p s x hleft hright ⟨hj, hi⟩
  have hn3 : ¬ C1S10_test3 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  simp only [C1S10_assignment, if_neg hn0, if_neg hn1, if_neg hn2, if_neg hn3, if_pos hi]

theorem C1S10_assignment_on_run5 (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : a = 1 ∨ a = 3) (hp29 : 29 ≤ p) (hp4 : ¬ p ∣ 4)
    (hrp : r ≤ 5 * p) (hm1 : 10 * m ≤ r + 5)
    (hleft : 2 * r ≤ 5 * p)
    (hright : 9 * p ≤ 4 * r) (x : ZMod p)
    (hi : C1S10_test5 r p s x) :
    C1S10_assignment a p r m s ha hp29 hp4 hrp hm1 x = C1T18 := by
  have hn0 : ¬ C1S10_test0 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  have hn1 : ¬ C1S10_test1 r p s x := fun hj => C1S10_disjoint1_5 r p s x hleft hright ⟨hj, hi⟩
  have hn2 : ¬ C1S10_test2 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  have hn3 : ¬ C1S10_test3 r p s x := fun hj => C1S10_disjoint3_5 r p s x hleft hright ⟨hj, hi⟩
  have hn4 : ¬ C1S10_test4 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  simp only [C1S10_assignment, if_neg hn0, if_neg hn1, if_neg hn2, if_neg hn3, if_neg hn4, if_pos hi]

theorem C1S10_assignment_on_run6 (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : a = 1 ∨ a = 3) (hp29 : 29 ≤ p) (hp4 : ¬ p ∣ 4)
    (hrp : r ≤ 5 * p) (hm1 : 10 * m ≤ r + 5)
    (hleft : 2 * r ≤ 5 * p)
    (hright : 9 * p ≤ 4 * r) (x : ZMod p)
    (hi : C1S10_test6 r p s x) :
    C1S10_assignment a p r m s ha hp29 hp4 hrp hm1 x = C1T20 := by
  have hn0 : ¬ C1S10_test0 r p s x := fun hj => C1S10_disjoint0_6 r p s x hleft hright ⟨hj, hi⟩
  have hn1 : ¬ C1S10_test1 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  have hn2 : ¬ C1S10_test2 r p s x := fun hj => C1S10_disjoint2_6 r p s x hleft hright ⟨hj, hi⟩
  have hn3 : ¬ C1S10_test3 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  have hn4 : ¬ C1S10_test4 r p s x := fun hj => C1S10_disjoint4_6 r p s x hleft hright ⟨hj, hi⟩
  have hn5 : ¬ C1S10_test5 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  simp only [C1S10_assignment, if_neg hn0, if_neg hn1, if_neg hn2, if_neg hn3, if_neg hn4, if_neg hn5, if_pos hi]

theorem C1S10_assignment_on_run7 (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : a = 1 ∨ a = 3) (hp29 : 29 ≤ p) (hp4 : ¬ p ∣ 4)
    (hrp : r ≤ 5 * p) (hm1 : 10 * m ≤ r + 5)
    (hleft : 2 * r ≤ 5 * p)
    (hright : 9 * p ≤ 4 * r) (x : ZMod p)
    (hi : C1S10_test7 r p s x) :
    C1S10_assignment a p r m s ha hp29 hp4 hrp hm1 x = C1T20 := by
  have hn0 : ¬ C1S10_test0 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  have hn1 : ¬ C1S10_test1 r p s x := fun hj => C1S10_disjoint1_7 r p s x hleft hright ⟨hj, hi⟩
  have hn2 : ¬ C1S10_test2 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  have hn3 : ¬ C1S10_test3 r p s x := fun hj => C1S10_disjoint3_7 r p s x hleft hright ⟨hj, hi⟩
  have hn4 : ¬ C1S10_test4 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  have hn5 : ¬ C1S10_test5 r p s x := fun hj => C1S10_disjoint5_7 r p s x hleft hright ⟨hj, hi⟩
  have hn6 : ¬ C1S10_test6 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  simp only [C1S10_assignment, if_neg hn0, if_neg hn1, if_neg hn2, if_neg hn3, if_neg hn4, if_neg hn5, if_neg hn6, if_pos hi]

#print axioms C1S10_assignment_valid
#print axioms C1S10_assignment_on_run0

#print axioms C1S10_run0
end CatalanCore.Uniform.Bank.Lambda.RankFibre
