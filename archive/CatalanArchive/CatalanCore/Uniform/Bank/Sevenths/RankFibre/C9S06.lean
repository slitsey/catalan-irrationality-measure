import CatalanCore.Uniform.Bank.Sevenths.CommonMinorRealize
import CatalanCore.Uniform.Content.RankProducer.Boundary
import CatalanCore.Uniform.Bank.Sevenths.Band
import CatalanCore.Uniform.Bank.Sevenths.RankSource.C9S06
import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C9
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankFibre
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.RankProducer
open CatalanCore.Uniform.Content.RankProducer.Geometry RankSource RankData
open scoped Classical

theorem C9S06_run0 (a p Bnd : ℕ) [Fact p.Prime] (hp7 : ¬ p ∣ 7)
    (hc : ∀ j, (D7Frame a).c j ∈ S p) (hpq : ∀ j, ¬ p ∣ (D7Frame a).q j)
    (hp3 : 3 ≤ p) (hbd : ∀ j, (D7Frame a).q j * Bnd + (D7Frame a).u j ≤ p ^ 2)
    (r m x : ℕ) (s : Finset (Fin r)) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 0) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 12 * m ≤ r + 6) (hm2 : r ≤ 12 * m + 6) (hrp : r ≤ 6 * p)
    (hleft : 7 * r ≤ 32 * p)
    (hright : 30 * p ≤ 7 * r)
    (hlo : (1 : ℤ) * x ≥ (0 : ℤ) * r + (0 : ℤ) * p + 4)
    (hhi : (6 : ℤ) * x ≤ (7 : ℤ) * r + (-30 : ℤ) * p - 24)
    (k : ℕ) (ha : 1 ≤ a ∧ a ≤ 6) (hk : k < p) (hroot : 7 * k + a = 4 * p)
    (hgood : x ∉ deletedResidues r p s) (hden : ¬ p ∣ C9T08_den) :
    C9T08.Ok ∧ C9T08.Integral p ∧
      Realizes ((D7Frame a).poleSplit Bnd hc hpq hp3 hbd)
        (rowsOf r m s) (colsOf r m s) (x : ZMod p) C9T08 := by
  refine ⟨C9T08_ok, C9T08_integral p hden, ?_⟩
  apply realizes_commonMinor_D7Frame a p Bnd hp7 hc hpq hp3 hbd r m s k 4 x 0
    hk (by omega) hxp
    (C9S06_run0_bit r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi a k ha hroot)
    C9T08
  · exact C9S06_run0_R r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact C9S06_run0_C r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact kept_of_not_deleted r p s x hxp hgood
  · exact C9T08_palette.1
  · exact fun d hd => (C9T08_palette.2 d hd).1

theorem C9S06_run1 (a p Bnd : ℕ) [Fact p.Prime] (hp7 : ¬ p ∣ 7)
    (hc : ∀ j, (D7Frame a).c j ∈ S p) (hpq : ∀ j, ¬ p ∣ (D7Frame a).q j)
    (hp3 : 3 ≤ p) (hbd : ∀ j, (D7Frame a).q j * Bnd + (D7Frame a).u j ≤ p ^ 2)
    (r m x : ℕ) (s : Finset (Fin r)) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 1) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 12 * m ≤ r + 6) (hm2 : r ≤ 12 * m + 6) (hrp : r ≤ 6 * p)
    (hleft : 7 * r ≤ 32 * p)
    (hright : 30 * p ≤ 7 * r)
    (hlo : (1 : ℤ) * x ≥ (0 : ℤ) * r + (0 : ℤ) * p + 4)
    (hhi : (6 : ℤ) * x ≤ (7 : ℤ) * r + (-30 : ℤ) * p - 24)
    (k : ℕ) (ha : 1 ≤ a ∧ a ≤ 6) (hk : k < p) (hroot : 7 * k + a = 4 * p)
    (hgood : x ∉ deletedResidues r p s) (hden : ¬ p ∣ C9T09_den) :
    C9T09.Ok ∧ C9T09.Integral p ∧
      Realizes ((D7Frame a).poleSplit Bnd hc hpq hp3 hbd)
        (rowsOf r m s) (colsOf r m s) (x : ZMod p) C9T09 := by
  refine ⟨C9T09_ok, C9T09_integral p hden, ?_⟩
  apply realizes_commonMinor_D7Frame a p Bnd hp7 hc hpq hp3 hbd r m s k 4 x 0
    hk (by omega) hxp
    (C9S06_run1_bit r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi a k ha hroot)
    C9T09
  · exact C9S06_run1_R r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact C9S06_run1_C r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact kept_of_not_deleted r p s x hxp hgood
  · exact C9T09_palette.1
  · exact fun d hd => (C9T09_palette.2 d hd).1

theorem C9S06_run2 (a p Bnd : ℕ) [Fact p.Prime] (hp7 : ¬ p ∣ 7)
    (hc : ∀ j, (D7Frame a).c j ∈ S p) (hpq : ∀ j, ¬ p ∣ (D7Frame a).q j)
    (hp3 : 3 ≤ p) (hbd : ∀ j, (D7Frame a).q j * Bnd + (D7Frame a).u j ≤ p ^ 2)
    (r m x : ℕ) (s : Finset (Fin r)) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 0) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 12 * m ≤ r + 6) (hm2 : r ≤ 12 * m + 6) (hrp : r ≤ 6 * p)
    (hleft : 7 * r ≤ 32 * p)
    (hright : 30 * p ≤ 7 * r)
    (hlo : (6 : ℤ) * x ≥ (7 : ℤ) * r + (-30 : ℤ) * p + 24)
    (hhi : (1 : ℤ) * x ≤ (1 : ℤ) * r + (-4 : ℤ) * p - 4)
    (k : ℕ) (ha : 1 ≤ a ∧ a ≤ 6) (hk : k < p) (hroot : 7 * k + a = 4 * p)
    (hgood : x ∉ deletedResidues r p s) (hden : ¬ p ∣ C9T13_den) :
    C9T13.Ok ∧ C9T13.Integral p ∧
      Realizes ((D7Frame a).poleSplit Bnd hc hpq hp3 hbd)
        (rowsOf r m s) (colsOf r m s) (x : ZMod p) C9T13 := by
  refine ⟨C9T13_ok, C9T13_integral p hden, ?_⟩
  apply realizes_commonMinor_D7Frame a p Bnd hp7 hc hpq hp3 hbd r m s k 4 x 0
    hk (by omega) hxp
    (C9S06_run2_bit r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi a k ha hroot)
    C9T13
  · exact C9S06_run2_R r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact C9S06_run2_C r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact kept_of_not_deleted r p s x hxp hgood
  · exact C9T13_palette.1
  · exact fun d hd => (C9T13_palette.2 d hd).1

theorem C9S06_run3 (a p Bnd : ℕ) [Fact p.Prime] (hp7 : ¬ p ∣ 7)
    (hc : ∀ j, (D7Frame a).c j ∈ S p) (hpq : ∀ j, ¬ p ∣ (D7Frame a).q j)
    (hp3 : 3 ≤ p) (hbd : ∀ j, (D7Frame a).q j * Bnd + (D7Frame a).u j ≤ p ^ 2)
    (r m x : ℕ) (s : Finset (Fin r)) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 1) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 12 * m ≤ r + 6) (hm2 : r ≤ 12 * m + 6) (hrp : r ≤ 6 * p)
    (hleft : 7 * r ≤ 32 * p)
    (hright : 30 * p ≤ 7 * r)
    (hlo : (6 : ℤ) * x ≥ (7 : ℤ) * r + (-30 : ℤ) * p + 24)
    (hhi : (1 : ℤ) * x ≤ (1 : ℤ) * r + (-4 : ℤ) * p - 4)
    (k : ℕ) (ha : 1 ≤ a ∧ a ≤ 6) (hk : k < p) (hroot : 7 * k + a = 4 * p)
    (hgood : x ∉ deletedResidues r p s) (hden : ¬ p ∣ C9T13_den) :
    C9T13.Ok ∧ C9T13.Integral p ∧
      Realizes ((D7Frame a).poleSplit Bnd hc hpq hp3 hbd)
        (rowsOf r m s) (colsOf r m s) (x : ZMod p) C9T13 := by
  refine ⟨C9T13_ok, C9T13_integral p hden, ?_⟩
  apply realizes_commonMinor_D7Frame a p Bnd hp7 hc hpq hp3 hbd r m s k 4 x 0
    hk (by omega) hxp
    (C9S06_run3_bit r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi a k ha hroot)
    C9T13
  · exact C9S06_run3_R r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact C9S06_run3_C r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact kept_of_not_deleted r p s x hxp hgood
  · exact C9T13_palette.1
  · exact fun d hd => (C9T13_palette.2 d hd).1

theorem C9S06_run4 (a p Bnd : ℕ) [Fact p.Prime] (hp7 : ¬ p ∣ 7)
    (hc : ∀ j, (D7Frame a).c j ∈ S p) (hpq : ∀ j, ¬ p ∣ (D7Frame a).q j)
    (hp3 : 3 ≤ p) (hbd : ∀ j, (D7Frame a).q j * Bnd + (D7Frame a).u j ≤ p ^ 2)
    (r m x : ℕ) (s : Finset (Fin r)) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 0) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 12 * m ≤ r + 6) (hm2 : r ≤ 12 * m + 6) (hrp : r ≤ 6 * p)
    (hleft : 7 * r ≤ 32 * p)
    (hright : 30 * p ≤ 7 * r)
    (hlo : (1 : ℤ) * x ≥ (1 : ℤ) * r + (-4 : ℤ) * p + 4)
    (hhi : (7 : ℤ) * x ≤ (0 : ℤ) * r + (4 : ℤ) * p - 28)
    (k : ℕ) (ha : 1 ≤ a ∧ a ≤ 6) (hk : k < p) (hroot : 7 * k + a = 4 * p)
    (hgood : x ∉ deletedResidues r p s) (hden : ¬ p ∣ C9T14_den) :
    C9T14.Ok ∧ C9T14.Integral p ∧
      Realizes ((D7Frame a).poleSplit Bnd hc hpq hp3 hbd)
        (rowsOf r m s) (colsOf r m s) (x : ZMod p) C9T14 := by
  refine ⟨C9T14_ok, C9T14_integral p hden, ?_⟩
  apply realizes_commonMinor_D7Frame a p Bnd hp7 hc hpq hp3 hbd r m s k 4 x 0
    hk (by omega) hxp
    (C9S06_run4_bit r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi a k ha hroot)
    C9T14
  · exact C9S06_run4_R r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact C9S06_run4_C r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact kept_of_not_deleted r p s x hxp hgood
  · exact C9T14_palette.1
  · exact fun d hd => (C9T14_palette.2 d hd).1

theorem C9S06_run5 (a p Bnd : ℕ) [Fact p.Prime] (hp7 : ¬ p ∣ 7)
    (hc : ∀ j, (D7Frame a).c j ∈ S p) (hpq : ∀ j, ¬ p ∣ (D7Frame a).q j)
    (hp3 : 3 ≤ p) (hbd : ∀ j, (D7Frame a).q j * Bnd + (D7Frame a).u j ≤ p ^ 2)
    (r m x : ℕ) (s : Finset (Fin r)) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 1) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 12 * m ≤ r + 6) (hm2 : r ≤ 12 * m + 6) (hrp : r ≤ 6 * p)
    (hleft : 7 * r ≤ 32 * p)
    (hright : 30 * p ≤ 7 * r)
    (hlo : (1 : ℤ) * x ≥ (1 : ℤ) * r + (-4 : ℤ) * p + 4)
    (hhi : (7 : ℤ) * x ≤ (0 : ℤ) * r + (4 : ℤ) * p - 28)
    (k : ℕ) (ha : 1 ≤ a ∧ a ≤ 6) (hk : k < p) (hroot : 7 * k + a = 4 * p)
    (hgood : x ∉ deletedResidues r p s) (hden : ¬ p ∣ C9T15_den) :
    C9T15.Ok ∧ C9T15.Integral p ∧
      Realizes ((D7Frame a).poleSplit Bnd hc hpq hp3 hbd)
        (rowsOf r m s) (colsOf r m s) (x : ZMod p) C9T15 := by
  refine ⟨C9T15_ok, C9T15_integral p hden, ?_⟩
  apply realizes_commonMinor_D7Frame a p Bnd hp7 hc hpq hp3 hbd r m s k 4 x 0
    hk (by omega) hxp
    (C9S06_run5_bit r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi a k ha hroot)
    C9T15
  · exact C9S06_run5_R r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact C9S06_run5_C r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact kept_of_not_deleted r p s x hxp hgood
  · exact C9T15_palette.1
  · exact fun d hd => (C9T15_palette.2 d hd).1

theorem C9S06_run6 (a p Bnd : ℕ) [Fact p.Prime] (hp7 : ¬ p ∣ 7)
    (hc : ∀ j, (D7Frame a).c j ∈ S p) (hpq : ∀ j, ¬ p ∣ (D7Frame a).q j)
    (hp3 : 3 ≤ p) (hbd : ∀ j, (D7Frame a).q j * Bnd + (D7Frame a).u j ≤ p ^ 2)
    (r m x : ℕ) (s : Finset (Fin r)) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 0) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 12 * m ≤ r + 6) (hm2 : r ≤ 12 * m + 6) (hrp : r ≤ 6 * p)
    (hleft : 7 * r ≤ 32 * p)
    (hright : 30 * p ≤ 7 * r)
    (hlo : (7 : ℤ) * x ≥ (0 : ℤ) * r + (4 : ℤ) * p + 28)
    (hhi : (1 : ℤ) * x ≤ (0 : ℤ) * r + (1 : ℤ) * p - 4)
    (k : ℕ) (ha : 1 ≤ a ∧ a ≤ 6) (hk : k < p) (hroot : 7 * k + a = 4 * p)
    (hgood : x ∉ deletedResidues r p s) (hden : ¬ p ∣ C9T11_den) :
    C9T11.Ok ∧ C9T11.Integral p ∧
      Realizes ((D7Frame a).poleSplit Bnd hc hpq hp3 hbd)
        (rowsOf r m s) (colsOf r m s) (x : ZMod p) C9T11 := by
  refine ⟨C9T11_ok, C9T11_integral p hden, ?_⟩
  apply realizes_commonMinor_D7Frame a p Bnd hp7 hc hpq hp3 hbd r m s k 4 x 1
    hk (by omega) hxp
    (C9S06_run6_bit r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi a k ha hroot)
    C9T11
  · exact C9S06_run6_R r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact C9S06_run6_C r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact kept_of_not_deleted r p s x hxp hgood
  · exact C9T11_palette.1
  · exact fun d hd => (C9T11_palette.2 d hd).1

theorem C9S06_run7 (a p Bnd : ℕ) [Fact p.Prime] (hp7 : ¬ p ∣ 7)
    (hc : ∀ j, (D7Frame a).c j ∈ S p) (hpq : ∀ j, ¬ p ∣ (D7Frame a).q j)
    (hp3 : 3 ≤ p) (hbd : ∀ j, (D7Frame a).q j * Bnd + (D7Frame a).u j ≤ p ^ 2)
    (r m x : ℕ) (s : Finset (Fin r)) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = 1) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 12 * m ≤ r + 6) (hm2 : r ≤ 12 * m + 6) (hrp : r ≤ 6 * p)
    (hleft : 7 * r ≤ 32 * p)
    (hright : 30 * p ≤ 7 * r)
    (hlo : (7 : ℤ) * x ≥ (0 : ℤ) * r + (4 : ℤ) * p + 28)
    (hhi : (1 : ℤ) * x ≤ (0 : ℤ) * r + (1 : ℤ) * p - 4)
    (k : ℕ) (ha : 1 ≤ a ∧ a ≤ 6) (hk : k < p) (hroot : 7 * k + a = 4 * p)
    (hgood : x ∉ deletedResidues r p s) (hden : ¬ p ∣ C9T12_den) :
    C9T12.Ok ∧ C9T12.Integral p ∧
      Realizes ((D7Frame a).poleSplit Bnd hc hpq hp3 hbd)
        (rowsOf r m s) (colsOf r m s) (x : ZMod p) C9T12 := by
  refine ⟨C9T12_ok, C9T12_integral p hden, ?_⟩
  apply realizes_commonMinor_D7Frame a p Bnd hp7 hc hpq hp3 hbd r m s k 4 x 1
    hk (by omega) hxp
    (C9S06_run7_bit r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi a k ha hroot)
    C9T12
  · exact C9S06_run7_R r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact C9S06_run7_C r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact kept_of_not_deleted r p s x hxp hgood
  · exact C9T12_palette.1
  · exact fun d hd => (C9T12_palette.2 d hd).1

noncomputable def C9S06_test0 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p) : Prop :=
  x.val % 2 = 0 ∧ 4 ≤ x.val ∧
    (0 : ℤ) * r + (0 : ℤ) * p + 4 ≤ (1 : ℤ) * x.val ∧
    (6 : ℤ) * x.val ≤ (7 : ℤ) * r + (-30 : ℤ) * p - 24 ∧
    x.val ∉ deletedResidues r p s
noncomputable def C9S06_test1 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p) : Prop :=
  x.val % 2 = 1 ∧ 4 ≤ x.val ∧
    (0 : ℤ) * r + (0 : ℤ) * p + 4 ≤ (1 : ℤ) * x.val ∧
    (6 : ℤ) * x.val ≤ (7 : ℤ) * r + (-30 : ℤ) * p - 24 ∧
    x.val ∉ deletedResidues r p s
noncomputable def C9S06_test2 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p) : Prop :=
  x.val % 2 = 0 ∧ 4 ≤ x.val ∧
    (7 : ℤ) * r + (-30 : ℤ) * p + 24 ≤ (6 : ℤ) * x.val ∧
    (1 : ℤ) * x.val ≤ (1 : ℤ) * r + (-4 : ℤ) * p - 4 ∧
    x.val ∉ deletedResidues r p s
noncomputable def C9S06_test3 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p) : Prop :=
  x.val % 2 = 1 ∧ 4 ≤ x.val ∧
    (7 : ℤ) * r + (-30 : ℤ) * p + 24 ≤ (6 : ℤ) * x.val ∧
    (1 : ℤ) * x.val ≤ (1 : ℤ) * r + (-4 : ℤ) * p - 4 ∧
    x.val ∉ deletedResidues r p s
noncomputable def C9S06_test4 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p) : Prop :=
  x.val % 2 = 0 ∧ 4 ≤ x.val ∧
    (1 : ℤ) * r + (-4 : ℤ) * p + 4 ≤ (1 : ℤ) * x.val ∧
    (7 : ℤ) * x.val ≤ (0 : ℤ) * r + (4 : ℤ) * p - 28 ∧
    x.val ∉ deletedResidues r p s
noncomputable def C9S06_test5 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p) : Prop :=
  x.val % 2 = 1 ∧ 4 ≤ x.val ∧
    (1 : ℤ) * r + (-4 : ℤ) * p + 4 ≤ (1 : ℤ) * x.val ∧
    (7 : ℤ) * x.val ≤ (0 : ℤ) * r + (4 : ℤ) * p - 28 ∧
    x.val ∉ deletedResidues r p s
noncomputable def C9S06_test6 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p) : Prop :=
  x.val % 2 = 0 ∧ 4 ≤ x.val ∧
    (0 : ℤ) * r + (4 : ℤ) * p + 28 ≤ (7 : ℤ) * x.val ∧
    (1 : ℤ) * x.val ≤ (0 : ℤ) * r + (1 : ℤ) * p - 4 ∧
    x.val ∉ deletedResidues r p s
noncomputable def C9S06_test7 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p) : Prop :=
  x.val % 2 = 1 ∧ 4 ≤ x.val ∧
    (0 : ℤ) * r + (4 : ℤ) * p + 28 ≤ (7 : ℤ) * x.val ∧
    (1 : ℤ) * x.val ≤ (0 : ℤ) * r + (1 : ℤ) * p - 4 ∧
    x.val ∉ deletedResidues r p s

noncomputable def C9S06_assignment (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : 1 ≤ a ∧ a ≤ 6) (hp64 : 64 ≤ p) (hp7 : ¬ p ∣ 7)
    (hrp : r ≤ 6 * p) (hm1 : 12 * m ≤ r + 6) : ZMod p → FibreCert := fun x =>
  if C9S06_test0 r p s x then C9T08 else
  if C9S06_test1 r p s x then C9T09 else
  if C9S06_test2 r p s x then C9T13 else
  if C9S06_test3 r p s x then C9T13 else
  if C9S06_test4 r p s x then C9T14 else
  if C9S06_test5 r p s x then C9T15 else
  if C9S06_test6 r p s x then C9T11 else
  if C9S06_test7 r p s x then C9T12 else
  trivCert (seventhsPoleSplit a p r m ha hp64 hp7 hrp hm1) (rowsOf r m s) (colsOf r m s) x

theorem C9S06_assignment_valid (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : 1 ≤ a ∧ a ≤ 6) (hp64 : 64 ≤ p) (hp7 : ¬ p ∣ 7)
    (hrp : r ≤ 6 * p) (hm1 : 12 * m ≤ r + 6)
    (hr : r % 2 = 0) (hp : p % 2 = 1) (hm2 : r ≤ 12 * m + 6)
    (hleft : 7 * r ≤ 32 * p)
    (hright : 30 * p ≤ 7 * r)
    (k : ℕ) (hk : k < p) (hroot : 7 * k + a = 4 * p)
    (hden : ∀ N ∈ ([C9T08_den, C9T09_den, C9T11_den, C9T12_den, C9T13_den, C9T14_den, C9T15_den] : List ℕ), ¬ p ∣ N) (x : ZMod p) :
    (C9S06_assignment a p r m s ha hp64 hp7 hrp hm1 x).Ok ∧
    (C9S06_assignment a p r m s ha hp64 hp7 hrp hm1 x).Integral p ∧
    Realizes (seventhsPoleSplit a p r m ha hp64 hp7 hrp hm1)
      (rowsOf r m s) (colsOf r m s) x
      (C9S06_assignment a p r m s ha hp64 hp7 hrp hm1 x) := by
  have hxp : x.val < p := ZMod.val_lt x
  unfold C9S06_assignment
  split_ifs with h0 h1 h2 h3 h4 h5 h6 h7
  · obtain ⟨hpar, hx, hlo, hhi, hgood⟩ := h0
    have h := C9S06_run0 a p (r + 2 * m) hp7 (D7Frame_coeff_mem a p)
      (D7Frame_den_units a p hp7) (by omega) (D7Frame_band a r m p ha hp64 hrp hm1)
      r m x.val s hr hp hpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
      k ha hk hroot hgood (hden C9T08_den (by simp))
    simpa only [seventhsPoleSplit, ZMod.natCast_zmod_val] using h
  · obtain ⟨hpar, hx, hlo, hhi, hgood⟩ := h1
    have h := C9S06_run1 a p (r + 2 * m) hp7 (D7Frame_coeff_mem a p)
      (D7Frame_den_units a p hp7) (by omega) (D7Frame_band a r m p ha hp64 hrp hm1)
      r m x.val s hr hp hpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
      k ha hk hroot hgood (hden C9T09_den (by simp))
    simpa only [seventhsPoleSplit, ZMod.natCast_zmod_val] using h
  · obtain ⟨hpar, hx, hlo, hhi, hgood⟩ := h2
    have h := C9S06_run2 a p (r + 2 * m) hp7 (D7Frame_coeff_mem a p)
      (D7Frame_den_units a p hp7) (by omega) (D7Frame_band a r m p ha hp64 hrp hm1)
      r m x.val s hr hp hpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
      k ha hk hroot hgood (hden C9T13_den (by simp))
    simpa only [seventhsPoleSplit, ZMod.natCast_zmod_val] using h
  · obtain ⟨hpar, hx, hlo, hhi, hgood⟩ := h3
    have h := C9S06_run3 a p (r + 2 * m) hp7 (D7Frame_coeff_mem a p)
      (D7Frame_den_units a p hp7) (by omega) (D7Frame_band a r m p ha hp64 hrp hm1)
      r m x.val s hr hp hpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
      k ha hk hroot hgood (hden C9T13_den (by simp))
    simpa only [seventhsPoleSplit, ZMod.natCast_zmod_val] using h
  · obtain ⟨hpar, hx, hlo, hhi, hgood⟩ := h4
    have h := C9S06_run4 a p (r + 2 * m) hp7 (D7Frame_coeff_mem a p)
      (D7Frame_den_units a p hp7) (by omega) (D7Frame_band a r m p ha hp64 hrp hm1)
      r m x.val s hr hp hpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
      k ha hk hroot hgood (hden C9T14_den (by simp))
    simpa only [seventhsPoleSplit, ZMod.natCast_zmod_val] using h
  · obtain ⟨hpar, hx, hlo, hhi, hgood⟩ := h5
    have h := C9S06_run5 a p (r + 2 * m) hp7 (D7Frame_coeff_mem a p)
      (D7Frame_den_units a p hp7) (by omega) (D7Frame_band a r m p ha hp64 hrp hm1)
      r m x.val s hr hp hpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
      k ha hk hroot hgood (hden C9T15_den (by simp))
    simpa only [seventhsPoleSplit, ZMod.natCast_zmod_val] using h
  · obtain ⟨hpar, hx, hlo, hhi, hgood⟩ := h6
    have h := C9S06_run6 a p (r + 2 * m) hp7 (D7Frame_coeff_mem a p)
      (D7Frame_den_units a p hp7) (by omega) (D7Frame_band a r m p ha hp64 hrp hm1)
      r m x.val s hr hp hpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
      k ha hk hroot hgood (hden C9T11_den (by simp))
    simpa only [seventhsPoleSplit, ZMod.natCast_zmod_val] using h
  · obtain ⟨hpar, hx, hlo, hhi, hgood⟩ := h7
    have h := C9S06_run7 a p (r + 2 * m) hp7 (D7Frame_coeff_mem a p)
      (D7Frame_den_units a p hp7) (by omega) (D7Frame_band a r m p ha hp64 hrp hm1)
      r m x.val s hr hp hpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
      k ha hk hroot hgood (hden C9T12_den (by simp))
    simpa only [seventhsPoleSplit, ZMod.natCast_zmod_val] using h
  · exact ⟨FibreCert.triv_ok _ _ _ _, FibreCert.triv_integral _ _ _ _,
      trivCert_realizes _ _ _ _⟩

private theorem C9S06_disjoint0_2 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p)
    (hleft : 7 * r ≤ 32 * p)
    (hright : 30 * p ≤ 7 * r) :
    ¬ (C9S06_test0 r p s x ∧ C9S06_test2 r p s x) := by
  rintro ⟨⟨hpar0, hx0, hlo0, hhi0, hgood0⟩, ⟨hpar1, hx1, hlo1, hhi1, hgood1⟩⟩
  omega

private theorem C9S06_disjoint0_4 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p)
    (hleft : 7 * r ≤ 32 * p)
    (hright : 30 * p ≤ 7 * r) :
    ¬ (C9S06_test0 r p s x ∧ C9S06_test4 r p s x) := by
  rintro ⟨⟨hpar0, hx0, hlo0, hhi0, hgood0⟩, ⟨hpar1, hx1, hlo1, hhi1, hgood1⟩⟩
  omega

private theorem C9S06_disjoint0_6 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p)
    (hleft : 7 * r ≤ 32 * p)
    (hright : 30 * p ≤ 7 * r) :
    ¬ (C9S06_test0 r p s x ∧ C9S06_test6 r p s x) := by
  rintro ⟨⟨hpar0, hx0, hlo0, hhi0, hgood0⟩, ⟨hpar1, hx1, hlo1, hhi1, hgood1⟩⟩
  omega

private theorem C9S06_disjoint1_3 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p)
    (hleft : 7 * r ≤ 32 * p)
    (hright : 30 * p ≤ 7 * r) :
    ¬ (C9S06_test1 r p s x ∧ C9S06_test3 r p s x) := by
  rintro ⟨⟨hpar0, hx0, hlo0, hhi0, hgood0⟩, ⟨hpar1, hx1, hlo1, hhi1, hgood1⟩⟩
  omega

private theorem C9S06_disjoint1_5 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p)
    (hleft : 7 * r ≤ 32 * p)
    (hright : 30 * p ≤ 7 * r) :
    ¬ (C9S06_test1 r p s x ∧ C9S06_test5 r p s x) := by
  rintro ⟨⟨hpar0, hx0, hlo0, hhi0, hgood0⟩, ⟨hpar1, hx1, hlo1, hhi1, hgood1⟩⟩
  omega

private theorem C9S06_disjoint1_7 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p)
    (hleft : 7 * r ≤ 32 * p)
    (hright : 30 * p ≤ 7 * r) :
    ¬ (C9S06_test1 r p s x ∧ C9S06_test7 r p s x) := by
  rintro ⟨⟨hpar0, hx0, hlo0, hhi0, hgood0⟩, ⟨hpar1, hx1, hlo1, hhi1, hgood1⟩⟩
  omega

private theorem C9S06_disjoint2_4 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p)
    (hleft : 7 * r ≤ 32 * p)
    (hright : 30 * p ≤ 7 * r) :
    ¬ (C9S06_test2 r p s x ∧ C9S06_test4 r p s x) := by
  rintro ⟨⟨hpar0, hx0, hlo0, hhi0, hgood0⟩, ⟨hpar1, hx1, hlo1, hhi1, hgood1⟩⟩
  omega

private theorem C9S06_disjoint2_6 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p)
    (hleft : 7 * r ≤ 32 * p)
    (hright : 30 * p ≤ 7 * r) :
    ¬ (C9S06_test2 r p s x ∧ C9S06_test6 r p s x) := by
  rintro ⟨⟨hpar0, hx0, hlo0, hhi0, hgood0⟩, ⟨hpar1, hx1, hlo1, hhi1, hgood1⟩⟩
  omega

private theorem C9S06_disjoint3_5 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p)
    (hleft : 7 * r ≤ 32 * p)
    (hright : 30 * p ≤ 7 * r) :
    ¬ (C9S06_test3 r p s x ∧ C9S06_test5 r p s x) := by
  rintro ⟨⟨hpar0, hx0, hlo0, hhi0, hgood0⟩, ⟨hpar1, hx1, hlo1, hhi1, hgood1⟩⟩
  omega

private theorem C9S06_disjoint3_7 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p)
    (hleft : 7 * r ≤ 32 * p)
    (hright : 30 * p ≤ 7 * r) :
    ¬ (C9S06_test3 r p s x ∧ C9S06_test7 r p s x) := by
  rintro ⟨⟨hpar0, hx0, hlo0, hhi0, hgood0⟩, ⟨hpar1, hx1, hlo1, hhi1, hgood1⟩⟩
  omega

private theorem C9S06_disjoint4_6 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p)
    (hleft : 7 * r ≤ 32 * p)
    (hright : 30 * p ≤ 7 * r) :
    ¬ (C9S06_test4 r p s x ∧ C9S06_test6 r p s x) := by
  rintro ⟨⟨hpar0, hx0, hlo0, hhi0, hgood0⟩, ⟨hpar1, hx1, hlo1, hhi1, hgood1⟩⟩
  omega

private theorem C9S06_disjoint5_7 (r p : ℕ) (s : Finset (Fin r)) (x : ZMod p)
    (hleft : 7 * r ≤ 32 * p)
    (hright : 30 * p ≤ 7 * r) :
    ¬ (C9S06_test5 r p s x ∧ C9S06_test7 r p s x) := by
  rintro ⟨⟨hpar0, hx0, hlo0, hhi0, hgood0⟩, ⟨hpar1, hx1, hlo1, hhi1, hgood1⟩⟩
  omega

theorem C9S06_assignment_on_run0 (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : 1 ≤ a ∧ a ≤ 6) (hp64 : 64 ≤ p) (hp7 : ¬ p ∣ 7)
    (hrp : r ≤ 6 * p) (hm1 : 12 * m ≤ r + 6)
    (hleft : 7 * r ≤ 32 * p)
    (hright : 30 * p ≤ 7 * r) (x : ZMod p)
    (hi : C9S06_test0 r p s x) :
    C9S06_assignment a p r m s ha hp64 hp7 hrp hm1 x = C9T08 := by
  simp only [C9S06_assignment, if_pos hi]

theorem C9S06_assignment_on_run1 (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : 1 ≤ a ∧ a ≤ 6) (hp64 : 64 ≤ p) (hp7 : ¬ p ∣ 7)
    (hrp : r ≤ 6 * p) (hm1 : 12 * m ≤ r + 6)
    (hleft : 7 * r ≤ 32 * p)
    (hright : 30 * p ≤ 7 * r) (x : ZMod p)
    (hi : C9S06_test1 r p s x) :
    C9S06_assignment a p r m s ha hp64 hp7 hrp hm1 x = C9T09 := by
  have hn0 : ¬ C9S06_test0 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  simp only [C9S06_assignment, if_neg hn0, if_pos hi]

theorem C9S06_assignment_on_run2 (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : 1 ≤ a ∧ a ≤ 6) (hp64 : 64 ≤ p) (hp7 : ¬ p ∣ 7)
    (hrp : r ≤ 6 * p) (hm1 : 12 * m ≤ r + 6)
    (hleft : 7 * r ≤ 32 * p)
    (hright : 30 * p ≤ 7 * r) (x : ZMod p)
    (hi : C9S06_test2 r p s x) :
    C9S06_assignment a p r m s ha hp64 hp7 hrp hm1 x = C9T13 := by
  have hn0 : ¬ C9S06_test0 r p s x := fun hj => C9S06_disjoint0_2 r p s x hleft hright ⟨hj, hi⟩
  have hn1 : ¬ C9S06_test1 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  simp only [C9S06_assignment, if_neg hn0, if_neg hn1, if_pos hi]

theorem C9S06_assignment_on_run3 (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : 1 ≤ a ∧ a ≤ 6) (hp64 : 64 ≤ p) (hp7 : ¬ p ∣ 7)
    (hrp : r ≤ 6 * p) (hm1 : 12 * m ≤ r + 6)
    (hleft : 7 * r ≤ 32 * p)
    (hright : 30 * p ≤ 7 * r) (x : ZMod p)
    (hi : C9S06_test3 r p s x) :
    C9S06_assignment a p r m s ha hp64 hp7 hrp hm1 x = C9T13 := by
  have hn0 : ¬ C9S06_test0 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  have hn1 : ¬ C9S06_test1 r p s x := fun hj => C9S06_disjoint1_3 r p s x hleft hright ⟨hj, hi⟩
  have hn2 : ¬ C9S06_test2 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  simp only [C9S06_assignment, if_neg hn0, if_neg hn1, if_neg hn2, if_pos hi]

theorem C9S06_assignment_on_run4 (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : 1 ≤ a ∧ a ≤ 6) (hp64 : 64 ≤ p) (hp7 : ¬ p ∣ 7)
    (hrp : r ≤ 6 * p) (hm1 : 12 * m ≤ r + 6)
    (hleft : 7 * r ≤ 32 * p)
    (hright : 30 * p ≤ 7 * r) (x : ZMod p)
    (hi : C9S06_test4 r p s x) :
    C9S06_assignment a p r m s ha hp64 hp7 hrp hm1 x = C9T14 := by
  have hn0 : ¬ C9S06_test0 r p s x := fun hj => C9S06_disjoint0_4 r p s x hleft hright ⟨hj, hi⟩
  have hn1 : ¬ C9S06_test1 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  have hn2 : ¬ C9S06_test2 r p s x := fun hj => C9S06_disjoint2_4 r p s x hleft hright ⟨hj, hi⟩
  have hn3 : ¬ C9S06_test3 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  simp only [C9S06_assignment, if_neg hn0, if_neg hn1, if_neg hn2, if_neg hn3, if_pos hi]

theorem C9S06_assignment_on_run5 (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : 1 ≤ a ∧ a ≤ 6) (hp64 : 64 ≤ p) (hp7 : ¬ p ∣ 7)
    (hrp : r ≤ 6 * p) (hm1 : 12 * m ≤ r + 6)
    (hleft : 7 * r ≤ 32 * p)
    (hright : 30 * p ≤ 7 * r) (x : ZMod p)
    (hi : C9S06_test5 r p s x) :
    C9S06_assignment a p r m s ha hp64 hp7 hrp hm1 x = C9T15 := by
  have hn0 : ¬ C9S06_test0 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  have hn1 : ¬ C9S06_test1 r p s x := fun hj => C9S06_disjoint1_5 r p s x hleft hright ⟨hj, hi⟩
  have hn2 : ¬ C9S06_test2 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  have hn3 : ¬ C9S06_test3 r p s x := fun hj => C9S06_disjoint3_5 r p s x hleft hright ⟨hj, hi⟩
  have hn4 : ¬ C9S06_test4 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  simp only [C9S06_assignment, if_neg hn0, if_neg hn1, if_neg hn2, if_neg hn3, if_neg hn4, if_pos hi]

theorem C9S06_assignment_on_run6 (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : 1 ≤ a ∧ a ≤ 6) (hp64 : 64 ≤ p) (hp7 : ¬ p ∣ 7)
    (hrp : r ≤ 6 * p) (hm1 : 12 * m ≤ r + 6)
    (hleft : 7 * r ≤ 32 * p)
    (hright : 30 * p ≤ 7 * r) (x : ZMod p)
    (hi : C9S06_test6 r p s x) :
    C9S06_assignment a p r m s ha hp64 hp7 hrp hm1 x = C9T11 := by
  have hn0 : ¬ C9S06_test0 r p s x := fun hj => C9S06_disjoint0_6 r p s x hleft hright ⟨hj, hi⟩
  have hn1 : ¬ C9S06_test1 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  have hn2 : ¬ C9S06_test2 r p s x := fun hj => C9S06_disjoint2_6 r p s x hleft hright ⟨hj, hi⟩
  have hn3 : ¬ C9S06_test3 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  have hn4 : ¬ C9S06_test4 r p s x := fun hj => C9S06_disjoint4_6 r p s x hleft hright ⟨hj, hi⟩
  have hn5 : ¬ C9S06_test5 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  simp only [C9S06_assignment, if_neg hn0, if_neg hn1, if_neg hn2, if_neg hn3, if_neg hn4, if_neg hn5, if_pos hi]

theorem C9S06_assignment_on_run7 (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : 1 ≤ a ∧ a ≤ 6) (hp64 : 64 ≤ p) (hp7 : ¬ p ∣ 7)
    (hrp : r ≤ 6 * p) (hm1 : 12 * m ≤ r + 6)
    (hleft : 7 * r ≤ 32 * p)
    (hright : 30 * p ≤ 7 * r) (x : ZMod p)
    (hi : C9S06_test7 r p s x) :
    C9S06_assignment a p r m s ha hp64 hp7 hrp hm1 x = C9T12 := by
  have hn0 : ¬ C9S06_test0 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  have hn1 : ¬ C9S06_test1 r p s x := fun hj => C9S06_disjoint1_7 r p s x hleft hright ⟨hj, hi⟩
  have hn2 : ¬ C9S06_test2 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  have hn3 : ¬ C9S06_test3 r p s x := fun hj => C9S06_disjoint3_7 r p s x hleft hright ⟨hj, hi⟩
  have hn4 : ¬ C9S06_test4 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  have hn5 : ¬ C9S06_test5 r p s x := fun hj => C9S06_disjoint5_7 r p s x hleft hright ⟨hj, hi⟩
  have hn6 : ¬ C9S06_test6 r p s x := by
    intro hj
    have h0 := hi.1
    have h1 := hj.1
    omega
  simp only [C9S06_assignment, if_neg hn0, if_neg hn1, if_neg hn2, if_neg hn3, if_neg hn4, if_neg hn5, if_neg hn6, if_pos hi]

#print axioms C9S06_assignment_valid
#print axioms C9S06_assignment_on_run0

#print axioms C9S06_run0
end CatalanCore.Uniform.Bank.Sevenths.RankFibre
