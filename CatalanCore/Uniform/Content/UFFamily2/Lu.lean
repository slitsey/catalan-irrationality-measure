module

public import CatalanCore.Uniform.Content.UFFamily.BorderDet
public import CatalanCore.Uniform.Content.UFFamily.KillOfTypes

@[expose] public section

/-!
# UF families with non-empty fibers: LU certificates attached to a named joint type (lane H, H11)

`LuData` is the per-type certificate record that a bank emits: triangular matrices for the block `M`,
for the bordered matrix of the `A`-datum and for the bordered matrix of the `B`-datum, and the claimed
values `a = fibZ T`, `b = fibZ (T.toB D)`.  `LuData.ok` is a `Bool` checked by `decide +kernel`
on `T = mkFib q o r nrm u0 J Dn` (cost `O(m³)` integer products, `UFFamily.fibZ_eq_val`), and
`crossZ_zmod_ne` turns two checked records into the `hnz` field of a `KillCert`.
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.UFMoments
  CatalanCore.Uniform.Content.UFWedge CatalanCore.Uniform.Content.Smith
  CatalanCore.Uniform.Content.UFFamily

namespace CatalanCore.Uniform.Content.UFFamily2

/-- Entry of a list-of-lists matrix (default `0`). -/
def entL (L : List (List ℤ)) (i j : ℕ) : ℤ := (L.getD i []).getD j 0

/-- The LU record of one joint type. -/
structure LuData where
  LM : List (List ℤ)
  UM : List (List ℤ)
  LA : List (List ℤ)
  UA : List (List ℤ)
  LB : List (List ℤ)
  UB : List (List ℤ)
  a : ℤ
  b : ℤ

/-- The kernel check of an LU record against the integer data `T` (scaling `D`). -/
def LuData.ok (X : LuData) (m : ℕ) (T : IntFib m) (D : ℤ) : Bool :=
  luOK m T.Mf (entL X.LM) (entL X.UM) &&
  luOK (m + 1) (borderedN T) (entL X.LA) (entL X.UA) &&
  luOK (m + 1) (borderedN (T.toB D)) (entL X.LB) (entL X.UB) &&
  decide (prodN m (fun i => entL X.UM i i) ≠ 0) &&
  decide (prodN (m + 1) (fun i => entL X.LA i i) ≠ 0) &&
  decide (prodN (m + 1) (fun i => entL X.LB i i) ≠ 0) &&
  decide (X.a * prodN (m + 1) (fun i => entL X.LA i i) = prodN (m + 1) (fun i => entL X.UA i i)) &&
  decide (X.b * prodN (m + 1) (fun i => entL X.LB i i) = prodN (m + 1) (fun i => entL X.UB i i))

theorem LuData.ok_spec {X : LuData} {m : ℕ} {T : IntFib m} {D : ℤ} (h : X.ok m T D = true) :
    fibZ m T = X.a ∧ fibZ m (T.toB D) = X.b := by
  simp only [LuData.ok, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨fibZ_eq_val T _ _ _ _ _ h1 h2 h4 h5 h7,
    fibZ_eq_val (T.toB D) _ _ _ _ _ h1 h3 h4 h6 h8⟩

/-- The cross wedge of two checked records. -/
theorem LuData.crossZ_eq {XJ XK : LuData} {mJ mK : ℕ} {J : IntFib mJ} {K : IntFib mK} {DJ DK : ℤ}
    (hJ : XJ.ok mJ J DJ = true) (hK : XK.ok mK K DK = true) :
    crossZ mJ mK DJ DK J K = XJ.b * XK.a - XJ.a * XK.b :=
  crossZ_of_vals (LuData.ok_spec hJ).1 (LuData.ok_spec hJ).2 (LuData.ok_spec hK).1
    (LuData.ok_spec hK).2

/-- **`hnz` of a `KillCert` from two checked LU records**: the prime `p` does not divide the
(`p`-independent) integer cross wedge. -/
theorem LuData.crossZ_zmod_ne {p : ℕ} [Fact p.Prime] {XJ XK : LuData} {mJ mK : ℕ} {J : IntFib mJ}
    {K : IntFib mK} {DJ DK : ℤ} (hJ : XJ.ok mJ J DJ = true) (hK : XK.ok mK K DK = true)
    (hnd : ¬ (p : ℤ) ∣ XJ.b * XK.a - XJ.a * XK.b) :
    (crossZ mJ mK DJ DK J K : ZMod p) ≠ 0 := by
  rw [LuData.crossZ_eq hJ hK]
  exact cast_ne_of_not_dvd hnd

/-- Bezout switch: if `x c₁ + y c₂ = g` and `p ∤ g`, then `p` misses one of `c₁, c₂`. -/
theorem not_dvd_or_of_bezout {p : ℕ} {c₁ c₂ x y g : ℤ} (h : x * c₁ + y * c₂ = g)
    (hg : ¬ (p : ℤ) ∣ g) : ¬ (p : ℤ) ∣ c₁ ∨ ¬ (p : ℤ) ∣ c₂ := by
  by_contra hc
  push Not at hc
  exact hg (h ▸ dvd_add (dvd_mul_of_dvd_right hc.1 x) (dvd_mul_of_dvd_right hc.2 y))

/-- A prime larger than every prime factor of a natural number does not divide it. -/
theorem not_dvd_of_factors {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0)
    (h : ∀ q ∈ n.primeFactorsList, q < p) : ¬ p ∣ n := by
  intro hd
  have := h p ((Nat.mem_primeFactorsList hn).2 ⟨hp, hd⟩)
  omega

end CatalanCore.Uniform.Content.UFFamily2
