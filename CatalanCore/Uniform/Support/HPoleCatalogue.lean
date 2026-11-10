module

public import CatalanCore.Uniform.Support.Producer

@[expose] public section
set_option Elab.async false

/-! # All-order assignment bounds and their catalogue producer (Q17)

The four arithmetic row theorems are reused from `Support.Producer` without
alteration. This module supplies their generic catalogue interface. Every pole
order, coefficient sequence, hybrid geometry and retained common subset remains
a parameter. The numerical bank catalogues are instances, not theory producers.
-/
namespace CatalanCore.Uniform.Support
open CatalanCore CatalanCore.Basic CatalanCore.Uniform
open CatalanCore.Arith.Hybrid CatalanCore.Uniform.Content.Shape
open CatalanCore.Uniform.Content.BankShared CatalanCore.Uniform.Content.BankShared.Check
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.Member
open CatalanCore.Uniform.Content.SmallPrimes Finset Polynomial
open CatalanCore.Uniform.Content.Wire

namespace IntegerPoleRows

/-- Q1–Q4 together, on every retained common subset and at every hybrid geometry.
The arithmetic statement is valid already for `h ≥ 2`, and therefore covers the
paper's `h ≥ 3` frames without a nonzero-top-coefficient restriction. -/
theorem assignment_bounds (h : ℕ) (hh : 2 ≤ h) (d : ℕ → ℚ)
    {p : ℕ} [Fact p.Prime]
    (hd : ∀ j ∈ Icc 1 (h - 1), d j ∈ LocRing p)
    {G : BlockGeom} {r : ℕ} (hs : HybShape G r) (S : Finset (G.geometry r).C)
    (hN : r + 2 * (G.geometry r).k < p * p) (hodd : p % 2 = 1) :
    GLE p (h * (r + (G.geometry r).k) - delta (G.geometry r).k p)
      (SeqFamily.poly (hpoleF h d) (hpoleE h d) G.geometry ⟨r, S⟩) ∧
    (p ≤ r → GLE p (2 * h * (r + (G.geometry r).k - p))
      (SeqFamily.poly (hpoleF h d) (hpoleE h d) G.geometry ⟨r, S⟩)) ∧
    ((p ≤ r) → (r ≤ 2 * p) → (2 * (G.geometry r).k ≤ p) →
      (2 * p ≤ r + 2 * (G.geometry r).k) → (r + 2 * (G.geometry r).k ≤ 3 * p) →
      GLE p ((2 * h - 1) * r + 2 * (h - 1) * (G.geometry r).k - 2 * (h - 1) * p)
        (SeqFamily.poly (hpoleF h d) (hpoleE h d) G.geometry ⟨r, S⟩)) ∧
    (r ≤ p → GLE p (h * (r + 2 * (G.geometry r).k - p))
      (SeqFamily.poly (hpoleF h d) (hpoleE h d) G.geometry ⟨r, S⟩)) := by
  exact ⟨family_first h hh d hd hs S hN hodd,
    (fun hpr => family_second h hh d hd hs S hN hpr),
    (fun hpr hrp hmp hlo hhi => family_third h hh d hd hs S hN hpr hrp hmp hlo hhi),
    (fun hpr => family_fourth h hh d hd hs S hN hpr)⟩

def firstBranch (h : ℕ) : KBranch :=
  ⟨.tsub (.smul h (.add .vr .vm)) (.dist .vm), [], 0⟩

def secondBranch (h : ℕ) : KBranch :=
  ⟨.smul (2 * h) (.tsub (.add .vr .vm) .vp), [⟨1,-1,0,[],0,false⟩], 0⟩

/-- The third branch is extended below `2p` using Q2, exactly as in the existing
numeric bank. Under the paper's lower guard it is Q3 itself. -/
def thirdBranch (h : ℕ) : KBranch :=
  ⟨.tsub (.add (.smul (2 * h - 1) .vr) (.smul (2 * (h - 1)) .vm))
    (.smul (2 * (h - 1)) .vp),
    [⟨1,-1,0,[],0,false⟩, ⟨-1,2,0,[],0,false⟩,
     ⟨0,1,-2,[],0,false⟩, ⟨-1,3,-2,[],0,false⟩], 0⟩

def fourthBranch (h : ℕ) : KBranch :=
  ⟨.smul h (.tsub (.add .vr (.smul 2 .vm)) .vp), [⟨-1,1,0,[],0,false⟩], 0⟩

def zeroBranch : KBranch := ⟨.cst 0, [⟨-1,1,-2,[],0,false⟩], 0⟩

def catalogue (h : ℕ) : List KBranch :=
  [firstBranch h, secondBranch h, thirdBranch h, fourthBranch h, zeroBranch]

private theorem second_le_third_below (h : ℕ) (hh : 2 ≤ h) (r m p : ℕ)
    (hpr : p ≤ r) (hlo : r + 2 * m ≤ 2 * p) :
    2 * h * (r + m - p) ≤
      (2 * h - 1) * r + 2 * (h - 1) * m - 2 * (h - 1) * p := by
  have hh1 : h - 1 + 1 = h := by omega
  have hh2 : 2 * h - 1 + 1 = 2 * h := by omega
  have hrr := congrArg (fun x : ℕ => x * r) hh2
  have hmm := congrArg (fun x : ℕ => x * m) hh1
  have hpp := congrArg (fun x : ℕ => x * p) hh1
  have ha := congrArg (fun x : ℕ => 2 * h * x)
    (Nat.sub_add_cancel (show p ≤ r + m by omega))
  have hb : 2 * (h - 1) * p ≤ (2 * h - 1) * r + 2 * (h - 1) * m := by
    have hmul := Nat.mul_le_mul_left (2 * (h - 1)) hpr
    nlinarith
  have hc := Nat.sub_add_cancel hb
  nlinarith only [hrr, hmm, hpp, ha, hc, hlo]

end IntegerPoleRows

/-- The generic all-order assignment catalogue producer. The shift list and its
master denominator are arbitrary because the assignment rows use only the actual
hybrid geometry. The coefficient supplier states exactly which primes are valid. -/
theorem hpole_catalogue (h : ℕ) (hh : 2 ≤ h) (d : ℕ → ℚ)
    (c : ℚ) (hc : 0 < c) (const : ℝ) (depth : ℕ)
    (shifts : List Shift) (Q0 Pbad N0 : ℕ) (hQ : 1 ≤ Q0) (hbad : 2 ≤ Pbad)
    (hcoeff : ∀ (p : ℕ) [Fact p.Prime], N0 < p →
      ∀ j ∈ Icc 1 (h - 1), d j ∈ LocRing p) :
    KCatValidFam c hc const depth
      (SeqFamily.poly (hpoleF h d) (hpoleE h d) (altGeom c hc).geometry)
      shifts Q0 Pbad N0 (IntegerPoleRows.catalogue h) := by
  intro br hbr i hi hr p _ hpb hpn hN kv hkv hcond
  have hd := hcoeff p hpn
  have hs := altGeom_hybShape c hc hi.2
  have hbase := Nat.mul_le_mul_right (i.1 + 2 * (altGeom c hc).borderSize i.1) hQ
  simp only [Nat.one_mul] at hbase
  have hwin : i.1 + 2 * ((altGeom c hc).geometry i.1).k < p * p := by
    rw [geometry_k_eq_borderSize]
    exact lt_of_le_of_lt hbase hN
  have hodd : p % 2 = 1 := by
    rcases (Fact.out : p.Prime).eq_two_or_odd with hp | hp
    · omega
    · exact hp
  have bounds := IntegerPoleRows.assignment_bounds h hh d hd hs i.2 hwin hodd
  simp only [IntegerPoleRows.catalogue, List.mem_cons, List.not_mem_nil, or_false] at hbr
  rcases hbr with rfl | rfl | rfl | rfl | rfl
  · refine ⟨_, bounds.1, ?_⟩
    simp [IntegerPoleRows.firstBranch, KExpr.evalN, IntegerPoleRows.delta, geometry_k_eq_borderSize]
  · have hpr : p ≤ i.1 := by
      have ht := hcond ⟨1,-1,0,[],0,false⟩ (by simp [IntegerPoleRows.secondBranch])
      norm_num [KCond.Holds, KCond.L, dot] at ht
      omega
    refine ⟨_, bounds.2.1 hpr, ?_⟩
    simp [IntegerPoleRows.secondBranch, KExpr.evalN, geometry_k_eq_borderSize]
  · have hpr : p ≤ i.1 := by
      have ht := hcond ⟨1,-1,0,[],0,false⟩ (by simp [IntegerPoleRows.thirdBranch])
      norm_num [KCond.Holds, KCond.L, dot] at ht
      omega
    have hrp : i.1 ≤ 2 * p := by
      have ht := hcond ⟨-1,2,0,[],0,false⟩ (by simp [IntegerPoleRows.thirdBranch])
      norm_num [KCond.Holds, KCond.L, dot] at ht
      omega
    have hmp : 2 * ((altGeom c hc).geometry i.1).k ≤ p := by
      have ht := hcond ⟨0,1,-2,[],0,false⟩ (by simp [IntegerPoleRows.thirdBranch])
      norm_num [KCond.Holds, KCond.L, dot] at ht
      rw [geometry_k_eq_borderSize]
      omega
    have hhi : i.1 + 2 * ((altGeom c hc).geometry i.1).k ≤ 3 * p := by
      have ht := hcond ⟨-1,3,-2,[],0,false⟩ (by simp [IntegerPoleRows.thirdBranch])
      norm_num [KCond.Holds, KCond.L, dot] at ht
      rw [geometry_k_eq_borderSize]
      omega
    by_cases hlo : 2 * p ≤ i.1 + 2 * ((altGeom c hc).geometry i.1).k
    · refine ⟨_, bounds.2.2.1 hpr hrp hmp hlo hhi, ?_⟩
      simp [IntegerPoleRows.thirdBranch, KExpr.evalN, geometry_k_eq_borderSize]
    · refine ⟨_, bounds.2.1 hpr, ?_⟩
      simp only [IntegerPoleRows.thirdBranch, KExpr.evalN, Nat.zero_mul, add_zero]
      simp only [geometry_k_eq_borderSize] at hlo ⊢
      exact IntegerPoleRows.second_le_third_below h hh _ _ _ hpr (by omega)
  · have hpr : i.1 ≤ p := by
      have ht := hcond ⟨-1,1,0,[],0,false⟩ (by simp [IntegerPoleRows.fourthBranch])
      norm_num [KCond.Holds, KCond.L, dot] at ht
      omega
    refine ⟨_, bounds.2.2.2 hpr, ?_⟩
    simp [IntegerPoleRows.fourthBranch, KExpr.evalN, geometry_k_eq_borderSize]
  · have hnp : i.1 + 2 * ((altGeom c hc).geometry i.1).k ≤ p := by
      have ht := hcond ⟨-1,1,-2,[],0,false⟩ (by simp [IntegerPoleRows.zeroBranch])
      norm_num [KCond.Holds, KCond.L, dot] at ht
      rw [geometry_k_eq_borderSize]
      omega
    have hrow := bounds.2.2.2 (show i.1 ≤ p by omega)
    refine ⟨0, ?_, ?_⟩
    · rw [Nat.sub_eq_zero_of_le hnp, Nat.mul_zero] at hrow
      exact hrow
    · simp [IntegerPoleRows.zeroBranch, KExpr.evalN]

end CatalanCore.Uniform.Support

#print axioms CatalanCore.Uniform.Support.IntegerPoleRows.assignment_bounds
#print axioms CatalanCore.Uniform.Support.hpole_catalogue
