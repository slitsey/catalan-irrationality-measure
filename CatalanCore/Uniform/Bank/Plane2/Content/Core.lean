module

public import CatalanCore.Uniform.Bank.Plane2.Content.Cat
public import CatalanCore.Uniform.Content.Sweep.RowP1
public import CatalanCore.Uniform.Content.Shape.Alt
public import CatalanCore.Uniform.Content.BankShared.Reindex
public import CatalanCore.Uniform.Content.BankShared.KTerm.Content
public import CatalanCore.Uniform.Content.BankShared.TwoTerm.Class
public import CatalanCore.Uniform.Support.Producer

@[expose] public section
set_option Elab.async false

open Polynomial Finset Matrix CatalanCore.Basic CatalanCore.Arith.Hybrid

/-!
# Plane 2 content: the shared core (lane H, wave P210; ledger P210)

* `p2G = altGeom (6/41)`, the member polynomial `p2Q v u r S` of the family of `(fS v u, eS v u)` and its
  determinant form `p2Q_eq` (the generalisation of `Zeta3Rows.zQ_eq` through `altGeom_hybShape`);
* the border facts of `p2G` at even scales (`2 m ≤ r`, `6 r ≤ 41 (2m) + 41`, `41 (2m) < 6 r + 41`);
* `Real v u b`: the branch `b` of `Content.Cat` is realised on the family (the interface of the row agents);
* `kcatValid_of_real`: `KCatValidFam` from `Real` for every branch of a list (debit `0`).
-/

namespace CatalanCore.Uniform.Bank.Plane2.Content

open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Support CatalanCore.Uniform.Content.Sweep
  CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.Wire
  CatalanCore.Uniform.Content.BankShared CatalanCore.Uniform.Content.BankShared.Check
  CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.TwoTerm

/-- The slope `c = 2 α = 6/41` is positive. -/
theorem plane2_pos : (0 : ℚ) < 6 / 41 := by norm_num

/-- The geometry of plane 2 (`= P2G` of `Bank.Plane2.Bound`). -/
noncomputable abbrev p2G : BlockGeom := altGeom (6 / 41) plane2_pos

/-- The bad-prime bound of the catalogue: `p > 6` (so `p ≥ 7`). -/
def p2Pbad : ℕ := 6
/-- `N₀`: primes above it do not divide `v` and satisfy the guard `p ≥ r/400 ⇒ p² > 2N + 2p`. -/
def p2N0 (v : ℤ) : ℕ := max 919 v.natAbs
/-- The shift list of the single pole at `1/2`: `2 k = p + 1`. -/
def p2shifts : List Shift := [⟨2, 1, 1⟩]

/-- The member polynomial of `(r, S)`. -/
noncomputable abbrev p2Q (v u : ℤ) (r : ℕ) (S : Finset (p2G.geometry r).C) : ℚ[X] :=
  SeqFamily.poly (fS v u) (eS v u) p2G.geometry ⟨r, S⟩

/-- The member is the determinant of `seqFullN (fS v u) (eS v u)` on the window nodes. -/
theorem p2Q_eq (v u : ℤ) (r : ℕ) (hr : r % 2 = 0) (S : Finset (p2G.geometry r).C) :
    p2Q v u r S = (seqFullN (fS v u) (eS v u) (fun a : S => ((a.1 : (p2G.geometry r).C) : ℕ))
      (fun i : Fin (p2G.geometry r).k => r + 2 * (i : ℕ))
      (fun i : Fin (p2G.geometry r).k => r + 2 * (i : ℕ) + 1) (X : ℚ[X])).det := by
  have hs : HybShape p2G r := altGeom_hybShape (6 / 41) plane2_pos hr
  have hx : (p2G.geometry r).xs = fun i : Fin (p2G.geometry r).k => r + 2 * (i : ℕ) := funext hs.xs_eq
  have hy : (p2G.geometry r).ys = fun i : Fin (p2G.geometry r).k => r + 2 * (i : ℕ) + 1 := funext hs.ys_eq
  unfold p2Q SeqFamily.poly
  rw [hx, hy]

theorem p2Q_inj (r : ℕ) (S : Finset (p2G.geometry r).C) :
    Function.Injective (fun a : S => ((a.1 : (p2G.geometry r).C) : ℕ)) := by
  intro a b h
  exact Subtype.ext (Subtype.ext h)

theorem p2Q_lt (r : ℕ) (hr : r % 2 = 0) (S : Finset (p2G.geometry r).C) (a : S) :
    ((a.1 : (p2G.geometry r).C) : ℕ) < r :=
  hybShape_lt_scale (altGeom_hybShape (6 / 41) plane2_pos hr) a.1

/-- The border size `m` of `p2G` at an even scale: `6 r ≤ 41 (2m) + 41` and `41 (2m) < 6 r + 41`. -/
theorem p2_border {r : ℕ} (hr : r % 2 = 0) :
    6 * r ≤ 41 * (2 * p2G.borderSize r) + 41 ∧ 41 * (2 * p2G.borderSize r) < 6 * r + 41 :=
  altGeom_border_nat (6 / 41) plane2_pos 6 41 (by norm_num) (by norm_num) hr

/-- `2 m ≤ r` for `r > 0` (the rows `P₅ .. P₇` need it). -/
theorem p2_two_m_le {r : ℕ} (hr : r % 2 = 0) (hr0 : 0 < r) : 2 * p2G.borderSize r ≤ r := by
  obtain ⟨-, h2⟩ := p2_border hr
  omega

/-- **The branch `b` is realised on the family of `(fS v u, eS v u)`.**  For every even scale `r > 0`, every member
`S`, every prime `p` above `p₂Pbad` and `N₀`, with `2 (r + 2m) < p²`, every `kv` with `2 kv₀ = p + 1`, and the
conditions of `b` holding at `(r, p, m, kv)` (`m` the border size): some exponent `n` clears `p`-adically and is at
most the price of `b`.  Debit `0`. -/
def Real (v u : ℤ) (b : KBranch) : Prop :=
  ∀ (r p : ℕ) [Fact p.Prime] (S : Finset (p2G.geometry r).C) (kv : ℕ → ℕ),
    r % 2 = 0 → 0 < r → p2Pbad < p → p2N0 v < p → 2 * (r + 2 * p2G.borderSize r) < p * p →
    2 * kv 0 = p + 1 →
    (∀ cd ∈ b.conds, cd.Holds r p (p2G.borderSize r) kv) →
    ∃ n, GLE p n (p2Q v u r S) ∧ n ≤ b.τ.evalN r p (p2G.borderSize r) kv

/-- **`KCatValidFam` from `Real`** for a list of debit-0 branches. -/
theorem kcatValid_of_real (v u : ℤ) (const : ℝ) (depth : ℕ) (cat : List KBranch)
    (hdeb : ∀ b ∈ cat, b.debit = 0) (h : ∀ b ∈ cat, Real v u b) :
    KCatValidFam (6 / 41) plane2_pos const depth (SeqFamily.poly (fS v u) (eS v u) p2G.geometry) p2shifts 2
      p2Pbad (p2N0 v) cat := by
  intro b hb i hi hr0 p _ hPb hN hqN kv hroots hcond
  obtain ⟨r, S⟩ := i
  have hr : r % 2 = 0 := hi.2
  obtain ⟨jn, hj1, hj2, hj3, -, -⟩ := hroots 0 (by simp [p2shifts])
  simp only [p2shifts, shAt] at hj1 hj3
  have hjn : jn = 1 := by omega
  subst hjn
  have hk : 2 * kv 0 = p + 1 := by omega
  obtain ⟨n, hn, hle⟩ := h b hb r p S kv hr hr0 hPb hN hqN hk hcond
  refine ⟨n, hn, ?_⟩
  rw [hdeb b hb]
  simpa using hle

/-- **Dual monotonicity in `u`** (the edge `u = 0`, ζ(3)): the cell weight of the datum `(v, u)` is at most the cell
weight of `(v, 1)`.  A dual of the `u ≠ 0` table, stated through `cell p 1`, is therefore a dual of every `u`. -/
theorem w3_cell_mono (p : ℕ) (u : ℤ) (t t' : ℕ) :
    w3 (cell p u t) (cell p u t') ≤ w3 (cell p 1 t) (cell p 1 t') := by
  by_cases hu : u = 0
  · subst hu
    unfold w3 cell half
    simp only [if_true]
    split_ifs <;> simp_all <;> omega
  · have : cell p u t = cell p 1 t := by unfold cell half; simp [hu]
    have h' : cell p u t' = cell p 1 t' := by unfold cell half; simp [hu]
    rw [this, h']

end CatalanCore.Uniform.Bank.Plane2.Content

#print axioms CatalanCore.Uniform.Bank.Plane2.Content.p2Q_eq
#print axioms CatalanCore.Uniform.Bank.Plane2.Content.w3_cell_mono
#print axioms CatalanCore.Uniform.Bank.Plane2.Content.p2_border
#print axioms CatalanCore.Uniform.Bank.Plane2.Content.kcatValid_of_real
