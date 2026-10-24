module

public import CatalanFrames.HybGen.TropM
public import CatalanCore.Arith.Hybrid.Pieces

@[expose] public section

/-! # Uniform class sums with table and window data

The modulus, residue class, prefix endpoint, prefix coefficient, additive
rounding slack, table, weight and admissibility predicate are all inputs.
No border ratio or instance-specific table endpoint is fixed here.
-/

open Finset Filter CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid

namespace CatalanFrames.HybGen

/-- A table family may have arbitrary admissibility and additive prefix slack.
Only eventual covers are required, so instance-specific size guards stay outside
this shared summation theorem. -/
theorem class_sum_of_family {M : ℕ} [NeZero M] {c : ZMod M}
    (hc : IsUnit c) (Adm : ℕ → ℕ → Prop) (w : ℕ → ℕ → ℕ → ℝ)
    (A s C : ℝ) (hA : 0 ≤ A) (hs : 0 < s)
    (ll : List Piece) (hl : Chain s ll)
    (hprefix : ∀ᶠ r : ℕ in atTop, ∀ m, Adm r m →
      ∀ p, p ≤ ⌊s * r⌋₊ → p.Prime → (p : ZMod M) = c →
        w r m p ≤ A * r + C)
    (hcover : ∀ᶠ r : ℕ in atTop, ∀ m, Adm r m →
      ∀ P ∈ ll, Covers c (w r m) r P)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ m, Adm r m →
      clsSum M c (w r m) 0 ⌊lastEnd s ll * r⌋₊ ≤
        (r : ℝ)^2 * ((A * s + listInt ll) / (M.totient : ℝ) + ε) := by
  let η : ℝ := ε / (2 * (s + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  have hs1 : s + 1 ≠ 0 := ne_of_gt (by linarith)
  have hηeq : η * (s + 1) = ε / 2 := by
    dsimp [η]
    field_simp [hs1]
    <;> ring
  have hηs : η * s ≤ ε / 2 := by nlinarith
  have hφ : (1 : ℝ) ≤ (M.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne M))
  have hsum := class_total hc (α0 := A + η) (t1 := s)
    (by positivity) hs ll hl (ε := ε / 2) (by positivity)
  filter_upwards [hsum, hprefix, hcover,
    eventually_ge_atTop ⌈max C 0 / η⌉₊] with r hr hpr hcr hsize
  intro m hm
  have hratio : max C 0 / η ≤ (r : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hsize)
  have hC : C ≤ η * (r : ℝ) := by
    have hh := (div_le_iff₀ hη).mp hratio
    nlinarith [le_max_left C 0]
  have hh := hr (w r m) (fun p hp hpp hpc =>
    (hpr m hm p hp hpp hpc).trans (by nlinarith)) (hcr m hm)
  refine hh.trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _))
  have heq : ((A + η) * s + listInt ll) / (M.totient : ℝ) =
      (A * s + listInt ll) / (M.totient : ℝ) + η * s / (M.totient : ℝ) := by ring
  have herr : η * s / (M.totient : ℝ) ≤ ε / 2 :=
    (div_le_self (mul_nonneg hη.le hs.le) hφ).trans hηs
  rw [heq]
  linarith

/-- The universal tropical prefix bound for an arbitrary real border window. -/
lemma WGm_le_affine_window {Fr : Frame} (I : HybInst Fr)
    (r m p : ℕ) (α a : ℝ) (hm : (m : ℝ) ≤ α * r + a) :
    WGm I r m p ≤ (2 + 2 * α) * r + 2 * a := by
  have ht := trop_D1 (lev := I.lev) p r m
  have hn : XGm I r m p ≤ 2 * (r + m) := by
    change tropVal (HW I.lev p r m) ≤ _
    exact_mod_cast ht
  have hr : (XGm I r m p : ℝ) ≤ ((2 * (r + m) : ℕ) : ℝ) := by
    exact_mod_cast hn
  dsimp [WGm]
  push_cast at hr
  nlinarith

/-- Specialize the family theorem to a tropical weight and any admissibility
predicate whose border size has a uniform affine upper bound. -/
theorem class_sum_of_affine_window {Fr : Frame} {M : ℕ} [NeZero M]
    {c : ZMod M} (hc : IsUnit c) (I : HybInst Fr)
    (Adm : ℕ → ℕ → Prop) (α a s : ℝ) (hα : 0 ≤ α) (hs : 0 < s)
    (hwindow : ∀ r m, Adm r m → (m : ℝ) ≤ α * r + a)
    (ll : List Piece) (hl : Chain s ll)
    (hcover : ∀ᶠ r : ℕ in atTop, ∀ m, Adm r m →
      ∀ P ∈ ll, Covers c (WGm I r m) r P)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ m, Adm r m →
      clsSum M c (WGm I r m) 0 ⌊lastEnd s ll * r⌋₊ ≤
        (r : ℝ)^2 * (((2 + 2 * α) * s + listInt ll) / (M.totient : ℝ) + ε) := by
  exact class_sum_of_family hc Adm (WGm I) (2 + 2 * α) s (2 * a)
    (by positivity) hs ll hl (Filter.Eventually.of_forall (fun r m hm p _ _ _ =>
      WGm_le_affine_window I r m p α a (hwindow r m hm))) hcover hε

#print axioms class_sum_of_family
#print axioms class_sum_of_affine_window

end CatalanFrames.HybGen
