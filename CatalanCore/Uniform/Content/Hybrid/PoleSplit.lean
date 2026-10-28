module

public import CatalanCore.Uniform.Content.Hybrid.Leading
public import CatalanCore.Basic.ZModGood
public import Mathlib.Algebra.Polynomial.Roots

@[expose] public section

/-!
# Exact pole subtraction and the residue-fiber leading matrices (frame-generic)

For a rational Loewner frame with row nodes `a i` and column nodes `b j` (naturals), prefixes
`f, e : ℕ → ℚ` and the actual matrix

  `Φ_ij = (f(b_j) - f(a_i))/(b_j - a_i)` (`a_i ≠ b_j`),  `Φ_ij = X - e(a_i)` (common node),

an exact pole split at `p` on the nodes `n ≤ B` is `f = Lf/p + F`, `e = E/p² + Gq` with `Lf, F, E, Gq` `p`-integral
and the regular prefix periodic: `F n ≡ F m (mod p)` whenever `n ≡ m (mod p)` (per pole; balance is
not needed).  Digits `t = a/p` of distinct same-residue nodes differ by a unit (`hdig`: bounded
digits on the compact band).

Then (`PoleSplit.hB`, `hCr`, `hK`, `disp`):

* `p²Φ = K + p·Cr` EXACTLY, with constant `K` zero across residue fibers,
  `K_ij = (Lf(b_j) - Lf(a_i))/(s_j - t_i)` within a fiber and `K_ij = -E(a_i)` at a common node;
* `Cr mod p` is the Loewner cross matrix `(lf(b_j) - lf(a_i))/(β_j - α_i)` of residues and reduced
  pole loads, ZERO on every same-residue pair (no within-fiber order-`p` coefficient);
* the fiber blocks satisfy the displacement identity `(t_i - s_j)·K̄_ij = lf(a_i) - lf(b_j)`.

These are exactly the inputs of `LeadingData` / `nextRed_eq_loadMat` / `omega_load_eq_zero`.
The original `X` is untouched (it enters only at order `p²`).
-/

open Polynomial CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid

namespace CatalanCore.Uniform.Content.Hybrid

variable {p : ℕ} [hp : Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual Loewner matrix of the frame on the given nodes. -/
noncomputable def loewner (a b : ι → ℕ) (f e : ℕ → ℚ) : Matrix ι ι ℚ[X] :=
  Matrix.of fun i j => if a i = b j then X - C (e (a i)) else
    C ((f (b j) - f (a i)) / ((b j : ℚ) - a i))

/-- Exact pole subtraction of the prefixes at `p`. -/
structure PoleSplit (p : ℕ) [Fact p.Prime] (B : ℕ) (f e : ℕ → ℚ) where
  Lf : ℕ → ℚ
  F : ℕ → ℚ
  E : ℕ → ℚ
  Gq : ℕ → ℚ
  lf : ℕ → ZMod p
  hf : ∀ n ≤ B, f n = Lf n / p + F n
  he : ∀ n ≤ B, e n = E n / (p : ℚ) ^ 2 + Gq n
  hLf : ∀ n ≤ B, Good p (Lf n) (lf n)
  hF : ∀ n ≤ B, F n ∈ S p
  hE : ∀ n ≤ B, E n ∈ S p
  hGq : ∀ n ≤ B, Gq n ∈ S p
  hper : ∀ n ≤ B, ∀ m ≤ B, n % p = m % p → (F n - F m) / p ∈ S p

/-- Lift of a rational into `ℤ_(p)` (junk `0` outside). -/
noncomputable def liftQ (p : ℕ) [Fact p.Prime] (x : ℚ) : LocRing p := by
  classical
  exact if h : x ∈ LocRing p then ⟨x, h⟩ else 0

lemma liftQ_val {x : ℚ} (h : x ∈ S p) : ((liftQ p x : LocRing p) : ℚ) = x := by
  have h' : x ∈ LocRing p := h
  simp [liftQ, h']

lemma redQ_liftQ {x : ℚ} {y : ZMod p} (h : Good p x y) : redQ p (liftQ p x) = y := by
  rw [redQ_apply, liftQ_val h.1]; exact h.2

/-- Digit difference `s_j - t_i`. -/
def digitDiff (p : ℕ) (a b : ι → ℕ) (i j : ι) : ℤ := ((b j / p : ℕ) : ℤ) - ((a i / p : ℕ) : ℤ)

lemma natCast_eq_of_mod {n m : ℕ} (h : (n : ZMod p) = (m : ZMod p)) : n % p = m % p :=
  (ZMod.natCast_eq_natCast_iff' n m p).1 h

lemma sub_eq_p_mul_digitDiff {a b : ι → ℕ} {i j : ι} (h : (a i : ZMod p) = (b j : ZMod p)) :
    (b j : ℚ) - a i = p * (digitDiff p a b i j : ℚ) := by
  have hm := natCast_eq_of_mod h
  have h1 := Nat.div_add_mod (a i) p
  have h2 := Nat.div_add_mod (b j) p
  have e1 : (a i : ℚ) = p * ((a i / p : ℕ) : ℚ) + ((a i % p : ℕ) : ℚ) := by exact_mod_cast h1.symm
  have e2 : (b j : ℚ) = p * ((b j / p : ℕ) : ℚ) + ((b j % p : ℕ) : ℚ) := by exact_mod_cast h2.symm
  rw [e1, e2, hm, digitDiff, Int.cast_sub, Int.cast_natCast, Int.cast_natCast]; ring

variable (a b : ι → ℕ) {B : ℕ} {f e : ℕ → ℚ}

/-- Nodes are at most `B`, and same-residue distinct nodes have digit differences prime to `p`. -/
def DigitHyp (p : ℕ) [Fact p.Prime] (B : ℕ) (a b : ι → ℕ) : Prop :=
  (∀ i, a i ≤ B) ∧ (∀ j, b j ≤ B) ∧
  ∀ i j, (a i : ZMod p) = (b j : ZMod p) → a i ≠ b j → ((digitDiff p a b i j : ℤ) : ZMod p) ≠ 0

namespace PoleSplit

variable (PS : PoleSplit p B f e)

/-- The constant leading value of `p²Φ_ij`. -/
noncomputable def Kq (i j : ι) : ℚ :=
  if a i = b j then -PS.E (a i) else
    if (a i : ZMod p) = (b j : ZMod p) then
      (PS.Lf (b j) - PS.Lf (a i)) / (digitDiff p a b i j : ℚ) else 0

/-- The rational order-`p` value of `p²Φ_ij` off the common nodes. -/
noncomputable def Crq (i j : ι) : ℚ :=
  if (a i : ZMod p) = (b j : ZMod p) then (PS.F (b j) - PS.F (a i)) / (digitDiff p a b i j : ℚ)
  else (PS.Lf (b j) - PS.Lf (a i) + p * (PS.F (b j) - PS.F (a i))) / ((b j : ℚ) - a i)

/-- The leading matrix `K` (block diagonal over residue fibers). -/
noncomputable def K : Matrix ι ι (LocRing p) := Matrix.of fun i j => liftQ p (PS.Kq a b i j)

/-- The integral order-`p` remainder `Cr`. -/
noncomputable def Cr : Matrix ι ι (LocRing p)[X] := Matrix.of fun i j =>
  if a i = b j then C (liftQ p p) * X - C (liftQ p (p * PS.Gq (a i)))
  else C (liftQ p (PS.Crq a b i j))

variable {a b}

lemma p_mem : (p : ℚ) ∈ S p := (Good.natCast (ℓ := p) p).1

lemma digit_good (hd : DigitHyp p B a b) {i j : ι} (h : (a i : ZMod p) = (b j : ZMod p))
    (hne : a i ≠ b j) :
    Good p (digitDiff p a b i j : ℚ) ((digitDiff p a b i j : ℤ) : ZMod p) ∧
      ((digitDiff p a b i j : ℤ) : ZMod p) ≠ 0 :=
  ⟨Good.intCast _, hd.2.2 i j h hne⟩

lemma diff_good {i j : ι} (h : (a i : ZMod p) ≠ (b j : ZMod p)) :
    Good p ((b j : ℚ) - a i) ((b j : ZMod p) - (a i : ZMod p)) ∧
      (b j : ZMod p) - (a i : ZMod p) ≠ 0 :=
  ⟨(Good.natCast _).sub (Good.natCast _), sub_ne_zero.2 (Ne.symm h)⟩

lemma Kq_mem (hd : DigitHyp p B a b) (i j : ι) : PS.Kq a b i j ∈ S p := by
  unfold Kq
  split_ifs with h1 h2
  · exact (S p).neg_mem (PS.hE _ (hd.1 i))
  · obtain ⟨hg, hne⟩ := digit_good hd h2 h1
    exact (((PS.hLf _ (hd.2.1 j)).sub (PS.hLf _ (hd.1 i))).div hg hne).1
  · exact (S p).zero_mem

lemma Crq_good (hd : DigitHyp p B a b) {i j : ι} (hne : a i ≠ b j) :
    Good p (PS.Crq a b i j) ((PS.lf (b j) - PS.lf (a i)) / ((b j : ZMod p) - (a i : ZMod p))) := by
  unfold Crq
  split_ifs with h
  · obtain ⟨hg, hz⟩ := digit_good hd h hne
    have hm := PS.hper (b j) (hd.2.1 j) (a i) (hd.1 i) (natCast_eq_of_mod h).symm
    have hx : (PS.F (b j) - PS.F (a i)) / (digitDiff p a b i j : ℚ) =
        (p : ℚ) * ((PS.F (b j) - PS.F (a i)) / p / (digitDiff p a b i j : ℚ)) := by
      have : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
      field_simp
    rw [hx, h, sub_self, div_zero]
    exact (((good_red hm).div hg hz)).ell_mul
  · obtain ⟨hg, hz⟩ := diff_good h
    have h0 : Good p (PS.Lf (b j) - PS.Lf (a i) + p * (PS.F (b j) - PS.F (a i)))
        (PS.lf (b j) - PS.lf (a i)) := by
      have := ((PS.hLf (b j) (hd.2.1 j)).sub (PS.hLf (a i) (hd.1 i))).add
        (good_red ((S p).sub_mem (PS.hF (b j) (hd.2.1 j)) (PS.hF (a i) (hd.1 i)))).ell_mul
      simpa using this
    exact h0.div hg hz

/-- **Exact pole split.** `p² Φ = K + p·Cr`. -/
theorem hB (hd : DigitHyp p B a b) (i j : ι) :
    toQ p (C (PS.K a b i j) + C ((p : ℕ) : LocRing p) * PS.Cr a b i j) =
      C ((p : ℚ) ^ 2) * loewner a b f e i j := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hK : ((PS.K a b i j : LocRing p) : ℚ) = PS.Kq a b i j := liftQ_val (PS.Kq_mem hd i j)
  simp only [K, Cr, loewner, Matrix.of_apply] at hK ⊢
  apply Polynomial.funext
  intro r
  by_cases h1 : a i = b j
  · simp only [if_pos h1, map_add, map_mul, map_sub, toQ, Polynomial.coe_mapRingHom,
      Polynomial.map_C, Polynomial.map_X, eval_add, eval_mul, eval_sub, eval_C, eval_X,
      Subring.coe_subtype, Subring.coe_natCast]
    rw [liftQ_val (p_mem), liftQ_val ((S p).mul_mem p_mem (PS.hGq _ (hd.1 i)))]
    rw [hK]
    simp only [Kq, if_pos h1]
    rw [PS.he _ (hd.1 i)]
    field_simp
    ring
  · simp only [if_neg h1, map_add, map_mul, toQ, Polynomial.coe_mapRingHom,
      Polynomial.map_C, eval_add, eval_mul, eval_C, Subring.coe_subtype, Subring.coe_natCast]
    rw [liftQ_val (PS.Crq_good hd h1).1, hK, PS.hf _ (hd.2.1 j), PS.hf _ (hd.1 i)]
    simp only [Kq, Crq, if_neg h1]
    by_cases h2 : (a i : ZMod p) = (b j : ZMod p)
    · simp only [if_pos h2]
      have hdd : (digitDiff p a b i j : ℚ) ≠ 0 := by
        intro h0
        apply hd.2.2 i j h2 h1
        have : digitDiff p a b i j = 0 := by exact_mod_cast h0
        rw [this, Int.cast_zero]
      rw [sub_eq_p_mul_digitDiff h2]
      field_simp
      ring
    · simp only [if_neg h2]
      have hba : (b j : ℚ) - a i ≠ 0 := by
        intro h0
        apply h2
        have : (b j : ℚ) = a i := by linarith
        have : b j = a i := by exact_mod_cast this
        rw [this]
      field_simp
      ring

/-- **No within-fiber order-`p` coefficient.** `Cr mod p` is the Loewner cross matrix of the
residues and reduced pole loads (same-residue entries vanish, as `x/0 = 0`). -/
theorem hCr (hd : DigitHyp p B a b) (i j : ι) :
    phiP p (PS.Cr a b i j) =
      rfC p ((PS.lf (b j) - PS.lf (a i)) / ((b j : ZMod p) - (a i : ZMod p))) := by
  simp only [Cr, Matrix.of_apply]
  by_cases h1 : a i = b j
  · rw [if_pos h1, map_sub, map_mul, phiP_C, phiP_C, h1]
    rw [redQ_liftQ (Good.ell (ℓ := p)), redQ_liftQ ((good_red (PS.hGq (b j) (hd.2.1 j))).ell_mul)]
    simp [rfC]
  · rw [if_neg h1, phiP_C, redQ_liftQ (PS.Crq_good hd h1)]

/-- The leading matrix vanishes across residue fibers. -/
theorem hK_cross (i j : ι) (h : (a i : ZMod p) ≠ (b j : ZMod p)) : PS.K a b i j = 0 := by
  have h1 : a i ≠ b j := fun e => h (by rw [e])
  simp only [K, Kq, Matrix.of_apply, if_neg h1, if_neg h]
  simp [liftQ]

/-- **Displacement.** Within a residue fiber, `(t_i - s_j) K̄_ij = lf(a_i) - lf(b_j)`. -/
theorem disp (hd : DigitHyp p B a b) (i j : ι) (h : (a i : ZMod p) = (b j : ZMod p)) :
    (((a i / p : ℕ) : ZMod p) - ((b j / p : ℕ) : ZMod p)) * redQ p (PS.K a b i j) =
      PS.lf (a i) - PS.lf (b j) := by
  have ht : ((a i / p : ℕ) : ZMod p) - ((b j / p : ℕ) : ZMod p) =
      -((digitDiff p a b i j : ℤ) : ZMod p) := by
    rw [digitDiff, Int.cast_sub, Int.cast_natCast, Int.cast_natCast, neg_sub]
  rw [ht]
  by_cases h1 : a i = b j
  · rw [h1]
    have : digitDiff p a b i j = 0 := by simp [digitDiff, h1]
    simp [this]
  · obtain ⟨hg, hz⟩ := digit_good hd h h1
    have hgood : Good p (PS.Kq a b i j)
        ((PS.lf (b j) - PS.lf (a i)) / ((digitDiff p a b i j : ℤ) : ZMod p)) := by
      simp only [Kq, if_neg h1, if_pos h]
      exact ((PS.hLf _ (hd.2.1 j)).sub (PS.hLf _ (hd.1 i))).div hg hz
    simp only [K, Matrix.of_apply]
    rw [redQ_liftQ hgood]
    field_simp
    ring

end PoleSplit

end CatalanCore.Uniform.Content.Hybrid
