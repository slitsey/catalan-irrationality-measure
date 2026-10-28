module
public import CatalanCore.Uniform.Decay.Tools.Bernstein
@[expose] public section

/-!
# Kernel-friendly Bernstein checker

Structural recursion only (`lsum`, `chooseFast` via `descFactorial / factorial`), no `Finset`
and no Pascal-recursion `Nat.choose` in the computation.  Soundness is by equality with the
generic `bern` / `affCoeffs` of `Tools.Bernstein`.  Subdivision is the affine change
`affK` (exact), so any cover by subintervals is checked with `bernOkK_Icc_sound`.
(Degree elevation only sharpens the enclosure; it is not needed for soundness.)
-/

namespace CatalanCore.Uniform.Decay.Tools

open Finset

/-- Structural sum `f 0 + ... + f (n-1)`. -/
def lsum {K : Type*} [Add K] [Zero K] (f : ℕ → K) : ℕ → K
  | 0 => 0
  | n + 1 => lsum f n + f n

theorem lsum_eq {K : Type*} [AddCommMonoid K] (f : ℕ → K) (n : ℕ) :
    lsum f n = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp [lsum]
  | succ n ih => rw [lsum, ih, Finset.sum_range_succ]

/-- Binomial coefficient by `descFactorial / factorial` (linear-cost kernel evaluation). -/
def chooseFast (n k : ℕ) : ℕ := n.descFactorial k / k.factorial

theorem chooseFast_eq (n k : ℕ) : chooseFast n k = n.choose k :=
  (Nat.choose_eq_descFactorial_div_factorial n k).symm

section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Kernel-friendly Bernstein coefficient. -/
def bernK (a : ℕ → K) (d k : ℕ) : K :=
  lsum (fun i => ((chooseFast k i : ℕ) : K) / ((chooseFast d i : ℕ) : K) * a i) (k + 1)

theorem bernK_eq (a : ℕ → K) (d k : ℕ) : bernK a d k = bern a d k := by
  unfold bernK bern
  rw [lsum_eq]
  simp only [chooseFast_eq]

/-- Kernel-friendly affine coefficients of `t ↦ p (u + w t)`. -/
def affK (a : ℕ → K) (d : ℕ) (u w : K) (j : ℕ) : K :=
  w ^ j * lsum (fun l => ((chooseFast (j + l) j : ℕ) : K) * u ^ l * a (j + l)) (d + 1 - j)

theorem affK_eq (a : ℕ → K) (d : ℕ) (u w : K) : affK a d u w = affCoeffs a d u w := by
  funext j
  unfold affK affCoeffs
  rw [lsum_eq, Finset.sum_Ico_eq_sum_range]
  simp only [chooseFast_eq, Nat.add_sub_cancel_left]

/-- Coefficient function from a list. -/
def coeffs (l : List K) (i : ℕ) : K := l.getD i 0

/-- Checker on `[0,1]` from a coefficient list (degree `l.length - 1`). -/
def bernOkK (l : List K) (lo hi : K) : Bool :=
  (List.range l.length).all fun k =>
    decide (lo ≤ bernK (coeffs l) (l.length - 1) k) && decide (bernK (coeffs l) (l.length - 1) k ≤ hi)

theorem bernOkK_sound {l : List K} {lo hi : K} (hne : l ≠ []) (h : bernOkK l lo hi = true)
    {t : K} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    lo ≤ peval (coeffs l) (l.length - 1) t ∧ peval (coeffs l) (l.length - 1) t ≤ hi := by
  unfold bernOkK at h
  rw [List.all_eq_true] at h
  have hpos : 0 < l.length := List.length_pos_iff.mpr hne
  have hl : ∀ k ≤ l.length - 1, lo ≤ bern (coeffs l) (l.length - 1) k ∧
      bern (coeffs l) (l.length - 1) k ≤ hi := by
    intro k hk
    have := h k (List.mem_range.mpr (by omega))
    simp only [Bool.and_eq_true, decide_eq_true_eq, bernK_eq] at this
    exact this
  exact bernstein_range _ _ (fun k hk => (hl k hk).1) (fun k hk => (hl k hk).2) h0 h1

/-- Subinterval `[u, u+w]`: checker on the exactly substituted coefficients (kernel form). -/
def bernOkKIcc (a : ℕ → K) (d : ℕ) (u w lo hi : K) : Bool :=
  (List.range (d + 1)).all fun k =>
    decide (lo ≤ bernK (affK a d u w) d k) && decide (bernK (affK a d u w) d k ≤ hi)

theorem bernOkKIcc_sound {a : ℕ → K} {d : ℕ} {u w lo hi : K} (hw : 0 < w)
    (h : bernOkKIcc a d u w lo hi = true) {x : K} (hx0 : u ≤ x) (hx1 : x ≤ u + w) :
    lo ≤ peval a d x ∧ peval a d x ≤ hi := by
  have h' : bernOk (affCoeffs a d u w) d lo hi = true := by
    unfold bernOkKIcc at h
    unfold bernOk
    rw [List.all_eq_true] at h ⊢
    intro k hk
    have := h k hk
    rwa [bernK_eq, affK_eq] at this
  exact bernOk_Icc_sound hw h' hx0 hx1

end

end CatalanCore.Uniform.Decay.Tools
