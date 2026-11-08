module

public import CatalanCore.Uniform.Decay.Breakpoint.Cell
public import CatalanCore.Uniform.Decay.Breakpoint.TruncLog
public import CatalanCore.Uniform.Decay.Nodes.EnergyCheck

@[expose] public section
set_option Elab.async false

/-!
# The truncated-logarithm breakpoint cell rule (ledger B05a; sevenths avoidance, 7 Nov 2026)

Sibling of `Breakpoint.Cell` (which is not changed).  The logarithmic part `Bi(s) log s` of the
expansion about the breakpoint `p` is bounded below, on `0 < s ≤ S`, by the polynomial
`Bi(s) (λ - T_K(s/S))` (degree `n - 1 + K`) minus the constant
`ε ∑ |b_m| S^m + ∑_{b_m > 0} b_m S^m ρ(m,K)` (`TL.term_lower`), `|log S - λ| ≤ ε = 10⁻¹¹` being
checked in the kernel by the series enclosures `logLoQ`, `logHiQ` of `Nodes.EnergyCheck`.
The current rule bounds `∑ b_m s^m log s` by `∑ |b_m| S^m |log S|`, a loss of about `0.7 e_S` per unit of
`∑ |b_m| S^m`; here the cell polynomial is taken to degree `n - 1 + K` and Bernstein runs on it.

* `polyMul` (list product) with `hev_polyMul`; `truncLog K S` with `hev_truncLog`;
* `bpLineT`, `bpOkT`: the cell Boolean (`K` is the order of the truncation), and `bpOkT_sound`, which has the
  statement of `bpOk_sound`, so a cover can use it in place of `bpOk` (`CellKind.bp n side lo C Fs K`
  read with this rule, `PolyWire3.KindsT`).
-/

namespace CatalanCore.Uniform.Decay.Breakpoint

open Finset CatalanCore.Uniform.Decay.Tools CatalanCore.Uniform.Decay.Spline
  CatalanCore.Uniform.Decay.Cells CatalanCore.Uniform.Decay.NearCells
  CatalanCore.Uniform.Decay.NearFast CatalanCore.Uniform.Decay.Nodes
open CatalanCore.Uniform.Decay.Breakpoint.TL (TK rhoMK)

/-! ### Lists of rationals as polynomials -/

/-- Value of the polynomial with coefficient list `l` (Horner). -/
def hev : List ℚ → ℝ → ℝ
  | [], _ => 0
  | c :: l, s => (c : ℝ) + s * hev l s

theorem hev_addL (a b : List ℚ) (s : ℝ) : hev (addL a b) s = hev a s + hev b s := by
  induction a generalizing b with
  | nil => simp [addL, hev]
  | cons x xs ih =>
    cases b with
    | nil => simp [addL, hev]
    | cons y ys =>
      simp only [addL, hev, ih]
      push_cast; ring

theorem hev_scaleL (q : ℚ) (c : List ℚ) (s : ℝ) : hev (scaleL q c) s = (q : ℝ) * hev c s := by
  induction c with
  | nil => simp [scaleL, hev]
  | cons x xs ih =>
    simp only [scaleL, List.map_cons, hev] at ih ⊢
    rw [ih]; push_cast; ring

/-- Product of coefficient lists. -/
def polyMul : List ℚ → List ℚ → List ℚ
  | [], _ => []
  | a :: as, b => addL (scaleL a b) (0 :: polyMul as b)

theorem hev_polyMul (a b : List ℚ) (s : ℝ) : hev (polyMul a b) s = hev a s * hev b s := by
  induction a with
  | nil => simp [polyMul, hev]
  | cons x xs ih =>
    simp only [polyMul, hev_addL, hev_scaleL, hev, ih]
    push_cast; ring

/-- A list of length `≤ n` evaluates as the sum of `n` terms. -/
theorem hev_eq_sum : ∀ (l : List ℚ) (n : ℕ), l.length ≤ n → ∀ s : ℝ,
    hev l s = ∑ m ∈ range n, ((coeffs l m : ℚ) : ℝ) * s ^ m
  | [], n, _, s => by simp [hev, coeffs]
  | c :: l, n, h, s => by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by simp at h; omega⟩
    rw [Finset.sum_range_succ']
    have ih := hev_eq_sum l k (by simpa using h) s
    simp only [hev]
    have e : ∀ m ∈ range k, ((coeffs (c :: l) (m + 1) : ℚ) : ℝ) * s ^ (m + 1)
        = s * (((coeffs l m : ℚ) : ℝ) * s ^ m) := by
      intro m _
      simp [coeffs]; ring
    rw [Finset.sum_congr rfl e, ← Finset.mul_sum, ← ih]
    simp [coeffs]
    ring

/-! ### The truncated logarithm as a list -/

/-- `∑_{i<r} (1 - s/S)^(k+i+1) / (k+i+1)` added to `acc`, where `pw` is the list of `(1 - s/S)^k`. -/
def tlGo (S : ℚ) : ℕ → ℕ → List ℚ → List ℚ → List ℚ
  | 0, _, _, acc => acc
  | r + 1, k, pw, acc =>
    let pw' := polyMul pw [1, -1 / S]
    tlGo S r (k + 1) pw' (addL acc (scaleL (1 / ((k + 1 : ℕ) : ℚ)) pw'))

/-- `T_K(s/S) = ∑_{k=1}^K (1 - s/S)^k / k` as a coefficient list in `s`. -/
def truncLog (K : ℕ) (S : ℚ) : List ℚ := tlGo S K 0 [1] []

theorem hev_tlGo {S : ℚ} (hS : S ≠ 0) (s : ℝ) : ∀ (r k : ℕ) (pw acc : List ℚ),
    hev pw s = (1 - s / (S : ℝ)) ^ k →
    hev (tlGo S r k pw acc) s = hev acc s +
      ∑ i ∈ range r, (1 - s / (S : ℝ)) ^ (k + i + 1) / ((k : ℝ) + i + 1)
  | 0, k, pw, acc, _ => by simp [tlGo]
  | r + 1, k, pw, acc, h => by
    have hS' : (S : ℝ) ≠ 0 := by exact_mod_cast hS
    have h1 : hev (polyMul pw [1, -1 / S]) s = (1 - s / (S : ℝ)) ^ (k + 1) := by
      rw [hev_polyMul, h]
      simp only [hev]
      push_cast
      rw [pow_succ]
      field_simp
      ring
    have ih := hev_tlGo hS s r (k + 1) (polyMul pw [1, -1 / S])
      (addL acc (scaleL (1 / ((k + 1 : ℕ) : ℚ)) (polyMul pw [1, -1 / S]))) h1
    simp only [tlGo]
    rw [ih, hev_addL, hev_scaleL, h1, Finset.sum_range_succ']
    have e : ∀ i ∈ range r, (1 - s / (S : ℝ)) ^ (k + 1 + i + 1) / (((k + 1 : ℕ) : ℝ) + i + 1)
        = (1 - s / (S : ℝ)) ^ (k + (i + 1) + 1) / ((k : ℝ) + ((i + 1 : ℕ) : ℝ) + 1) := by
      intro i _
      rw [show k + 1 + i + 1 = k + (i + 1) + 1 by ring]
      congr 1
      push_cast; ring
    rw [Finset.sum_congr rfl e]
    push_cast
    ring

theorem hev_truncLog {S : ℚ} (hS : S ≠ 0) (K : ℕ) (s : ℝ) :
    hev (truncLog K S) s = TK K (s / (S : ℝ)) := by
  have := hev_tlGo hS s K 0 [1] [] (by simp [hev])
  unfold truncLog
  rw [this]
  simp only [hev, zero_add, TL.TK]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

/-! ### The logarithm check -/

/-- Number of terms of the series enclosures of `log S`. -/
def logN : ℕ := 16

/-- The accepted error of the stored `λ`. -/
def logEps : ℚ := 1 / 10 ^ 11

/-- `|log S - λ| ≤ 10⁻¹¹` from the series enclosures. -/
def logOk (lam S : ℚ) : Bool :=
  decide (lam - logEps ≤ logLoQ logN S) && decide (logHiQ logN S ≤ lam + logEps)

theorem logOk_sound {lam S : ℚ} (hS : 0 < S) (h : logOk lam S = true) :
    |Real.log (S : ℝ) - lam| ≤ (logEps : ℝ) := by
  unfold logOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  have a1 := logLoQ_le hS logN
  have a2 := le_logHiQ hS logN
  have b1 : ((lam - logEps : ℚ) : ℝ) ≤ (logLoQ logN S : ℝ) := by exact_mod_cast h1
  have b2 : (logHiQ logN S : ℝ) ≤ ((lam + logEps : ℚ) : ℝ) := by exact_mod_cast h2
  push_cast at b1 b2
  rw [abs_le]
  constructor <;> linarith

/-! ### The cell rule -/

theorem rhoMK_nonneg (m K : ℕ) : 0 ≤ rhoMK m K := by
  unfold TL.rhoMK
  split_ifs
  · positivity
  · positivity

/-- The stored `λ`: read off the first non-zero coefficient `mi` of `Bi` from `C = C0 + Bi (λ - T)`. -/
def lamOf (C C0 Bi T : List ℚ) : Option ℕ → ℚ
  | some mi => (coeffs C mi - coeffs C0 mi) / coeffs Bi mi + coeffs T 0
  | none => 0

/-- Truncated-logarithm expansion part of the breakpoint rule (cf. `bpLine`).  `C` is the model about
`p` in degree `n - 1 + K`: `Cf + Ci + Bi (λ - T_K)`, with `λ` read off the first non-zero coefficient of
`Bi` (it is then checked: `|log S - λ| ≤ 10⁻¹¹`). -/
def bpLineT (n K : ℕ) (ps : List WP) (p d' : CQ) (S cpi lo : ℚ) (C : List ℚ) (Fs : ℚ) : Bool :=
  match aggEvalMF n p d' S (bpFar p ps), incAgg n d' S (bpInc p ps) with
  | some (Cf, Ff), some (Ci, Bi, Fi) =>
    let C0 := addL Cf Ci
    let T := truncLog K S
    let mi? := (List.range n).find? (fun m => decide (coeffs Bi m ≠ 0))
    let lam : ℚ := lamOf C C0 Bi T mi?
    let BT := polyMul Bi (addL [lam] (scaleL (-1) T))
    let bs := lsum (fun m => |coeffs Bi m| * S ^ m) n
    let logb := lsum (fun m => if 0 < coeffs Bi m then coeffs Bi m * S ^ m * rhoMK m K else 0) n
      + bs * logEps
    decide (0 < S) && decide (S ≤ 1 / 3) && decide (2 ≤ n) && decide (addL C0 BT = C) &&
      decide (coeffs Bi 0 = 0) && decide (Bi.length ≤ n) && decide (C0.length ≤ n) &&
      decide (BT.length ≤ n + K) && decide (Ff + Fi + logb ≤ Fs) && (mi?.isNone || logOk lam S) &&
      bernLoOk2 (coeffs (cellPoly C cpi p d')) (n - 1 + K) 0 S lo
  | _, _ => false

theorem bpLineT_sound {n K : ℕ} {ps : List WP} {p d' : CQ} {S cpi lo : ℚ} {C : List ℚ} {Fs : ℚ}
    (hc : bpLineT n K ps p d' S cpi lo C Fs = true) (s : ℝ) (hs0 : 0 ≤ s) (hs : s ≤ (S : ℝ)) :
    (lo : ℝ) - Fs ≤ -(ps.map (fun P => (P.w : ℝ) * PhiW P (p.toC + (s : ℂ) * d'.toC))).sum
      + (cpi : ℝ) * ((p.im : ℝ) + s * (d'.im : ℝ)) := by
  unfold bpLineT at hc
  split at hc
  · rename_i Cf Ff Ci Bi Fi hag hinc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hS0, hS3⟩, hn2⟩, hCeq⟩, hB0⟩, hBl⟩, hC0l⟩, hBTl⟩, hFs⟩, hlg⟩, hbern⟩ := hc
    have hbern := bernLoOk2_imp hbern
    set C0 := addL Cf Ci with hC0
    set mi? := (List.range n).find? (fun m => decide (coeffs Bi m ≠ 0)) with hmi
    set lam : ℚ := lamOf C C0 Bi (truncLog K S) mi? with hlam
    set BT := polyMul Bi (addL [lam] (scaleL (-1) (truncLog K S))) with hBT
    have hSR : (0 : ℝ) < S := by exact_mod_cast hS0
    have hSne : S ≠ 0 := hS0.ne'
    have habs : |s| ≤ (S : ℝ) := by rw [abs_of_nonneg hs0]; exact hs
    have hagg := aggEvalMF_sound (zc := p) (dd := d') (h := S) s habs (bpFar p ps) hag
    have hincs := incAgg_sound (n := n) (dd := d') (h := S) (pc := p.toC) s hs0 hs (bpInc p ps)
      (bpInc_A p ps) hinc
    rw [bp_sum p ps]
    -- the Bernstein bound on the cell polynomial of degree n - 1 + K
    have hnK : n - 1 + K + 1 = n + K := by omega
    have hB : (lo : ℝ) ≤ ∑ m ∈ range (n + K), ((coeffs (cellPoly C cpi p d') m : ℚ) : ℝ) * s ^ m := by
      have := bernLoOk_sound_real (a := coeffs (cellPoly C cpi p d')) (d := n - 1 + K) (u := 0)
        (w := S) hS0 hbern (x := s) (by push_cast; exact hs0) (by push_cast; linarith)
      unfold peval at this
      rw [hnK] at this
      exact this
    have hsplit : ∑ m ∈ range (n + K), ((coeffs (cellPoly C cpi p d') m : ℚ) : ℝ) * s ^ m
        = ∑ m ∈ range (n + K), ((coeffs C m : ℚ) : ℝ) * s ^ m
          + (cpi : ℝ) * ((p.im : ℝ) + s * d'.im) := by
      have h1 : ∀ m ∈ range (n + K), ((coeffs (cellPoly C cpi p d') m : ℚ) : ℝ) * s ^ m
          = ((coeffs C m : ℚ) : ℝ) * s ^ m
            + ((coeffs [cpi * p.im, cpi * d'.im] m : ℚ) : ℝ) * s ^ m := by
        intro m _
        unfold cellPoly
        rw [coeffs_addL]; push_cast; ring
      rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib]
      congr 1
      obtain ⟨k, hk⟩ : ∃ k, n + K = k + 2 := ⟨n + K - 2, by omega⟩
      rw [hk, Finset.sum_range_succ', Finset.sum_range_succ']
      have h3 : ∀ m ∈ range k,
          ((coeffs [cpi * p.im, cpi * d'.im] (m + 1 + 1) : ℚ) : ℝ) * s ^ (m + 1 + 1) = 0 := by
        intro m _; simp [coeffs]
      rw [Finset.sum_eq_zero h3]
      simp [coeffs]; ring
    -- C = C0 + BT, summed over n + K terms
    have hcoef : ∀ m, ((coeffs C m : ℚ) : ℝ) = ((coeffs C0 m : ℚ) : ℝ) + ((coeffs BT m : ℚ) : ℝ) := by
      intro m
      rw [← hCeq, coeffs_addL]; push_cast; ring
    have hBTe := hev_eq_sum BT (n + K) hBTl s
    have hC0e := hev_eq_sum C0 (n + K) (by omega) s
    have hC0n := hev_eq_sum C0 n hC0l s
    have hCsum : ∑ m ∈ range (n + K), ((coeffs C m : ℚ) : ℝ) * s ^ m
        = (∑ m ∈ range n, ((coeffs Cf m : ℚ) : ℝ) * s ^ m
          + ∑ m ∈ range n, ((coeffs Ci m : ℚ) : ℝ) * s ^ m) + hev BT s := by
      have h1 : ∑ m ∈ range n, ((coeffs Cf m : ℚ) : ℝ) * s ^ m
          + ∑ m ∈ range n, ((coeffs Ci m : ℚ) : ℝ) * s ^ m = hev C0 s := by
        rw [hC0n, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [hC0, coeffs_addL]; push_cast; ring
      rw [h1, hC0e, hBTe, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [hcoef m]; ring
    -- the logarithmic terms
    have hBp : hev Bi s = ∑ m ∈ range n, ((coeffs Bi m : ℚ) : ℝ) * s ^ m := hev_eq_sum Bi n hBl s
    have hBTv : hev BT s
        = (∑ m ∈ range n, ((coeffs Bi m : ℚ) : ℝ) * s ^ m) * ((lam : ℝ) - TK K (s / S)) := by
      rw [hBT, hev_polyMul, hev_addL, hev_scaleL, hev_truncLog hSne, hBp]
      simp only [hev]
      push_cast; ring
    have hlogε : ∀ m ∈ range n, ((coeffs Bi m : ℚ) : ℝ) ≠ 0 →
        |Real.log (S : ℝ) - lam| ≤ (logEps : ℝ) := by
      intro m hm hne
      by_cases hnone : mi?.isNone = true
      · have hnn : mi? = none := Option.isNone_iff_eq_none.1 hnone
        have hall := List.find?_eq_none.1 (hmi.symm.trans hnn)
        have := hall m hm
        simp at this
        exact absurd (by exact_mod_cast this) hne
      · have hl : logOk lam S = true := by
          rcases Bool.or_eq_true_iff.1 hlg with h | h
          · exact absurd h hnone
          · exact h
        exact logOk_sound hS0 hl
    have hε0 : (0 : ℝ) ≤ (logEps : ℝ) := by unfold logEps; norm_num
    have hterm : ∀ m ∈ range n,
        ((coeffs Bi m : ℚ) : ℝ) * s ^ m * ((lam : ℝ) - TK K (s / S))
          - |((coeffs Bi m : ℚ) : ℝ)| * (S : ℝ) ^ m * (logEps : ℝ)
          - (if 0 < coeffs Bi m then ((coeffs Bi m * S ^ m * rhoMK m K : ℚ) : ℝ) else 0)
        ≤ ((coeffs Bi m : ℚ) : ℝ) * s ^ m * Real.log s := by
      intro m hm
      by_cases hm0 : m = 0
      · subst hm0
        simp [hB0]
      · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.2 hm0
        rcases hs0.eq_or_lt with h0 | hpos
        · -- s = 0
          rw [← h0]
          have hrho : (0 : ℝ) ≤ (rhoMK m K : ℝ) := by exact_mod_cast rhoMK_nonneg m K
          simp only [zero_pow hm0, mul_zero, zero_mul, Real.log_zero]
          have h1 : 0 ≤ |((coeffs Bi m : ℚ) : ℝ)| * (S : ℝ) ^ m * (logEps : ℝ) := by positivity
          have h2 : (0 : ℝ) ≤ (if 0 < coeffs Bi m then ((coeffs Bi m * S ^ m * rhoMK m K : ℚ) : ℝ) else 0) := by
            split_ifs with hp
            · have : (0 : ℚ) ≤ coeffs Bi m * S ^ m * rhoMK m K :=
                mul_nonneg (mul_nonneg hp.le (pow_nonneg hS0.le _)) (rhoMK_nonneg m K)
              exact_mod_cast this
            · exact le_refl _
          linarith
        · have key := TL.term_lower (b := ((coeffs Bi m : ℚ) : ℝ)) (lam := (lam : ℝ)) (ε := (logEps : ℝ))
            (S := (S : ℝ)) (s := s) hm1 K hpos hs (fun hne => hlogε m hm hne)
          have e : max ((coeffs Bi m : ℚ) : ℝ) 0 * (S : ℝ) ^ m * (rhoMK m K : ℝ)
              = (if 0 < coeffs Bi m then ((coeffs Bi m * S ^ m * rhoMK m K : ℚ) : ℝ) else 0) := by
            split_ifs with hp
            · have hp' : (0 : ℝ) < ((coeffs Bi m : ℚ) : ℝ) := by exact_mod_cast hp
              rw [max_eq_left hp'.le]; push_cast; ring
            · have hp' : ((coeffs Bi m : ℚ) : ℝ) ≤ 0 := by exact_mod_cast not_lt.1 hp
              rw [max_eq_right hp']; ring
          rw [e] at key
          exact key
    have hsumT := Finset.sum_le_sum hterm
    simp only [Finset.sum_sub_distrib] at hsumT
    have hlogb : (∑ m ∈ range n, ((coeffs Bi m : ℚ) : ℝ) * s ^ m * ((lam : ℝ) - TK K (s / S)))
        - (∑ m ∈ range n, |((coeffs Bi m : ℚ) : ℝ)| * (S : ℝ) ^ m * (logEps : ℝ))
        - (∑ m ∈ range n, (if 0 < coeffs Bi m then ((coeffs Bi m * S ^ m * rhoMK m K : ℚ) : ℝ) else 0))
        ≤ Real.log s * ∑ m ∈ range n, ((coeffs Bi m : ℚ) : ℝ) * s ^ m := by
      have e : Real.log s * ∑ m ∈ range n, ((coeffs Bi m : ℚ) : ℝ) * s ^ m
          = ∑ m ∈ range n, ((coeffs Bi m : ℚ) : ℝ) * s ^ m * Real.log s := by
        rw [mul_comm, Finset.sum_mul]
      rw [e]; exact hsumT
    have hpoly : (∑ m ∈ range n, ((coeffs Bi m : ℚ) : ℝ) * s ^ m * ((lam : ℝ) - TK K (s / S)))
        = (∑ m ∈ range n, ((coeffs Bi m : ℚ) : ℝ) * s ^ m) * ((lam : ℝ) - TK K (s / S)) := by
      rw [Finset.sum_mul]
    have hs1 : ((lsum (fun m => if 0 < coeffs Bi m then coeffs Bi m * S ^ m * rhoMK m K else 0) n : ℚ) : ℝ)
        = ∑ m ∈ range n, (if 0 < coeffs Bi m then ((coeffs Bi m * S ^ m * rhoMK m K : ℚ) : ℝ) else 0) := by
      rw [lsum_eq, Rat.cast_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      split_ifs <;> simp
    have hs2 : ((lsum (fun m => |coeffs Bi m| * S ^ m) n * logEps : ℚ) : ℝ)
        = ∑ m ∈ range n, |((coeffs Bi m : ℚ) : ℝ)| * (S : ℝ) ^ m * (logEps : ℝ) := by
      rw [lsum_eq, Rat.cast_mul, Rat.cast_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun m _ => ?_
      push_cast; ring
    have hconst : (∑ m ∈ range n, |((coeffs Bi m : ℚ) : ℝ)| * (S : ℝ) ^ m * (logEps : ℝ))
        + (∑ m ∈ range n, (if 0 < coeffs Bi m then ((coeffs Bi m * S ^ m * rhoMK m K : ℚ) : ℝ) else 0))
        = ((lsum (fun m => if 0 < coeffs Bi m then coeffs Bi m * S ^ m * rhoMK m K else 0) n
            + lsum (fun m => |coeffs Bi m| * S ^ m) n * logEps : ℚ) : ℝ) := by
      rw [Rat.cast_add, hs1, hs2]; ring
    have hFsR : (Ff : ℝ) + Fi + ((lsum (fun m => if 0 < coeffs Bi m then coeffs Bi m * S ^ m * rhoMK m K else 0) n
            + lsum (fun m => |coeffs Bi m| * S ^ m) n * logEps : ℚ) : ℝ) ≤ Fs := by
      exact_mod_cast hFs
    rw [abs_le] at hagg hincs
    rw [hsplit, hCsum, hBTv] at hB
    nlinarith [hagg.1, hagg.2, hincs.1, hincs.2, hFsR, hlogb, hpoly, hconst, hB]
  · cases hc

/-- The breakpoint cell rule with the truncated logarithm: `K` is the truncation order (the field `eS` of the
shared cell kind `CellKind.bp`). -/
def bpOkT (n : ℕ) (side : Bool) (ps : List WP) (zc dd : CQ) (h W Rtwo cpi lo m' : ℚ) (C : List ℚ)
    (Fs : ℚ) (eW eP K : ℕ) : Bool :=
  bpLineT n K ps (bpPoint side zc dd h) (bpDir side dd) (2 * h) cpi lo C Fs &&
    decide (0 < h) && decide (0 < W) && decide (0 ≤ cpi) && decide (0 ≤ zc.im - h * |dd.im|) &&
    modAll Rtwo W eW eP ps && decide (m' ≤ lo - Fs - modSum Rtwo W eW eP ps)

theorem bpLineT_cell {n K : ℕ} {side : Bool} {ps : List WP} {zc dd : CQ} {h cpi lo : ℚ} {C : List ℚ}
    {Fs : ℚ}
    (hc : bpLineT n K ps (bpPoint side zc dd h) (bpDir side dd) (2 * h) cpi lo C Fs = true)
    (s : ℝ) (hs : |s| ≤ h) :
    (lo : ℝ) - Fs ≤ -(ps.map (fun P => (P.w : ℝ) * PhiW P (zc.toC + (s : ℂ) * dd.toC))).sum
      + (cpi : ℝ) * ((zc.im : ℝ) + s * (dd.im : ℝ)) := by
  have hs' := abs_le.1 hs
  cases side
  · have := bpLineT_sound hc (s + h) (by linarith [hs'.1]) (by push_cast; linarith [hs'.2])
    have hz : (bpPoint false zc dd h).toC + ((s + h : ℝ) : ℂ) * (bpDir false dd).toC
        = zc.toC + (s : ℂ) * dd.toC := by
      simp only [bpPoint, bpDir, Bool.false_eq_true, ↓reduceIte, CQ.toC_sub, CQ.toC_smul]
      push_cast; ring
    have hi : ((bpPoint false zc dd h).im : ℝ) + (s + h) * ((bpDir false dd).im : ℝ)
        = (zc.im : ℝ) + s * (dd.im : ℝ) := by
      simp only [bpPoint, bpDir, Bool.false_eq_true, ↓reduceIte, CQ.sub, CQ.smul]
      push_cast; ring
    rw [hz, hi] at this
    exact this
  · have := bpLineT_sound hc (h - s) (by linarith [hs'.2]) (by push_cast; linarith [hs'.1])
    have hz : (bpPoint true zc dd h).toC + ((h - s : ℝ) : ℂ) * (bpDir true dd).toC
        = zc.toC + (s : ℂ) * dd.toC := by
      simp only [bpPoint, bpDir, ↓reduceIte, CQ.toC_add, CQ.toC_neg, CQ.toC_smul]
      push_cast; ring
    have hi : ((bpPoint true zc dd h).im : ℝ) + (h - s) * ((bpDir true dd).im : ℝ)
        = (zc.im : ℝ) + s * (dd.im : ℝ) := by
      simp only [bpPoint, bpDir, ↓reduceIte, CQ.add, CQ.smul, CQ.neg]
      push_cast; ring
    rw [hz, hi] at this
    exact this

/-- **The truncated-logarithm breakpoint cell rule** (statement of `bpOk_sound`). -/
theorem bpOkT_sound {n : ℕ} {side : Bool} {ps : List WP} {zc dd : CQ}
    {h W Rtwo cpi lo m' : ℚ} {C : List ℚ} {Fs : ℚ} {eW eP K : ℕ}
    (hc : bpOkT n side ps zc dd h W Rtwo cpi lo m' C Fs eW eP K = true) (s δ : ℝ) (hs : |s| ≤ h)
    (hδ : |δ| ≤ W) :
    (m' : ℝ) ≤ -(ps.map (fun P => (P.w : ℝ) * PhiW P (zc.toC + (s : ℂ) * dd.toC + (δ : ℂ)))).sum
      + (cpi : ℝ) * |(zc.toC + (s : ℂ) * dd.toC + (δ : ℂ)).im| := by
  unfold bpOkT at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨hline, hh⟩, hW⟩, hcpi⟩, hy0⟩, hmod⟩, hfin⟩ := hc
  have hWR : (0 : ℝ) < W := by exact_mod_cast hW
  have hl := bpLineT_cell hline s hs
  have hz : ‖(zc.toC + (s : ℂ) * dd.toC) - (zc.toC + (s : ℂ) * dd.toC + (δ : ℂ))‖ ≤ (W : ℝ) := by
    have : (zc.toC + (s : ℂ) * dd.toC) - (zc.toC + (s : ℂ) * dd.toC + (δ : ℂ)) = -(δ : ℂ) := by ring
    rw [this, norm_neg, Complex.norm_real, Real.norm_eq_abs]; exact hδ
  have hms := modAll_sum hWR ps hmod hz
  have him : (zc.toC + (s : ℂ) * dd.toC + (δ : ℂ)).im = (zc.im : ℝ) + s * (dd.im : ℝ) := by
    simp [CQ.toC]
  have hy : 0 ≤ (zc.im : ℝ) + s * dd.im := by
    have h1 : |s * (dd.im : ℝ)| ≤ h * |(dd.im : ℝ)| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right hs (abs_nonneg _)
    have h2 := (abs_le.1 h1).1
    have h0 : (0 : ℝ) ≤ (zc.im : ℝ) - h * |(dd.im : ℝ)| := by exact_mod_cast hy0
    linarith
  rw [him, abs_of_nonneg hy]
  have hfinR : (m' : ℝ) ≤ lo - Fs - modSum Rtwo W eW eP ps := by exact_mod_cast hfin
  rw [abs_le] at hms
  nlinarith [hms.1, hms.2, hl, hfinR]

end CatalanCore.Uniform.Decay.Breakpoint
