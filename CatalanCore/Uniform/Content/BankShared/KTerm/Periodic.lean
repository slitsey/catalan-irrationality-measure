module

public import CatalanCore.Uniform.Content.BankShared.KTerm.PeriodContent

@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 1600000

/-! # Theorem PC: periodic content of a bank, generic in the price family and the period (wave P210-L)

`PERIODIC-CONTENT-2026-11-08.md`.  A bank with `α = a / b` (`b = den α`) whose profile on the periodic range is the
translate of one table of *cells*.  Lattice shift of order `n`: `(r, p, m) ↦ (r + n b p, p, m + n a p)`, which keeps `p`,
the pole indices and `m - α r`.

* `Transl b a Kc Ω kb`: a translation `ρ n` of the base catalogue `kb` with (i) the debit preserved, (ii) **price
  covariance** `τ_{ρ n B}(σ_n x) = τ_B(x) + n Kc p` (`Kc = K₀ b`, `K₀` the prefix constant), (iii) forward transport of
  the conditions (which may use the ambient range `r ≤ Ω p` of the strip).  The plain pullback `Transl.pullback` is the
  case `ρ n B = (τ_B, conds^[n])`; plane 1's prefix branches use `ρ n (PRE(n₀, j)) = PRE(n₀ + a n, j)`.
* `BaseSound`: a base cell `(s, t; A + B θ; C)` with threshold `R` is sound: validity of the base catalogue at the
  configuration `(r', p, m', k)` gives a good exponent `≤ A r' + B p + C`.  `pieceOK` gives it (`piece_sound_large`, the
  large-scale half of Theorem B).
* `trPiece`: the `n`-th translate
  `(s/(1 + n b s), t/(1 + n b t); A + (B + (Kc - A b) n) θ; C + K_crude(⌈R (1 + n b t)⌉))`.
  `trPiece_basic` is (K0); `exp_cov_per` is `PieceCov` of the translate (Claim (P)): Theorem B at the configuration
  `x' = (r - n b p, p, m - n a p, k)` with `Good'(e) := GLE p (e + n Kc p)`, branch validity by (T2) at `σ_n x'`.
* `expPer`, `KTmplP`: the expansion (strips `n = N-1, …, 0` of the table) and the class template `expansion ++ head`;
  `hasScaledContent_of_periodic` is `hasScaledContent_of_facts` for such templates. -/

namespace CatalanCore.Uniform.Content.BankShared.KTerm
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.BankShared
  CatalanCore.Uniform.Content.SmallPrimes CatalanCore.Uniform.Content.Member CatalanCore.Arith.Hybrid
  CatalanCore.Basic Filter Finset Polynomial CatalanCore.Uniform.Content.BankShared.Check

/-! ### Theorem B for large scales -/

section Large
variable {cat : List Branch} {q : ℕ} {α κ : ℚ} {depth cF Pbad : ℕ}

set_option maxHeartbeats 1000000 in
/-- **Theorem B for large scales** (`Check.piece_sound` with `cert.R ≤ r` in place of the crude exponent). -/
theorem piece_sound_large (P : QPiece) (cert : Cert) (hok : pieceOK cat q α κ depth cF Pbad P cert = true)
    (hq : 1 ≤ q) (hα : 0 ≤ α) {r p m k del : ℕ} (Good : ℕ → Prop)
    (hrd : Cond.Round q r p m k α κ) (hodd : Pbad < p → p % 2 = 1) (hpge : 2 ≤ p)
    (hdel : del ≤ depth) (hRge : cert.R ≤ (r : ℚ))
    (hbr : BranchesValid cat Pbad q r p m k del Good)
    (hs : (P.s : ℝ) * r < p) (ht : (p : ℝ) ≤ P.t * r) :
    ∃ n, Good n ∧ (n : ℝ) ≤ P.a * r + P.b * p + P.C := by
  unfold pieceOK at hok
  rcases hb : nth cat cert.bi with _ | br <;> simp only [hb, reduceCtorEq, Bool.false_eq_true] at hok
  have hbm := nth_mem cat cert.bi hb
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', List.any_eq_true] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hs0, hst⟩, ha0⟩, ha1⟩, hC0⟩, hK1⟩, hK2⟩, hR1⟩, hR2⟩, hR3⟩, hR4⟩, hL⟩, hRt⟩,
    hE⟩, hcr⟩ := hok
  simp only [crudeOK, Bool.and_eq_true, decide_eq_true_eq] at hcr
  have hp0 : 0 < p := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  have hsR : (0 : ℝ) < P.s := by exact_mod_cast hs0
  -- r > 0
  have hr0 : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · subst h0; simp at ht; linarith
    · exact h0
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr0
  have hlin0 := line_nonneg_scaled hrR hs ht ha0 ha1
  by_cases hsmall : (r : ℚ) < cert.R
  · exact absurd hsmall (not_lt.2 hRge)
  · -- large scales
    have hRr : cert.R ≤ (r : ℚ) := le_of_not_gt hsmall
    have hRr' : (cert.R : ℝ) ≤ r := by exact_mod_cast hRr
    -- frame conditions
    have hPb : Pbad < p := by
      have h1 : ((Pbad : ℚ) / P.s : ℝ) ≤ r := by
        have := (Rat.cast_le (K := ℝ)).2 hR2; push_cast at this ⊢; linarith
      have h2 : (Pbad : ℝ) ≤ P.s * r := by
        push_cast at h1; rw [div_le_iff₀ hsR] at h1; linarith
      have : (Pbad : ℝ) < p := by linarith
      exact_mod_cast this
    have hqN : q * (r + 2 * m) < p * p := by
      have h1 : ((q : ℚ) * (2 + 2 * α) / (P.s * P.s) : ℝ) ≤ r := by
        have := (Rat.cast_le (K := ℝ)).2 hR1; push_cast at this ⊢; linarith
      push_cast at h1
      rw [div_le_iff₀ (mul_pos hsR hsR)] at h1
      have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
      have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr0
      have hα' : (0 : ℝ) ≤ α := by exact_mod_cast hα
      have hm2 : (m : ℝ) < α * r + 1 / 2 := by linarith [hrd.m_hi]
      have e1 : (q : ℝ) * (r + 2 * m) < q * ((1 + 2 * α) * r + 1) :=
        mul_lt_mul_of_pos_left (by linarith) hq0
      have e2 : (q : ℝ) * ((1 + 2 * α) * r + 1) ≤ q * (2 + 2 * α) * r := by
        have := mul_le_mul_of_nonneg_left hr1 hq0.le
        linarith
      have e3 : (q : ℝ) * (2 + 2 * α) * r ≤ (P.s * r) * (P.s * r) := by
        have := mul_le_mul_of_nonneg_right h1 hrR.le
        linarith
      have hsr : (0 : ℝ) ≤ P.s * r := mul_nonneg hsR.le hrR.le
      have e4 : ((P.s : ℝ) * r) * (P.s * r) < p * p := mul_self_lt_mul_self hsr hs
      have : ((q * (r + 2 * m) : ℕ) : ℝ) < ((p * p : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    have hbv := fun b hb hc => hbr b hb hPb hqN hc
    have hp2 := hodd hPb
    -- the main branch bound, given its conditions
    have main : (∀ c ∈ br.conds, c.Holds r p m k) → ∃ n, Good n ∧ (n : ℝ) ≤ P.a * r + P.b * p + P.C := by
      intro hc
      obtain ⟨n, hn, hnb⟩ := hbv br hbm hc
      refine ⟨n, hn, ?_⟩
      have h1 := branch_bound hq hr0 hp0 hrd hdel hnb (b := br)
      have hθ1 : (P.s : ℝ) < (p : ℝ) / r := by rw [lt_div_iff₀ hrR]; exact hs
      have hθ2 : (p : ℝ) / r ≤ P.t := by rw [div_le_iff₀ hrR]; exact ht
      have h2 := k2_sound α κ P.a P.b br.τ cert.cuts P.s P.t hs0 hK2 ((p : ℝ) / r) hθ1 hθ2
      have h3 : (r : ℝ) * prof α κ ((p : ℝ) / r) br.τ ≤ P.a * r + P.b * p := by
        have := mul_le_mul_of_nonneg_left h2 hrR.le
        have e : (r : ℝ) * ((P.a : ℝ) + P.b * ((p : ℝ) / r)) = P.a * r + P.b * p := by
          field_simp
        linarith
      have h4 : ((br.τ.err (1 - 1 / (q : ℚ)) + br.debit * depth : ℚ) : ℝ) ≤ P.C := by exact_mod_cast hE
      linarith
    -- a strip branch at an end `e` with `|p - e r| ≤ V`
    have strip : ∀ (st : Strip) (e : ℚ), 0 < e → stripOK cat q α κ depth P br cert.R e st = true →
        (st.left = true → (e : ℝ) * r < p ∧ (p : ℝ) ≤ e * r + st.V) →
        (st.left = false → (e : ℝ) * r - st.V < p ∧ (p : ℝ) ≤ e * r) →
        ∃ n, Good n ∧ (n : ℝ) ≤ P.a * r + P.b * p + P.C := by
      intro st e he0 hst hLs hRs
      unfold stripOK at hst
      rcases hy : nth cat st.yi with _ | y <;> simp only [hy, reduceCtorEq, Bool.false_eq_true] at hst
      have hym := nth_mem cat st.yi hy
      rcases hl : stripLine α κ e st.left st.w y.τ with _ | l <;>
        simp only [hl, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
          reduceCtorEq, Bool.false_eq_true, and_false] at hst
      obtain ⟨⟨⟨⟨⟨hw0, hwe⟩, -⟩, hyc⟩, hVw⟩, hle, hCs⟩ := hst
      have hwR : (0 : ℝ) < st.w := by exact_mod_cast hw0
      -- |p - e r| ≤ V and V ≤ w r
      have hVwr : (st.V : ℝ) ≤ st.w * r := by
        have h1 : ((st.V / st.w : ℚ) : ℝ) ≤ r := by
          have := (Rat.cast_le (K := ℝ)).2 hVw; push_cast at this ⊢; linarith
        push_cast at h1; rw [div_le_iff₀ hwR] at h1; linarith
      have hdist : |(p : ℝ) - e * r| ≤ st.V := by
        cases hlft : st.left
        · obtain ⟨h1, h2⟩ := hRs hlft; rw [abs_le]; constructor <;> linarith
        · obtain ⟨h1, h2⟩ := hLs hlft; rw [abs_le]; constructor <;> linarith
      have hV0 : (0 : ℝ) ≤ st.V := le_trans (abs_nonneg _) hdist
      -- conditions of the strip branch
      have hcy : ∀ c ∈ y.conds, c.Holds r p m k := by
        intro c hc
        obtain ⟨⟨hpos, hR5⟩, hR6⟩ := hyc c hc
        have hpos' : (0 : ℝ) < (c.lv α κ e : ℚ) := by exact_mod_cast hpos
        have h5 : ((2 * (1 - c.etaLo q) / c.lv α κ e : ℚ) : ℝ) ≤ r := by
          have := (Rat.cast_le (K := ℝ)).2 hR5; linarith
        have h6 : ((2 * st.V * |c.ell1 κ| / c.lv α κ e : ℚ) : ℝ) ≤ r := by
          have := (Rat.cast_le (K := ℝ)).2 hR6; linarith
        push_cast at h5 h6
        rw [div_le_iff₀ hpos'] at h5 h6
        apply Cond.holds_large c hrd
        have e1 : (c.ell0 α : ℝ) * r + (c.ell1 κ : ℝ) * p =
            r * ((c.lv α κ e : ℚ) : ℝ) + (c.ell1 κ : ℝ) * ((p : ℝ) - e * r) := by rw [lv_real]; ring
        have e2 : |(c.ell1 κ : ℝ) * ((p : ℝ) - e * r)| ≤ |(c.ell1 κ : ℝ)| * st.V := by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left hdist (abs_nonneg _)
        rw [e1]
        have e3 := (abs_le.1 e2).1
        linarith
      obtain ⟨n, hn, hnb⟩ := hbv y hym hcy
      refine ⟨n, hn, ?_⟩
      have h1 := branch_bound hq hr0 hp0 hrd hdel hnb (b := y)
      -- the strip line at θ = p / r
      have hθ : prof α κ ((p : ℝ) / r) y.τ = (l.1 : ℝ) + l.2 * ((p : ℝ) / r) := by
        unfold stripLine at hl
        cases hlft : st.left <;> simp only [hlft, if_true, if_false, Bool.false_eq_true] at hl
        · obtain ⟨h1, h2⟩ := hRs hlft
          have hwe' : (st.w : ℝ) < e := by
            simp only [hlft, Bool.false_eq_true, false_or] at hwe; exact_mod_cast hwe
          have hu : (0 : ℚ) < e - st.w := by
            have : (0 : ℝ) < e - st.w := by linarith
            exact_mod_cast this
          refine affineOn_sound α κ (e - st.w) e hu y.τ l hl _ ?_ ?_
          · push_cast; rw [lt_div_iff₀ hrR]; linarith
          · rw [div_le_iff₀ hrR]; exact h2
        · obtain ⟨h1, h2⟩ := hLs hlft
          refine affineOn_sound α κ e (e + st.w) he0 y.τ l hl _ ?_ ?_
          · rw [lt_div_iff₀ hrR]; exact h1
          · push_cast; rw [div_le_iff₀ hrR]; linarith
      have hle' : (l.1 : ℝ) + l.2 * e ≤ P.a + P.b * e := by
        have := (Rat.cast_le (K := ℝ)).2 hle; unfold lval at this; push_cast at this; exact this
      have hCs' : ((y.τ.err (1 - 1 / (q : ℚ)) + y.debit * depth : ℚ) : ℝ) + (|(P.b : ℝ)| + |(l.2 : ℝ)|) * st.V ≤
          P.C := by
        have := (Rat.cast_le (K := ℝ)).2 hCs; push_cast at this ⊢; linarith
      -- r · line(p/r) ≤ a r + b p + (|b| + |l₂|) V
      have hrl : (r : ℝ) * ((l.1 : ℝ) + l.2 * ((p : ℝ) / r)) ≤ P.a * r + P.b * p + (|(P.b : ℝ)| + |(l.2 : ℝ)|) * st.V := by
        have e1 : (r : ℝ) * ((l.1 : ℝ) + l.2 * ((p : ℝ) / r)) = r * ((l.1 : ℝ) + l.2 * e) + l.2 * ((p : ℝ) - e * r) := by
          field_simp; ring
        have e2 : (P.a : ℝ) * r + P.b * p = r * ((P.a : ℝ) + P.b * e) + P.b * ((p : ℝ) - e * r) := by ring
        have e3 : |(l.2 : ℝ) * ((p : ℝ) - e * r)| ≤ |(l.2 : ℝ)| * st.V := by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left hdist (abs_nonneg _)
        have e4 : |(P.b : ℝ) * ((p : ℝ) - e * r)| ≤ |(P.b : ℝ)| * st.V := by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left hdist (abs_nonneg _)
        have e5 : (r : ℝ) * ((l.1 : ℝ) + l.2 * e) ≤ r * ((P.a : ℝ) + P.b * e) :=
          mul_le_mul_of_nonneg_left hle' hrR.le
        rw [e1, e2]
        have := (abs_le.1 e3).2
        have := (abs_le.1 e4).1
        linarith
      rw [hθ] at h1
      linarith
    -- the case analysis on the strips
    by_cases hsl : ∃ st ∈ cert.strips, st.left = true ∧ stripOK cat q α κ depth P br cert.R P.s st = true ∧
        (p : ℝ) ≤ P.s * r + st.V
    · obtain ⟨st, -, hl, hok, hpV⟩ := hsl
      exact strip st P.s hs0 hok (fun _ => ⟨hs, hpV⟩) (fun h => by rw [hl] at h; exact absurd h (by decide))
    by_cases hsr : ∃ st ∈ cert.strips, st.left = false ∧ stripOK cat q α κ depth P br cert.R P.t st = true ∧
        (P.t : ℝ) * r - st.V < p
    · obtain ⟨st, -, hl, hok, hpV⟩ := hsr
      exact strip st P.t (lt_trans hs0 hst) hok (fun h => by rw [hl] at h; exact absurd h (by decide)) (fun _ => ⟨hpV, ht⟩)
    -- off the strips: every condition of the main branch holds
    apply main
    intro c hc
    have hk1 := hK1 c hc
    simp only [condK1, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at hk1
    obtain ⟨⟨hls, hlt⟩, hne⟩ := hk1
    have hlin_s : (c.ell0 α : ℝ) * r + (c.ell1 κ : ℝ) * p =
        r * ((c.lv α κ P.s : ℚ) : ℝ) + (c.ell1 κ : ℝ) * ((p : ℝ) - P.s * r) := by rw [lv_real]; ring
    have hlin_t : (c.ell0 α : ℝ) * r + (c.ell1 κ : ℝ) * p =
        r * ((c.lv α κ P.t : ℚ) : ℝ) + (c.ell1 κ : ℝ) * ((p : ℝ) - P.t * r) := by rw [lv_real]; ring
    have hst' : (P.s : ℝ) < P.t := by exact_mod_cast hst
    by_cases h0s : c.lv α κ P.s = 0
    · -- binding at s: ℓ₁ > 0
      have hne' : c.ell1 κ ≠ 0 := by
        rcases hne with h | h
        · exact absurd h0s h.1
        · exact h
      have hl1 : (0 : ℝ) < c.ell1 κ := by
        have h1 : (c.lv α κ P.t : ℝ) - (c.lv α κ P.s : ℝ) = (c.ell1 κ : ℝ) * (P.t - P.s) := by
          rw [lv_real, lv_real]; ring
        have h2 : (0 : ℝ) ≤ (c.lv α κ P.t : ℚ) := by exact_mod_cast hlt
        rw [h0s] at h1; push_cast at h1
        have h3 : (0 : ℝ) ≤ (c.ell1 κ : ℝ) * (P.t - P.s) := by linarith
        have h4 : (0 : ℝ) ≤ c.ell1 κ := by
          by_contra hc; push_neg at hc; have := mul_neg_of_neg_of_pos hc (sub_pos.2 hst'); linarith
        have h5 : (c.ell1 κ : ℝ) ≠ 0 := by exact_mod_cast hne'
        exact lt_of_le_of_ne h4 (Ne.symm h5)
      rw [h0s] at hlin_s; push_cast at hlin_s
      have hlin_pos : 0 < (c.ell0 α : ℝ) * r + (c.ell1 κ : ℝ) * p := by
        rw [hlin_s]; have : (0 : ℝ) < p - P.s * r := by linarith
        have := mul_pos hl1 this; linarith
      cases hx : c.exactL q
      · -- inexact: off the left strip
        have hneed : ∃ x ∈ br.conds, needL q α κ P.s x = true :=
          ⟨c, hc, by simp [needL, h0s, hx]⟩
        rcases hL with hL | hL
        · exact absurd (List.any_eq_true.2 hneed) (by rw [hL]; decide)
        obtain ⟨st, hstm, hstl, hstok⟩ := hL
        have hoff : P.s * r + st.V < (p : ℝ) := by
          by_contra hcon; push_neg at hcon
          exact hsl ⟨st, hstm, hstl, hstok, hcon⟩
        -- V ≥ (1 - η⁻)/ℓ₁
        have hV : ((1 - c.etaLo q) / |c.ell1 κ| : ℚ) ≤ st.V := by
          unfold stripOK at hstok
          rcases hy : nth cat st.yi with _ | y <;> simp only [hy, reduceCtorEq, Bool.false_eq_true] at hstok
          simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true] at hstok
          have := hstok.1.1.1.2 c hc
          rcases this with h | h
          · exact absurd h0s h
          · exact h
        have hV' : (1 - ((c.etaLo q : ℚ) : ℝ)) / (c.ell1 κ : ℝ) ≤ st.V := by
          have := (Rat.cast_le (K := ℝ)).2 hV
          push_cast at this
          rwa [abs_of_pos hl1] at this
        rw [div_le_iff₀ hl1] at hV'
        apply Cond.holds_large c hrd
        rw [hlin_s]
        have := mul_pos hl1 (show (0 : ℝ) < p - P.s * r - st.V by linarith); linarith
      · exact Cond.holds_left c hrd hp2 hx hlin_pos
    by_cases h0t : c.lv α κ P.t = 0
    · -- binding at t: ℓ₁ < 0
      have hne' : c.ell1 κ ≠ 0 := by
        rcases hne with h | h
        · exact absurd h0t h.2
        · exact h
      have hl1 : (c.ell1 κ : ℝ) < 0 := by
        have h1 : (c.lv α κ P.t : ℝ) - (c.lv α κ P.s : ℝ) = (c.ell1 κ : ℝ) * (P.t - P.s) := by
          rw [lv_real, lv_real]; ring
        have h2 : (0 : ℝ) ≤ (c.lv α κ P.s : ℚ) := by exact_mod_cast hls
        rw [h0t] at h1; push_cast at h1
        have h3 : (c.ell1 κ : ℝ) * (P.t - P.s) ≤ 0 := by linarith
        have h4 : (c.ell1 κ : ℝ) ≤ 0 := by
          by_contra hc; push_neg at hc; have := mul_pos hc (sub_pos.2 hst'); linarith
        have h5 : (c.ell1 κ : ℝ) ≠ 0 := by exact_mod_cast hne'
        exact lt_of_le_of_ne h4 h5
      rw [h0t] at hlin_t; push_cast at hlin_t
      have hlin_nn : 0 ≤ (c.ell0 α : ℝ) * r + (c.ell1 κ : ℝ) * p := by
        rw [hlin_t]; have : (p : ℝ) - P.t * r ≤ 0 := by linarith
        have := mul_nonneg (show (0 : ℝ) ≤ -(c.ell1 κ : ℝ) by linarith) (show (0 : ℝ) ≤ -((p : ℝ) - P.t * r) by linarith); linarith
      cases hx : c.exactR q
      · have hneed : ∃ x ∈ br.conds, needR q α κ P.t x = true :=
          ⟨c, hc, by simp [needR, h0t, hx]⟩
        rcases hRt with hRt | hRt
        · exact absurd (List.any_eq_true.2 hneed) (by rw [hRt]; decide)
        obtain ⟨st, hstm, hstl, hstok⟩ := hRt
        have hstl' : st.left = false := by simpa using hstl
        have hoff : (p : ℝ) ≤ P.t * r - st.V := by
          by_contra hcon; push_neg at hcon
          exact hsr ⟨st, hstm, hstl', hstok, hcon⟩
        have hV : ((1 - c.etaLo q) / |c.ell1 κ| : ℚ) ≤ st.V := by
          unfold stripOK at hstok
          rcases hy : nth cat st.yi with _ | y <;> simp only [hy, reduceCtorEq, Bool.false_eq_true] at hstok
          simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true] at hstok
          have := hstok.1.1.1.2 c hc
          rcases this with h | h
          · exact absurd h0t h
          · exact h
        have hV' : (1 - ((c.etaLo q : ℚ) : ℝ)) / (-(c.ell1 κ : ℝ)) ≤ st.V := by
          have := (Rat.cast_le (K := ℝ)).2 hV
          push_cast at this
          rwa [abs_of_neg hl1] at this
        rw [div_le_iff₀ (by linarith)] at hV'
        apply Cond.holds_large c hrd
        rw [hlin_t]
        have := mul_nonneg (show (0 : ℝ) ≤ -(c.ell1 κ : ℝ) by linarith) (show (0 : ℝ) ≤ P.t * r - st.V - p by linarith); linarith
      · exact Cond.holds_right c hrd hp2 hx hlin_nn
    -- non-binding
    have hR := hR4 c hc
    simp only [condRok, Bool.or_eq_true, decide_eq_true_eq] at hR
    rcases hR with hR | hR
    · rcases hR with h | h
      · exact absurd h h0s
      · exact absurd h h0t
    have hmin : (0 : ℚ) < min (c.lv α κ P.s) (c.lv α κ P.t) :=
      lt_min (lt_of_le_of_ne hls (Ne.symm h0s)) (lt_of_le_of_ne hlt (Ne.symm h0t))
    have hmin' : (0 : ℝ) < (min (c.lv α κ P.s) (c.lv α κ P.t) : ℚ) := by exact_mod_cast hmin
    have h1 : (((1 - c.etaLo q) / min (c.lv α κ P.s) (c.lv α κ P.t) : ℚ) : ℝ) ≤ r := by
      have := (Rat.cast_le (K := ℝ)).2 hR; linarith
    rw [Rat.cast_div, div_le_iff₀ hmin'] at h1
    have h2 := lin_ge_min α κ P.s P.t c hrR hs.le ht
    rw [Rat.cast_sub, Rat.cast_one] at h1
    apply Cond.holds_large c hrd
    linarith

end Large

/-! ### Translation data -/

/-- **A translation of the base catalogue** `kb` along the lattice shift `(r, p, m) ↦ (r + n b p, p, m + n a p)`:
the debit is preserved, the price is covariant with the constant `Kc` (`τ_{ρ n B}(σ_n x) = τ_B(x) + n Kc p`), and the
conditions of `B` at `x` give those of `ρ n B` at `σ_n x` (within the ambient range `r + n b p ≤ Ω p`). -/
structure Transl (b a Kc Ω : ℕ) (kb : List KBranch) where
  ρ : ℕ → KBranch → KBranch
  debit : ∀ n br, (ρ n br).debit = br.debit
  price : ∀ n br, br ∈ kb → ∀ (r p m : ℕ) (kv : ℕ → ℕ),
    (ρ n br).τ.evalN (r + n * b * p) p (m + n * a * p) kv = br.τ.evalN r p m kv + n * Kc * p
  cond : ∀ n br, br ∈ kb → ∀ (r p m : ℕ) (kv : ℕ → ℕ), r + n * b * p ≤ Ω * p →
    (∀ cd ∈ br.conds, cd.Holds r p m kv) →
    ∀ cd ∈ (ρ n br).conds, cd.Holds (r + n * b * p) p (m + n * a * p) kv

/-- The pullback of a condition along the lattice shift of order `n`. -/
def KCond.shift (b a n : ℕ) (c : KCond) : KCond :=
  ⟨c.cr, c.cp - n * (b * c.cr + a * c.cm), c.cm, c.ck, c.c1, c.strict⟩

theorem KCond.L_shift (b a n : ℕ) (c : KCond) (r p m : ℕ) (kv : ℕ → ℕ) :
    (c.shift b a n).L (r + n * b * p) p (m + n * a * p) kv = c.L r p m kv := by
  unfold KCond.L KCond.shift
  push_cast
  ring

theorem KCond.holds_shift (b a n : ℕ) (c : KCond) (r p m : ℕ) (kv : ℕ → ℕ) :
    (c.shift b a n).Holds (r + n * b * p) p (m + n * a * p) kv ↔ c.Holds r p m kv := by
  unfold KCond.Holds
  have hs : (c.shift b a n).strict = c.strict := rfl
  rw [hs, KCond.L_shift]

/-- **The plain pullback** `ρ n B = (τ_B, conds^[n], debit)` is a translation as soon as the prices are covariant. -/
def Transl.pullback (b a Kc Ω : ℕ) (kb : List KBranch)
    (hT1 : ∀ br ∈ kb, ∀ (n r p m : ℕ) (kv : ℕ → ℕ),
      br.τ.evalN (r + n * b * p) p (m + n * a * p) kv = br.τ.evalN r p m kv + n * Kc * p) :
    Transl b a Kc Ω kb where
  ρ n br := ⟨br.τ, br.conds.map (KCond.shift b a n), br.debit⟩
  debit _ _ := rfl
  price n br hbr r p m kv := hT1 br hbr n r p m kv
  cond n br _ r p m kv _ h cd hcd := by
    obtain ⟨cd', hcd', rfl⟩ := List.mem_map.1 hcd
    exact (KCond.holds_shift b a n cd' r p m kv).2 (h cd' hcd')

/-! ### Base cells and their translates -/

/-- The crude exponent bound at scales `≤ N`: `2 N (3 ⌊log₂ 14 N⌋ + c_F)`. -/
def crudeBd (cF N : ℕ) : ℕ := 2 * N * (3 * Nat.log 2 (14 * N) + cF)

theorem ecrude_le_bd {cF r N p : ℕ} (hp : 2 ≤ p) (hrN : r ≤ N) :
    2 * r * (3 * Nat.log p (14 * r) + cF) ≤ crudeBd cF N := by
  unfold crudeBd
  have h1 : Nat.log p (14 * r) ≤ Nat.log 2 (14 * r) := Nat.log_anti_left (by norm_num) hp
  have h2 : Nat.log 2 (14 * r) ≤ Nat.log 2 (14 * N) := Nat.log_mono_right (by omega)
  exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 hrN) (by omega)

/-- **Soundness of a base cell** `(P, R)` against the catalogue `cat` of the class `j`.  The configuration is a master
root (`Q k = j p + oM`, with the frame facts `KParams`), as in `PieceCov`: a prefix cell needs the pole indices. -/
def BaseSound (D : KBankData) (cat : List Branch) (j : ℕ) (P : QPiece) (R : ℚ) : Prop :=
  KParams D → (∀ y ∈ D.shifts, y.s * j % y.q ≠ 0) →
  ∀ (r p m k del : ℕ) (Good : ℕ → Prop), D.Q * k = j * p + D.oM → D.Q * (r + 2 * m) < p * p →
    Cond.Round D.Q r p m k D.α ((j : ℚ) / D.Q) → D.Pbad < p → p % 2 = 1 → 2 ≤ p → del ≤ D.depth →
    0 < r → (R : ℝ) ≤ r → (P.s : ℝ) * r < p → (p : ℝ) ≤ P.t * r →
    BranchesValid cat D.Pbad D.Q r p m k del Good →
    ∃ n, Good n ∧ (n : ℝ) ≤ P.a * r + P.b * p + P.C

/-- A `pieceOK` cell is sound (Theorem B, large scales). -/
theorem baseSound_of_pieceOK {D : KBankData} (hq : 1 ≤ D.Q) (hα : 0 ≤ D.α) {j : ℕ} {cat : List Branch}
    {x : QPiece × Cert}
    (hok : pieceOK cat D.Q D.α ((j : ℚ) / D.Q) D.depth D.cF D.Pbad x.1 x.2 = true) :
    BaseSound D cat j x.1 x.2.R := by
  intro _ _ r p m k del Good _ _ hrd hPb hodd hpge hdel _ hR hs ht hBV
  exact piece_sound_large x.1 x.2 hok hq hα Good hrd (fun _ => hodd) hpge hdel (by exact_mod_cast hR) hBV hs ht

/-- The `n`-th translate of a base cell `P` with threshold `R`. -/
def trPiece (b Kc cF : ℕ) (R : ℚ) (n : ℕ) (P : QPiece) : QPiece :=
  ⟨P.s / (1 + (n : ℚ) * b * P.s), P.t / (1 + (n : ℚ) * b * P.t), P.a, P.b + ((Kc : ℚ) - P.a * b) * n,
    P.C + (crudeBd cF ⌈R * (1 + (n : ℚ) * b * P.t)⌉₊ : ℚ)⟩

/-- **(K0) for a translate**: positivity, order and the nonnegative line at both ends. -/
theorem trPiece_basic {P : QPiece} (hP : PieceBasic P) (b Kc cF : ℕ) (R : ℚ) (n : ℕ) :
    PieceBasic (trPiece b Kc cF R n P) := by
  obtain ⟨hs0, hst, hC0, ha0, ha1⟩ := hP
  have ht0 : 0 < P.t := lt_trans hs0 hst
  have hds : (0 : ℚ) < 1 + (n : ℚ) * b * P.s := by positivity
  have hdt : (0 : ℚ) < 1 + (n : ℚ) * b * P.t := by positivity
  have hK : (0 : ℚ) ≤ (crudeBd cF ⌈R * (1 + (n : ℚ) * b * P.t)⌉₊ : ℚ) := Nat.cast_nonneg _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show 0 < P.s / (1 + (n : ℚ) * b * P.s)
    positivity
  · show P.s / (1 + (n : ℚ) * b * P.s) < P.t / (1 + (n : ℚ) * b * P.t)
    rw [div_lt_div_iff₀ hds hdt]
    nlinarith [hst]
  · show 0 ≤ P.C + _
    linarith
  · show 0 ≤ P.a + (P.b + ((Kc : ℚ) - P.a * b) * n) * (P.s / (1 + (n : ℚ) * b * P.s))
    have e : P.a + (P.b + ((Kc : ℚ) - P.a * b) * n) * (P.s / (1 + (n : ℚ) * b * P.s)) =
        (P.a + P.b * P.s) / (1 + (n : ℚ) * b * P.s) + n * Kc * (P.s / (1 + (n : ℚ) * b * P.s)) := by
      field_simp
      ring
    rw [e]
    have h1 : 0 ≤ (n : ℚ) * Kc * (P.s / (1 + (n : ℚ) * b * P.s)) := by positivity
    have h2 := div_nonneg ha0 hds.le
    linarith
  · show 0 ≤ P.a + (P.b + ((Kc : ℚ) - P.a * b) * n) * (P.t / (1 + (n : ℚ) * b * P.t))
    have e : P.a + (P.b + ((Kc : ℚ) - P.a * b) * n) * (P.t / (1 + (n : ℚ) * b * P.t)) =
        (P.a + P.b * P.t) / (1 + (n : ℚ) * b * P.t) + n * Kc * (P.t / (1 + (n : ℚ) * b * P.t)) := by
      field_simp
      ring
    rw [e]
    have h1 : 0 ≤ (n : ℚ) * Kc * (P.t / (1 + (n : ℚ) * b * P.t)) := by positivity
    have h2 := div_nonneg ha1 hdt.le
    linarith

/-! ### Claim (P): the piece bound of a translate -/

set_option maxHeartbeats 4000000 in
/-- **Theorem PC (the piece bound of the `n`-th translate of a sound base cell).**  `(P, R)` is a sound cell of the class
`j` against the base catalogue `kb` (compiled), the translates `ρ n kb` of the base catalogue are valid on the family
(T2), prices are covariant (T1, inside `tr`), and the strip lies in the ambient range (`1 / s + n b ≤ Ω`).  Then the
translated piece `trPiece b Kc c_F R n P` has the piece bound `n_p ≤ A r + B_n p + C_n` at every admissible member of
every scale, `p ∈ (s_n r, t_n r]`. -/
theorem exp_cov_per {D : KBankData} (hpar : KParams D) {c : ℚ} {hc : 0 < c} {const : ℝ} {depth : ℕ}
    {Q : NodeFamily.Index (altGeom c hc).geometry → ℚ[X]} {N0 : ℕ}
    (hdepth : depth ≤ D.depth) (hQ : AltQ c hc D.cF Q)
    {b a Kc Ω : ℕ} (hab : D.α * b = a) {kb : List KBranch} (tr : Transl b a Kc Ω kb)
    (hvalid : ∀ n, KCatValidFam c hc const depth Q D.shifts D.Q D.Pbad N0 (kb.map (tr.ρ n)))
    {j : ℕ} {P : QPiece} {R : ℚ} (hP : PieceBasic P)
    (hbase : BaseSound D (kb.map (KBranch.compile D.tS (D.bS j) D.cS)) j P R)
    (n : ℕ) (hΩ : 1 / P.s + (n : ℚ) * b ≤ Ω) :
    PieceCov D c hc const depth Q N0 j (trPiece b Kc D.cF R n P) := by
  intro i hi hr0 p k _ hk hN hPb hqN hrd hjs hs ht
  have hpar' := hpar
  obtain ⟨hq2, hqP, -, -, -, -, hα, -, -, -⟩ := hpar'
  have hpp : p.Prime := Fact.out
  have hp2 : 2 ≤ p := hpp.two_le
  have hr2 : i.1 % 2 = 0 := hi.2
  have hdel : delCount (altGeom c hc) i ≤ D.depth :=
    (show delCount (altGeom c hc) i ≤ depth from hi.1).trans hdepth
  have hodd : p % 2 = 1 := by
    rcases hpp.eq_two_or_odd with h | h
    · omega
    · exact h
  obtain ⟨hle0, hr⟩ := kv_roots hpar hjs hk hPb
  obtain ⟨kv, hkv⟩ : ∃ kv : ℕ → ℕ, kv = fun n => D.tS n * k - (D.bS j n * p + D.cS n) := ⟨_, rfl⟩
  have hroots : ∀ n < D.shifts.length, ∃ jn,
      (shAt D.shifts n).q * kv n = jn * p + (shAt D.shifts n).o ∧ 0 < jn ∧ jn < (shAt D.shifts n).q ∧
      0 < kv n ∧ kv n < p := fun n hn => by
    obtain ⟨-, -, -, h1, h2, h3, h4, h5⟩ := hr n hn
    subst hkv
    exact ⟨_, h1, h2, h3, h4, h5⟩
  set r := i.1 with hrdef
  set m := (altGeom c hc).borderSize r with hmdef
  obtain ⟨hs0, hst, hC0, ha0, ha1⟩ := hP
  have hP' : PieceBasic P := ⟨hs0, hst, hC0, ha0, ha1⟩
  have ht0 : 0 < P.t := lt_trans hs0 hst
  have hpQ : (0 : ℚ) < p := by exact_mod_cast hpp.pos
  have hrQ : (0 : ℚ) < r := by exact_mod_cast hr0
  have hds : (0 : ℚ) < 1 + (n : ℚ) * b * P.s := by positivity
  have hdt : (0 : ℚ) < 1 + (n : ℚ) * b * P.t := by positivity
  have hnb0 : (0 : ℚ) ≤ (n : ℚ) * b := by positivity
  -- the translated cell in rational form
  have hs' : P.s / (1 + (n : ℚ) * b * P.s) * (r : ℚ) < p := by
    have h := hs
    simp only [trPiece] at h
    exact_mod_cast h
  have ht' : (p : ℚ) ≤ P.t / (1 + (n : ℚ) * b * P.t) * (r : ℚ) := by
    have h := ht
    simp only [trPiece] at h
    exact_mod_cast h
  have hs'' : P.s * r < p * (1 + (n : ℚ) * b * P.s) := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hds] at hs'
    exact hs'
  have ht'' : (p : ℚ) * (1 + (n : ℚ) * b * P.t) ≤ P.t * r := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hdt] at ht'
    exact ht'
  -- n b p < r
  have hnbpQ : (n : ℚ) * b * p < r := by
    by_contra h
    push_neg at h
    have := mul_le_mul_of_nonneg_left h ht0.le
    nlinarith
  have hnbp : n * b * p < r := by exact_mod_cast hnbpQ
  obtain ⟨r', hr'eq⟩ : ∃ r', r' + n * b * p = r := ⟨r - n * b * p, by omega⟩
  have hr'Q : (r : ℚ) = r' + (n : ℚ) * b * p := by
    have : ((r' + n * b * p : ℕ) : ℚ) = r := by exact_mod_cast hr'eq
    push_cast at this
    linarith
  -- the base configuration
  have ht3 : (p : ℚ) ≤ P.t * r' := by
    rw [hr'Q] at ht''
    nlinarith
  have hs3 : P.s * r' < p := by
    rw [hr'Q] at hs''
    nlinarith
  have hr'pos : 0 < r' := by
    rcases Nat.eq_zero_or_pos r' with h | h
    · rw [h] at ht3
      simp only [Nat.cast_zero, mul_zero] at ht3
      linarith
    · exact h
  -- m' = m - n a p
  have habR : (D.α : ℝ) * b = a := by exact_mod_cast hab
  have hαR : (0 : ℝ) ≤ D.α := by exact_mod_cast hα
  have hrR : (r : ℝ) = r' + (n : ℝ) * b * p := by
    have : ((r' + n * b * p : ℕ) : ℝ) = r := by exact_mod_cast hr'eq
    push_cast at this
    linarith
  have e1 : (D.α : ℝ) * (n * b * p) = n * a * p := by
    rw [← habR]; ring
  have e2 : (D.α : ℝ) * r = D.α * r' + n * a * p := by
    rw [hrR, mul_add, e1]
  have hnap : n * a * p ≤ m := by
    by_contra h
    push_neg at h
    have h1 : ((m + 1 : ℕ) : ℝ) ≤ ((n * a * p : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at h1
    have h2 := hrd.m_lo
    have h3 : 0 ≤ (D.α : ℝ) * r' := mul_nonneg hαR (Nat.cast_nonneg _)
    linarith
  obtain ⟨m', hm'eq⟩ : ∃ m', m' + n * a * p = m := ⟨m - n * a * p, by omega⟩
  have hmR : (m' : ℝ) + n * a * p = m := by
    have : ((m' + n * a * p : ℕ) : ℝ) = m := by exact_mod_cast hm'eq
    push_cast at this
    linarith
  have hrd' : Cond.Round D.Q r' p m' k D.α ((j : ℚ) / D.Q) := by
    refine ⟨?_, ?_, hrd.k_lo, hrd.k_hi⟩
    · have := hrd.m_lo
      linarith
    · have := hrd.m_hi
      linarith
  have hqN' : D.Q * (r' + 2 * m') < p * p :=
    lt_of_le_of_lt (Nat.mul_le_mul_left _ (by omega)) hqN
  -- the ambient range
  have hΩp : r' + n * b * p ≤ Ω * p := by
    rw [hr'eq]
    have h1 : (r : ℚ) < p * (1 / P.s + (n : ℚ) * b) := by
      have e : (p : ℚ) * (1 / P.s + (n : ℚ) * b) = p * (1 + (n : ℚ) * b * P.s) / P.s := by
        field_simp
      rw [e, lt_div_iff₀ hs0]
      linarith
    have h2 : (p : ℚ) * (1 / P.s + (n : ℚ) * b) ≤ p * Ω := mul_le_mul_of_nonneg_left hΩ hpQ.le
    have : (r : ℚ) ≤ Ω * p := by linarith
    exact_mod_cast this
  -- the line of the translate is nonnegative on the cell
  obtain ⟨-, -, -, hl0, hl1⟩ := trPiece_basic hP' b Kc D.cF R n
  by_cases hRn : R * (1 + (n : ℚ) * b * P.t) ≤ (r : ℚ)
  · -- large scale: Theorem B at the configuration (r', p, m', k)
    have hRr' : R ≤ (r' : ℚ) := by
      have h1 : (n : ℚ) * b * p ≤ (n : ℚ) * b * (P.t * r') := mul_le_mul_of_nonneg_left ht3 hnb0
      have h2 : R * (1 + (n : ℚ) * b * P.t) ≤ r' * (1 + (n : ℚ) * b * P.t) := by nlinarith
      exact le_of_mul_le_mul_right h2 hdt
    have hs3R : (P.s : ℝ) * r' < p := by exact_mod_cast hs3
    have ht3R : (p : ℝ) ≤ P.t * r' := by exact_mod_cast ht3
    have hRr'R : (R : ℝ) ≤ r' := by exact_mod_cast hRr'
    have hBV : BranchesValid (kb.map (KBranch.compile D.tS (D.bS j) D.cS)) D.Pbad D.Q r' p m' k
        (delCount (altGeom c hc) i)
        (fun e => GLE p (e + n * Kc * p) ((AltEvenFam c hc const depth Q).Q i)) := by
      intro b' hb' _ _ hcond
      obtain ⟨kbr, hkbr, rfl⟩ := List.mem_map.1 hb'
      have hcondK : ∀ cd ∈ kbr.conds, cd.Holds r' p m' kv := by
        intro cd hcd
        have := (KCond.holds_compile D.tS (D.bS j) D.cS cd r' p m' k hle0).1
          (hcond _ (List.mem_map.2 ⟨cd, hcd, rfl⟩))
        rw [hkv]
        exact this
      have hcondX := tr.cond n kbr hkbr r' p m' kv hΩp hcondK
      rw [hr'eq, hm'eq] at hcondX
      obtain ⟨nn, hnn, hlen⟩ := hvalid n (tr.ρ n kbr) (List.mem_map.2 ⟨kbr, hkbr, rfl⟩) i hi hr0 p hPb hN
        hqN kv hroots hcondX
      have hpr := tr.price n kbr hkbr r' p m' kv
      rw [hr'eq, hm'eq] at hpr
      rw [hpr, tr.debit] at hlen
      have e1 : (kbr.compile D.tS (D.bS j) D.cS).τ.evalN r' p m' k = kbr.τ.evalN r' p m' kv := by
        rw [KBranch.evalN_compile, hkv]
      have e2 : (kbr.compile D.tS (D.bS j) D.cS).debit = kbr.debit := rfl
      refine ⟨nn - n * Kc * p, ?_, ?_⟩
      · exact GLE.mono (by omega) hnn
      · rw [e1, e2]
        exact tsub_le_iff_right.2 (by linarith)
    obtain ⟨e, he, hbd⟩ := hbase hpar hjs r' p m' k (delCount (altGeom c hc) i) _ hk hqN' hrd' hPb hodd hp2 hdel
      hr'pos hRr'R hs3R ht3R hBV
    refine ⟨e + n * Kc * p, he, ?_⟩
    have hcr : (0 : ℝ) ≤ (crudeBd D.cF ⌈R * (1 + (n : ℚ) * b * P.t)⌉₊ : ℝ) := Nat.cast_nonneg _
    simp only [trPiece]
    push_cast
    rw [hrR]
    nlinarith [hbd, hcr]
  · -- small scale: the crude exponent
    have hlt : r < ⌈R * (1 + (n : ℚ) * b * P.t)⌉₊ := Nat.lt_ceil.2 (not_le.1 hRn)
    have hcrude : GLE p (2 * r * (3 * Nat.log p (14 * r) + D.cF)) ((AltEvenFam c hc const depth Q).Q i) :=
      hQ.crude i hr2 p
    refine ⟨_, hcrude, ?_⟩
    have h1 := ecrude_le_bd (cF := D.cF) hp2 hlt.le
    have h2 : ((2 * r * (3 * Nat.log p (14 * r) + D.cF) : ℕ) : ℝ) ≤
        (crudeBd D.cF ⌈R * (1 + (n : ℚ) * b * P.t)⌉₊ : ℝ) := by exact_mod_cast h1
    have hline := line_nonneg_scaled (r := (r : ℝ)) (p := (p : ℝ)) (by exact_mod_cast hr0) hs ht hl0 hl1
    have hC : ((trPiece b Kc D.cF R n P).C : ℝ) =
        P.C + (crudeBd D.cF ⌈R * (1 + (n : ℚ) * b * P.t)⌉₊ : ℝ) := by
      simp only [trPiece]
      push_cast
      ring
    have hCnn : (0 : ℝ) ≤ P.C := by exact_mod_cast hC0
    rw [hC]
    linarith

theorem exp_cov_per_large {D : KBankData} (hpar : KParams D) {c : ℚ} {hc : 0 < c} {const : ℝ} {depth : ℕ}
    {Q : NodeFamily.Index (altGeom c hc).geometry → ℚ[X]} {N0 : ℕ}
    (hdepth : depth ≤ D.depth)
    {b a Kc Ω : ℕ} (hab : D.α * b = a) {kb : List KBranch} (tr : Transl b a Kc Ω kb)
    (hvalid : ∀ n, KCatValidFam c hc const depth Q D.shifts D.Q D.Pbad N0 (kb.map (tr.ρ n)))
    {j : ℕ} {P : QPiece} {R : ℚ} (hP : PieceBasic P)
    (hbase : BaseSound D (kb.map (KBranch.compile D.tS (D.bS j) D.cS)) j P R)
    (hRlim : R * P.t ≤ (N0 : ℚ)) (n : ℕ) (hΩ : 1 / P.s + (n : ℚ) * b ≤ Ω) :
    PieceCov D c hc const depth Q N0 j (trPiece b Kc D.cF R n P) := by
  intro i hi hr0 p k _ hk hN hPb hqN hrd hjs hs ht
  have hpar' := hpar
  obtain ⟨hq2, hqP, -, -, -, -, hα, -, -, -⟩ := hpar'
  have hpp : p.Prime := Fact.out
  have hp2 : 2 ≤ p := hpp.two_le
  have hr2 : i.1 % 2 = 0 := hi.2
  have hdel : delCount (altGeom c hc) i ≤ D.depth :=
    (show delCount (altGeom c hc) i ≤ depth from hi.1).trans hdepth
  have hodd : p % 2 = 1 := by
    rcases hpp.eq_two_or_odd with h | h
    · omega
    · exact h
  obtain ⟨hle0, hr⟩ := kv_roots hpar hjs hk hPb
  obtain ⟨kv, hkv⟩ : ∃ kv : ℕ → ℕ, kv = fun n => D.tS n * k - (D.bS j n * p + D.cS n) := ⟨_, rfl⟩
  have hroots : ∀ n < D.shifts.length, ∃ jn,
      (shAt D.shifts n).q * kv n = jn * p + (shAt D.shifts n).o ∧ 0 < jn ∧ jn < (shAt D.shifts n).q ∧
      0 < kv n ∧ kv n < p := fun n hn => by
    obtain ⟨-, -, -, h1, h2, h3, h4, h5⟩ := hr n hn
    subst hkv
    exact ⟨_, h1, h2, h3, h4, h5⟩
  set r := i.1 with hrdef
  set m := (altGeom c hc).borderSize r with hmdef
  obtain ⟨hs0, hst, hC0, ha0, ha1⟩ := hP
  have hP' : PieceBasic P := ⟨hs0, hst, hC0, ha0, ha1⟩
  have ht0 : 0 < P.t := lt_trans hs0 hst
  have hpQ : (0 : ℚ) < p := by exact_mod_cast hpp.pos
  have hrQ : (0 : ℚ) < r := by exact_mod_cast hr0
  have hds : (0 : ℚ) < 1 + (n : ℚ) * b * P.s := by positivity
  have hdt : (0 : ℚ) < 1 + (n : ℚ) * b * P.t := by positivity
  have hnb0 : (0 : ℚ) ≤ (n : ℚ) * b := by positivity
  -- the translated cell in rational form
  have hs' : P.s / (1 + (n : ℚ) * b * P.s) * (r : ℚ) < p := by
    have h := hs
    simp only [trPiece] at h
    exact_mod_cast h
  have ht' : (p : ℚ) ≤ P.t / (1 + (n : ℚ) * b * P.t) * (r : ℚ) := by
    have h := ht
    simp only [trPiece] at h
    exact_mod_cast h
  have hs'' : P.s * r < p * (1 + (n : ℚ) * b * P.s) := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hds] at hs'
    exact hs'
  have ht'' : (p : ℚ) * (1 + (n : ℚ) * b * P.t) ≤ P.t * r := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hdt] at ht'
    exact ht'
  -- n b p < r
  have hnbpQ : (n : ℚ) * b * p < r := by
    by_contra h
    push_neg at h
    have := mul_le_mul_of_nonneg_left h ht0.le
    nlinarith
  have hnbp : n * b * p < r := by exact_mod_cast hnbpQ
  obtain ⟨r', hr'eq⟩ : ∃ r', r' + n * b * p = r := ⟨r - n * b * p, by omega⟩
  have hr'Q : (r : ℚ) = r' + (n : ℚ) * b * p := by
    have : ((r' + n * b * p : ℕ) : ℚ) = r := by exact_mod_cast hr'eq
    push_cast at this
    linarith
  -- the base configuration
  have ht3 : (p : ℚ) ≤ P.t * r' := by
    rw [hr'Q] at ht''
    nlinarith
  have hs3 : P.s * r' < p := by
    rw [hr'Q] at hs''
    nlinarith
  have hr'pos : 0 < r' := by
    rcases Nat.eq_zero_or_pos r' with h | h
    · rw [h] at ht3
      simp only [Nat.cast_zero, mul_zero] at ht3
      linarith
    · exact h
  -- m' = m - n a p
  have habR : (D.α : ℝ) * b = a := by exact_mod_cast hab
  have hαR : (0 : ℝ) ≤ D.α := by exact_mod_cast hα
  have hrR : (r : ℝ) = r' + (n : ℝ) * b * p := by
    have : ((r' + n * b * p : ℕ) : ℝ) = r := by exact_mod_cast hr'eq
    push_cast at this
    linarith
  have e1 : (D.α : ℝ) * (n * b * p) = n * a * p := by
    rw [← habR]; ring
  have e2 : (D.α : ℝ) * r = D.α * r' + n * a * p := by
    rw [hrR, mul_add, e1]
  have hnap : n * a * p ≤ m := by
    by_contra h
    push_neg at h
    have h1 : ((m + 1 : ℕ) : ℝ) ≤ ((n * a * p : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at h1
    have h2 := hrd.m_lo
    have h3 : 0 ≤ (D.α : ℝ) * r' := mul_nonneg hαR (Nat.cast_nonneg _)
    linarith
  obtain ⟨m', hm'eq⟩ : ∃ m', m' + n * a * p = m := ⟨m - n * a * p, by omega⟩
  have hmR : (m' : ℝ) + n * a * p = m := by
    have : ((m' + n * a * p : ℕ) : ℝ) = m := by exact_mod_cast hm'eq
    push_cast at this
    linarith
  have hrd' : Cond.Round D.Q r' p m' k D.α ((j : ℚ) / D.Q) := by
    refine ⟨?_, ?_, hrd.k_lo, hrd.k_hi⟩
    · have := hrd.m_lo
      linarith
    · have := hrd.m_hi
      linarith
  have hqN' : D.Q * (r' + 2 * m') < p * p :=
    lt_of_le_of_lt (Nat.mul_le_mul_left _ (by omega)) hqN
  -- the ambient range
  have hΩp : r' + n * b * p ≤ Ω * p := by
    rw [hr'eq]
    have h1 : (r : ℚ) < p * (1 / P.s + (n : ℚ) * b) := by
      have e : (p : ℚ) * (1 / P.s + (n : ℚ) * b) = p * (1 + (n : ℚ) * b * P.s) / P.s := by
        field_simp
      rw [e, lt_div_iff₀ hs0]
      linarith
    have h2 : (p : ℚ) * (1 / P.s + (n : ℚ) * b) ≤ p * Ω := mul_le_mul_of_nonneg_left hΩ hpQ.le
    have : (r : ℚ) ≤ Ω * p := by linarith
    exact_mod_cast this
  -- the line of the translate is nonnegative on the cell
  obtain ⟨-, -, -, hl0, hl1⟩ := trPiece_basic hP' b Kc D.cF R n
  have hRn : R * (1 + (n : ℚ) * b * P.t) ≤ (r : ℚ) := by
    have hNp : (N0 : ℚ) < p := by exact_mod_cast hN
    have h1 := mul_lt_mul_of_pos_right (lt_of_le_of_lt hRlim hNp) hdt
    have h2 : (R * (1 + (n : ℚ) * b * P.t)) * P.t < (r : ℚ) * P.t := by
      nlinarith [ht'']
    exact le_of_mul_le_mul_right h2.le ht0
  -- large scale: Theorem B at the configuration (r', p, m', k)
  have hRr' : R ≤ (r' : ℚ) := by
    have h1 : (n : ℚ) * b * p ≤ (n : ℚ) * b * (P.t * r') := mul_le_mul_of_nonneg_left ht3 hnb0
    have h2 : R * (1 + (n : ℚ) * b * P.t) ≤ r' * (1 + (n : ℚ) * b * P.t) := by nlinarith
    exact le_of_mul_le_mul_right h2 hdt
  have hs3R : (P.s : ℝ) * r' < p := by exact_mod_cast hs3
  have ht3R : (p : ℝ) ≤ P.t * r' := by exact_mod_cast ht3
  have hRr'R : (R : ℝ) ≤ r' := by exact_mod_cast hRr'
  have hBV : BranchesValid (kb.map (KBranch.compile D.tS (D.bS j) D.cS)) D.Pbad D.Q r' p m' k
      (delCount (altGeom c hc) i)
      (fun e => GLE p (e + n * Kc * p) ((AltEvenFam c hc const depth Q).Q i)) := by
    intro b' hb' _ _ hcond
    obtain ⟨kbr, hkbr, rfl⟩ := List.mem_map.1 hb'
    have hcondK : ∀ cd ∈ kbr.conds, cd.Holds r' p m' kv := by
      intro cd hcd
      have := (KCond.holds_compile D.tS (D.bS j) D.cS cd r' p m' k hle0).1
        (hcond _ (List.mem_map.2 ⟨cd, hcd, rfl⟩))
      rw [hkv]
      exact this
    have hcondX := tr.cond n kbr hkbr r' p m' kv hΩp hcondK
    rw [hr'eq, hm'eq] at hcondX
    obtain ⟨nn, hnn, hlen⟩ := hvalid n (tr.ρ n kbr) (List.mem_map.2 ⟨kbr, hkbr, rfl⟩) i hi hr0 p hPb hN
      hqN kv hroots hcondX
    have hpr := tr.price n kbr hkbr r' p m' kv
    rw [hr'eq, hm'eq] at hpr
    rw [hpr, tr.debit] at hlen
    have e1 : (kbr.compile D.tS (D.bS j) D.cS).τ.evalN r' p m' k = kbr.τ.evalN r' p m' kv := by
      rw [KBranch.evalN_compile, hkv]
    have e2 : (kbr.compile D.tS (D.bS j) D.cS).debit = kbr.debit := rfl
    refine ⟨nn - n * Kc * p, ?_, ?_⟩
    · exact GLE.mono (by omega) hnn
    · rw [e1, e2]
      exact tsub_le_iff_right.2 (by linarith)
  obtain ⟨e, he, hbd⟩ := hbase hpar hjs r' p m' k (delCount (altGeom c hc) i) _ hk hqN' hrd' hPb hodd hp2 hdel
    hr'pos hRr'R hs3R ht3R hBV
  refine ⟨e + n * Kc * p, he, ?_⟩
  have hcr : (0 : ℝ) ≤ (crudeBd D.cF ⌈R * (1 + (n : ℚ) * b * P.t)⌉₊ : ℝ) := Nat.cast_nonneg _
  simp only [trPiece]
  push_cast
  rw [hrR]
  nlinarith [hbd, hcr]

/-! ### Templates with a periodic layer -/

/-- A class template with a periodic layer: the table `cells` (one period, increasing `θ`, each cell with its
certificate; the cell certificate is only read through `Cert.R`), `N` strips, the head pieces, the tail branch. -/
structure KTmplP where
  t1 : ℚ
  N : ℕ
  top : ℕ
  cells : List (QPiece × Cert)
  head : List (QPiece × Cert)
  tb : ℕ

/-- The partial strip `N` (the last `top` cells of the table, i.e. the lowest `u`), then the strips
`n = N - 1, …, 0` (increasing `θ`) of the translates of the table. -/
def expPer (b Kc cF N top : ℕ) (cells : List (QPiece × Cert)) : List (QPiece × Cert) :=
  (cells.drop (cells.length - top)).map (fun x => (trPiece b Kc cF x.2.R N x.1, dummyCert)) ++
  (List.range N).reverse.flatMap
    (fun n => cells.map (fun x => (trPiece b Kc cF x.2.R n x.1, dummyCert)))

theorem mem_expPer {b Kc cF N top : ℕ} {cells : List (QPiece × Cert)} {z : QPiece × Cert}
    (h : z ∈ expPer b Kc cF N top cells) :
    ∃ n ≤ N, ∃ x ∈ cells, z = (trPiece b Kc cF x.2.R n x.1, dummyCert) := by
  simp only [expPer, List.mem_append, List.mem_flatMap, List.mem_reverse, List.mem_range, List.mem_map] at h
  rcases h with ⟨x, hx, rfl⟩ | ⟨n, hn, x, hx, rfl⟩
  · exact ⟨N, le_rfl, x, List.mem_of_mem_drop hx, rfl⟩
  · exact ⟨n, hn.le, x, hx, rfl⟩

/-- The explicit template. -/
def KTmplP.toK (b Kc cF : ℕ) (T : KTmplP) : KTmpl :=
  ⟨T.t1, expPer b Kc cF T.N T.top T.cells ++ T.head, T.tb⟩

/-- The expansion pieces of a template (for the chain, `tend` and mass facts of the data). -/
def KTmplP.expP (b Kc cF : ℕ) (T : KTmplP) : List (QPiece × Cert) := expPer b Kc cF T.N T.top T.cells

theorem KTmplP.toK_pieces (b Kc cF : ℕ) (T : KTmplP) : (T.toK b Kc cF).pieces = T.expP b Kc cF ++ T.head := rfl

/-- `ktmplHead` of a periodic template from the facts about its expansion and head. -/
theorem ktmplHead_toKP_of {D : KBankData} {b Kc cF : ℕ} {T : KTmplP} {j : ℕ} {e0 : ℚ}
    (h1 : 0 < T.t1) (h2 : T.t1 ≤ D.t0) (hc1 : chainOK T.t1 (T.expP b Kc cF) = true)
    (he : tendQ T.t1 (T.expP b Kc cF) = e0) (hc2 : chainOK e0 T.head = true)
    (hs : D.shifts.all (fun x => decide (x.s * j % x.q ≠ 0)) = true)
    (ht : tailOK D j (tendQ e0 T.head) T.tb = true) (hτ : tendQ e0 T.head ≤ D.τ) :
    ktmplHead D j (T.toK b Kc cF) = true := by
  have hp : (T.toK b Kc cF).pieces = T.expP b Kc cF ++ T.head := rfl
  have ht1 : (T.toK b Kc cF).t1 = T.t1 := rfl
  have htb : (T.toK b Kc cF).tb = T.tb := rfl
  simp only [ktmplHead, Bool.and_eq_true, decide_eq_true_eq, hp, ht1, htb, chainOK_append, tendQ_append, hc1,
    he, hc2, hs, ht, Bool.true_and, and_true]
  exact ⟨⟨h1, h2⟩, hτ⟩

/-- The mass of a periodic template is additive. -/
theorem KTmplP.mass_toK (b Kc cF : ℕ) (α0 : ℚ) (T : KTmplP) :
    (T.toK b Kc cF).toQ.mass α0 = α0 * T.t1 + ((T.expP b Kc cF).map (fun x => x.1.mass)).sum +
      (T.head.map (fun x => x.1.mass)).sum := by
  simp only [KTmpl.toQ, QTmpl.mass, KTmplP.toK_pieces, List.map_append, List.sum_append, add_assoc]
  rfl

/-! ### Theorem PC for a bank -/

/- **Theorem PC (content of a bank whose periodic layer is the translate of a table).**  The templates of `D` are
`expansion(N) ++ head` (`KTmplP`); the base cells are sound against the base catalogue `kb`, the translates of `kb`
are valid on the family (T2), prices are covariant (T1, inside `tr`), and the head is a `pieceOK` catalogue piece
list.  `hasScaledContent_of_facts` with `PieceBasic` and `PieceCov` of the expansion from `trPiece_basic` and
`exp_cov_per`, of the head from `head_cov`. -/

/-- Increase a catalogue's finite exceptional-prime threshold. -/
theorem KCatValidFam.mono_threshold {c : ℚ} {hc : 0 < c} {const : ℝ} {depth : ℕ}
    {Q : NodeFamily.Index (altGeom c hc).geometry → ℚ[X]}
    {sh : List Shift} {Q0 Pbad N0 N1 : ℕ} {cat : List KBranch}
    (h : KCatValidFam c hc const depth Q sh Q0 Pbad N0 cat) (hle : N0 ≤ N1) :
    KCatValidFam c hc const depth Q sh Q0 Pbad N1 cat := by
  intro br hb i hi hr p _ hPb hN
  exact h br hb i hi hr p hPb (lt_of_le_of_lt hle hN)

/-- A head piece is sound above its finite scale threshold, without crude clearing. -/
theorem head_cov_large {D : KBankData} (hpar : KParams D)
    {c : ℚ} {hc : 0 < c} {const : ℝ} {depth : ℕ}
    {Q : NodeFamily.Index (altGeom c hc).geometry → ℚ[X]} {N0 : ℕ}
    (hdepth : depth ≤ D.depth)
    (hcat : KCatValidFam c hc const depth Q D.shifts D.Q D.Pbad N0 D.kcat)
    {j : ℕ} {x : QPiece × Cert}
    (hok : pieceOK (D.cat j) D.Q D.α ((j : ℚ) / D.Q) D.depth D.cF D.Pbad x.1 x.2 = true)
    (hRlim : x.2.R * x.1.t ≤ (N0 : ℚ)) :
    PieceCov D c hc const depth Q N0 j x.1 := by
  intro i hi hr0 p k _ hk hN hPb hqN hrd hjs hs ht
  have hpar' := hpar
  obtain ⟨hq2, hqP, -, -, -, -, hα, -, -, -⟩ := hpar'
  have hb := pieceBasic_of_ok hok
  have htpos : (0 : ℝ) < x.1.t := by exact_mod_cast (lt_trans hb.1 hb.2.1)
  have hlim : (x.2.R : ℝ) * x.1.t ≤ N0 := by exact_mod_cast hRlim
  have hNp : (N0 : ℝ) < p := by exact_mod_cast hN
  have hRr : (x.2.R : ℝ) ≤ i.1 := by
    exact le_of_mul_le_mul_right (by linarith) htpos
  have hodd : D.Pbad < p → p % 2 = 1 := by
    intro hPb'
    rcases (Fact.out : p.Prime).eq_two_or_odd with h | h
    · omega
    · exact h
  have hdel : delCount (altGeom c hc) i ≤ D.depth :=
    (show delCount (altGeom c hc) i ≤ depth from hi.1).trans hdepth
  exact piece_sound_large x.1 x.2 hok (by omega) hα
    (fun n => GLE p n ((AltEvenFam c hc const depth Q).Q i))
    hrd hodd (Fact.out : p.Prime).two_le hdel (by exact_mod_cast hRr)
    (branches_of_kcat' hpar hcat hjs i hi hr0 p k hk hN) hs ht

private theorem exists_nat_bound_list (xs : List ℚ) :
    ∃ N : ℕ, ∀ x ∈ xs, x ≤ (N : ℚ) := by
  induction xs with
  | nil => exact ⟨0, fun x hx => by cases hx⟩
  | cons x xs ih =>
    obtain ⟨N, hN⟩ := ih
    obtain ⟨M, hM⟩ := exists_nat_ge x
    refine ⟨max M N, ?_⟩
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hM.trans (by exact_mod_cast (le_max_left M N))
    · exact (hN y hy).trans (by exact_mod_cast (le_max_right M N))

theorem hasScaledContent_of_periodic_control (D : KBankData) (hpar : KParams D)
    (hcls : kclassOK D = true) (hheads : ∀ x ∈ D.tmpls, ktmplHead D x.1 x.2 = true)
    (c : ℚ) (hc : 0 < c) (hcα : c = 2 * D.α)
    (const : ℝ) (depth : ℕ) (Q : NodeFamily.Index (altGeom c hc).geometry → ℚ[X])
    (hdepth : depth ≤ D.depth) (hQ : AltContentControl c hc const depth D.M Q) (B : SmallBudget) (N0 : ℕ)
    {b a Kc Ω : ℕ} (hab : D.α * b = a) {kb : List KBranch} (tr : Transl b a Kc Ω kb)
    (Tm : List (ℕ × KTmplP)) (hTm : D.tmpls = Tm.map (fun x => (x.1, x.2.toK b Kc D.cF)))
    (hcellb : ∀ x ∈ Tm, ∀ y ∈ x.2.cells, PieceBasic y.1 ∧ 0 ≤ y.2.R ∧ 1 / y.1.s + (x.2.N : ℚ) * b ≤ Ω)
    (hcells : ∀ x ∈ Tm, ∀ y ∈ x.2.cells,
      BaseSound D (kb.map (KBranch.compile D.tS (D.bS x.1) D.cS)) x.1 y.1 y.2.R)
    (hhead : ∀ x ∈ Tm, ∀ y ∈ x.2.head,
      pieceOK (D.cat x.1) D.Q D.α ((x.1 : ℚ) / D.Q) D.depth D.cF D.Pbad y.1 y.2 = true)
    (hcat : KCatValidFam c hc const depth Q D.shifts D.Q D.Pbad N0 D.kcat)
    (hvalid : ∀ n, KCatValidFam c hc const depth Q D.shifts D.Q D.Pbad N0 (kb.map (tr.ρ n)))
    (hpre : PreValidFam c hc const depth Q D.M B D.t0 D.α0b) :
    HasScaledContent (AltEvenFam c hc const depth Q) (altGeom c hc).scale (D.Λ : ℝ) := by
  classical
  let limits : List ℚ := Tm.flatMap (fun x =>
    (x.2.head ++ x.2.cells).map (fun y => y.2.R * y.1.t))
  obtain ⟨N, hN⟩ := exists_nat_bound_list limits
  let N1 := max N0 N
  have hN0 : N0 ≤ N1 := le_max_left _ _
  have hlim : ∀ x ∈ Tm, ∀ y ∈ x.2.head ++ x.2.cells,
      y.2.R * y.1.t ≤ (N1 : ℚ) := by
    intro x hx y hy
    have hm : y.2.R * y.1.t ∈ limits :=
      List.mem_flatMap.mpr ⟨x, hx, List.mem_map.mpr ⟨y, hy, rfl⟩⟩
    exact (hN _ hm).trans (by exact_mod_cast (le_max_right N0 N))
  have hcat1 := hcat.mono_threshold hN0
  have hvalid1 : ∀ n, KCatValidFam c hc const depth Q D.shifts D.Q D.Pbad N1 (kb.map (tr.ρ n)) :=
    fun n => (hvalid n).mono_threshold hN0
  refine hasScaledContent_of_facts_control D hpar hcls hheads c hc hcα const depth Q hQ B N1
    ?_ ?_ hcat1 hpre
  · intro x hx z hz
    rw [hTm] at hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    simp only [KTmplP.toK, List.mem_append] at hz
    rcases hz with hz | hz
    · obtain ⟨n, -, w, hw, rfl⟩ := mem_expPer hz
      exact trPiece_basic (hcellb y hy w hw).1 b Kc D.cF w.2.R n
    · exact pieceBasic_of_ok (hhead y hy z hz)
  · intro x hx z hz
    rw [hTm] at hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    simp only [KTmplP.toK, List.mem_append] at hz
    rcases hz with hz | hz
    · obtain ⟨n, hn, w, hw, rfl⟩ := mem_expPer hz
      obtain ⟨hw1, hw2, hw3⟩ := hcellb y hy w hw
      have hnN : (n : ℚ) ≤ y.2.N := by exact_mod_cast hn
      have hb0 : (0 : ℚ) ≤ b := Nat.cast_nonneg _
      exact exp_cov_per_large hpar hdepth hab tr hvalid1 hw1 (hcells y hy w hw)
        (hlim y hy w (List.mem_append.mpr (Or.inr hw))) n
        (by linarith [mul_le_mul_of_nonneg_right hnN hb0, hw3])
    · exact head_cov_large hpar hdepth hcat1 (hhead y hy z hz)
        (hlim y hy z (List.mem_append.mpr (Or.inl hz)))

theorem hasScaledContent_of_periodic (D : KBankData) (hpar : KParams D)
    (hcls : kclassOK D = true) (hheads : ∀ x ∈ D.tmpls, ktmplHead D x.1 x.2 = true)
    (c : ℚ) (hc : 0 < c) (hcα : c = 2 * D.α)
    (const : ℝ) (depth : ℕ) (Q : NodeFamily.Index (altGeom c hc).geometry → ℚ[X])
    (hdepth : depth ≤ D.depth) (hQ : AltQ c hc D.cF Q) (B : SmallBudget) (N0 : ℕ)
    {b a Kc Ω : ℕ} (hab : D.α * b = a) {kb : List KBranch} (tr : Transl b a Kc Ω kb)
    (Tm : List (ℕ × KTmplP)) (hTm : D.tmpls = Tm.map (fun x => (x.1, x.2.toK b Kc D.cF)))
    (hcellb : ∀ x ∈ Tm, ∀ y ∈ x.2.cells, PieceBasic y.1 ∧ 0 ≤ y.2.R ∧ 1 / y.1.s + (x.2.N : ℚ) * b ≤ Ω)
    (hcells : ∀ x ∈ Tm, ∀ y ∈ x.2.cells,
      BaseSound D (kb.map (KBranch.compile D.tS (D.bS x.1) D.cS)) x.1 y.1 y.2.R)
    (hhead : ∀ x ∈ Tm, ∀ y ∈ x.2.head,
      pieceOK (D.cat x.1) D.Q D.α ((x.1 : ℚ) / D.Q) D.depth D.cF D.Pbad y.1 y.2 = true)
    (hcat : KCatValidFam c hc const depth Q D.shifts D.Q D.Pbad N0 D.kcat)
    (hvalid : ∀ n, KCatValidFam c hc const depth Q D.shifts D.Q D.Pbad N0 (kb.map (tr.ρ n)))
    (hpre : PreValidFam c hc const depth Q D.M B D.t0 D.α0b) :
    HasScaledContent (AltEvenFam c hc const depth Q) (altGeom c hc).scale (D.Λ : ℝ) := by
  haveI : NeZero D.M := ⟨by have := hpar.2.2.1; omega⟩
  exact hasScaledContent_of_periodic_control D hpar hcls hheads c hc hcα const depth Q hdepth
    (AltContentControl.ofAltQ c hc D.cF const depth Q D.M hQ) B N0 hab tr Tm hTm hcellb hcells hhead
    hcat hvalid hpre

/-! ### Boolean cell check and the `M = Q = 2` class sum -/

theorem pieceOK_one_le_R {cat : List Branch} {q : ℕ} {α κ : ℚ} {depth cF Pbad : ℕ} {P : QPiece} {c : Cert}
    (h : pieceOK cat q α κ depth cF Pbad P c = true) : 1 ≤ c.R := by
  unfold pieceOK at h
  rcases hb : nth cat c.bi with _ | br <;> simp only [hb, reduceCtorEq, Bool.false_eq_true] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hR3⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h
  exact hR3

/-- The check of one base cell: `pieceOK` against the compiled base catalogue and the ambient range of the strips. -/
def cellOKb (D : KBankData) (kb : List KBranch) (j N b Ω : ℕ) (y : QPiece × Cert) : Bool :=
  pieceOK (kb.map (KBranch.compile D.tS (D.bS j) D.cS)) D.Q D.α ((j : ℚ) / D.Q) D.depth D.cF D.Pbad y.1 y.2 &&
    decide (1 / y.1.s + (N : ℚ) * b ≤ Ω)

theorem cellOKb_facts {D : KBankData} (hq : 1 ≤ D.Q) (hα : 0 ≤ D.α) {kb : List KBranch} {j N b Ω : ℕ}
    {y : QPiece × Cert} (h : cellOKb D kb j N b Ω y = true) :
    (PieceBasic y.1 ∧ 0 ≤ y.2.R ∧ 1 / y.1.s + (N : ℚ) * b ≤ Ω) ∧
      BaseSound D (kb.map (KBranch.compile D.tS (D.bS j) D.cS)) j y.1 y.2.R := by
  simp only [cellOKb, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hok, hΩ⟩ := h
  have h1 := pieceOK_one_le_R hok
  exact ⟨⟨pieceBasic_of_ok hok, by linarith, hΩ⟩, baseSound_of_pieceOK hq hα hok⟩

/-- **Theorem PC with the Boolean cell check** (`cellOKb`). -/
theorem hasScaledContent_of_periodic_ok (D : KBankData) (hpar : KParams D)
    (hcls : kclassOK D = true) (hheads : ∀ x ∈ D.tmpls, ktmplHead D x.1 x.2 = true)
    (c : ℚ) (hc : 0 < c) (hcα : c = 2 * D.α)
    (const : ℝ) (depth : ℕ) (Q : NodeFamily.Index (altGeom c hc).geometry → ℚ[X])
    (hdepth : depth ≤ D.depth) (hQ : AltQ c hc D.cF Q) (B : SmallBudget) (N0 : ℕ)
    {b a Kc Ω : ℕ} (hab : D.α * b = a) {kb : List KBranch} (tr : Transl b a Kc Ω kb)
    (Tm : List (ℕ × KTmplP)) (hTm : D.tmpls = Tm.map (fun x => (x.1, x.2.toK b Kc D.cF)))
    (hcells : ∀ x ∈ Tm, ∀ y ∈ x.2.cells, cellOKb D kb x.1 x.2.N b Ω y = true)
    (hhead : ∀ x ∈ Tm, ∀ y ∈ x.2.head,
      pieceOK (D.cat x.1) D.Q D.α ((x.1 : ℚ) / D.Q) D.depth D.cF D.Pbad y.1 y.2 = true)
    (hcat : KCatValidFam c hc const depth Q D.shifts D.Q D.Pbad N0 D.kcat)
    (hvalid : ∀ n, KCatValidFam c hc const depth Q D.shifts D.Q D.Pbad N0 (kb.map (tr.ρ n)))
    (hpre : PreValidFam c hc const depth Q D.M B D.t0 D.α0b) :
    HasScaledContent (AltEvenFam c hc const depth Q) (altGeom c hc).scale (D.Λ : ℝ) := by
  have hpar' := hpar
  obtain ⟨hq2, -, -, -, -, -, hα, -, -, -⟩ := hpar'
  exact hasScaledContent_of_periodic D hpar hcls hheads c hc hcα const depth Q hdepth hQ B N0 hab tr Tm hTm
    (fun x hx y hy => (cellOKb_facts (by omega) hα (hcells x hx y hy)).1)
    (fun x hx y hy => (cellOKb_facts (by omega) hα (hcells x hx y hy)).2) hhead hcat hvalid hpre

/-- `kclassOK` for a bank with `M = Q = 2` (the single unit class `1`) and the member `a = 1`: the mass of the template
of the root class `1` is `Λ`. -/
theorem kclassOK_two (D : KBankData) (hM : D.M = 2) (hQ : D.Q = 2) (ha : D.a = 1)
    {T1 : KTmpl} (h1 : findK 1 D.tmpls = some T1) (hm : T1.toQ.mass D.α0 = D.Λ) : kclassOK D = true := by
  have hu : ∀ f : ℕ → ℚ, unitSum 2 f 2 = f 1 := fun f => by simp [unitSum]
  have hall : ∀ P : ℕ → Bool, unitAll 2 P 2 = P 1 := fun P => by simp [unitAll]
  have hc : unitCount 2 2 = 1 := by decide
  have j1 : jOf 2 1 1 = some 1 := by decide
  unfold kclassOK
  rw [hM, hQ]
  simp only [hall, hu, hc, ha, j1, h1, kclassMass, hQ, Option.isSome_some, Bool.true_and, decide_eq_true_eq]
  simp [hm]

end CatalanCore.Uniform.Content.BankShared.KTerm
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.piece_sound_large
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.trPiece_basic
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.exp_cov_per
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.ktmplHead_toKP_of
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.KTmplP.mass_toK
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.hasScaledContent_of_periodic
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.cellOKb_facts
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.hasScaledContent_of_periodic_ok
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.kclassOK_two

#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.hasScaledContent_of_periodic_control
