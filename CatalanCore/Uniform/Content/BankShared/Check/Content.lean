module

public import CatalanCore.Uniform.Content.BankShared.Check.Bank
public import CatalanCore.Uniform.Content.BankShared.AltCrude
public import CatalanCore.Uniform.Content.BankShared.BudgetedOne
public import CatalanCore.Uniform.Content.BankShared.Budgeted
public import CatalanCore.Uniform.Content.BankShared.TwoTerm.Class

@[expose] public section
set_option Elab.async false

/-! # Theorem D: acceptance of the bank check gives the scaled content (lane C1L; C1/PAPER.md §5)

* `altContent_of_bounds`: the content route of `thirds_content_of_bounds` for every alternating geometry `altGeom c`
  (`0 < c ≤ 1`, even scales): the price is the optimal clearing exponent `lpOptA`, so `gle` is automatic and the
  obligations `tail`, `pre`, `cov` ask for SOME `n` with `GLE p n (Q i)` below the template line;
* `CatValid`: the branch theorems of a catalogue (one statement per branch, for every admissible member, every
  prime `p > P_bad` with `q(r+2m) < p²` and every root datum `q k = j p + o`);
* `PreValid`: the prefix bound `n ≤ α0b r + B.X r p` for `p ≤ t0 r`;
* **Theorem D** `hasScaledContent_of_check`: `check D = true`, the catalogue and prefix statements for the member
  `a` give `HasScaledContent (AltEven c Fr depth) scale Λ_fin` (finite form, `c = 2α`). -/

namespace CatalanCore.Uniform.Content.BankShared.Check
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.BankShared
  CatalanCore.Uniform.Content.SmallPrimes CatalanCore.Uniform.Content.Member CatalanCore.Arith.Hybrid
  CatalanCore.Basic Filter Finset

/-- The alternating family at even scales. -/
noncomputable abbrev AltEven (c : ℚ) (hc : 0 < c) (Fr : Frame) (depth : ℕ) :=
  ((altGeom c hc).family Fr depth).restrictAdm (fun i => i.1 % 2 = 0)

/-- The even-scale family above the scale `R0`. -/
noncomputable abbrev AltR (c : ℚ) (hc : 0 < c) (Fr : Frame) (depth R0 : ℕ) :=
  (AltEven c hc Fr depth).restrictAdm (fun i => R0 ≤ i.1)

open Classical in
/-- The optimal clearing exponent of a member at a prime (`0` at non-primes). -/
noncomputable def lpOptA (c : ℚ) (hc : 0 < c) (Fr : Frame) (depth : ℕ) (i : (AltEven c hc Fr depth).ι)
    (p : ℕ) : ℕ :=
  if hp : p.Prime then
    haveI : Fact p.Prime := ⟨hp⟩
    if h : ∃ n, GLE p n ((AltEven c hc Fr depth).Q i) then Nat.find h else 0
  else 0

theorem lpOptA_gle (c : ℚ) (hc : 0 < c) (Fr : Frame) (depth : ℕ) (i : (AltEven c hc Fr depth).ι)
    (p : ℕ) [hp : Fact p.Prime] (h : ∃ n, GLE p n ((AltEven c hc Fr depth).Q i)) :
    GLE p (lpOptA c hc Fr depth i p) ((AltEven c hc Fr depth).Q i) := by
  classical
  unfold lpOptA
  rw [dif_pos hp.out, dif_pos h]
  exact Nat.find_spec h

theorem lpOptA_le (c : ℚ) (hc : 0 < c) (Fr : Frame) (depth : ℕ) (i : (AltEven c hc Fr depth).ι)
    (p : ℕ) [hp : Fact p.Prime] {n : ℕ} (h : GLE p n ((AltEven c hc Fr depth).Q i)) :
    lpOptA c hc Fr depth i p ≤ n := by
  classical
  unfold lpOptA
  rw [dif_pos hp.out, dif_pos ⟨n, h⟩]
  exact Nat.find_min' _ h

/-- **The generic content route** (the statement of `thirds_content_of_bounds` for every `altGeom c`). -/
theorem altContent_of_bounds (c : ℚ) (hc : 0 < c) (hc1 : c ≤ 1) (Fr : Frame) (depth R0 : ℕ)
    (M : ℕ) [NeZero M] (Lam : ℝ)
    (B : SmallBudget) (tmpl : ℝ → ZMod M → Template) (τ : ℝ)
    (hmass : ∀ ε : ℝ, 0 < ε → contentConstant M (tmpl ε) ≤ Lam + ε)
    (tend_le : ∀ ε : ℝ, 0 < ε → ∀ c' : ZMod M, IsUnit c' → (tmpl ε c').tend ≤ τ)
    (tail : ∀ ε : ℝ, 0 < ε → ∀ i, (AltR c hc Fr depth R0).Adm i → ∀ c' : ZMod M, IsUnit c' →
      ∀ p : ℕ, p.Prime → (p : ZMod M) = c' → ⌊(tmpl ε c').tend * (altGeom c hc).scale i⌋₊ < p →
        ∀ [Fact p.Prime], GLE p 0 ((AltR c hc Fr depth R0).Q i))
    (pre : ∀ ε : ℝ, 0 < ε → ∀ i, (AltR c hc Fr depth R0).Adm i → ∀ c' : ZMod M, IsUnit c' →
      ∀ p : ℕ, p ≤ ⌊(tmpl ε c').t1 * (altGeom c hc).scale i⌋₊ → p.Prime → (p : ZMod M) = c' →
        ∀ [Fact p.Prime], ∃ n : ℕ, GLE p n ((AltR c hc Fr depth R0).Q i) ∧
          (n : ℝ) ≤ (tmpl ε c').α0 * (altGeom c hc).scale i + B.X ((altGeom c hc).scale i) p)
    (cov : ∀ ε : ℝ, 0 < ε → ∀ i, (AltR c hc Fr depth R0).Adm i → ∀ c' : ZMod M, IsUnit c' →
      ∀ P ∈ (tmpl ε c').l, ∀ p : ℕ, ⌊P.s * (altGeom c hc).scale i⌋₊ < p →
        p ≤ ⌊P.t * (altGeom c hc).scale i⌋₊ → p.Prime → (p : ZMod M) = c' →
        ∀ [Fact p.Prime], ∃ n : ℕ, GLE p n ((AltR c hc Fr depth R0).Q i) ∧
          (n : ℝ) ≤ P.α * (altGeom c hc).scale i + P.β * p + P.C) :
    HasScaledContent (AltR c hc Fr depth R0) (altGeom c hc).scale Lam := by
  classical
  let sc := (altGeom c hc).scale
  let price : (AltR c hc Fr depth R0).ι → ℕ → ℕ := fun i p =>
    if p ∣ M then Ecrude (cFr Fr) i.1 p else lpOptA c hc Fr depth i p
  have hpr : ∀ i p, ¬ p ∣ M → price i p = lpOptA c hc Fr depth i p := fun i p h => by
    simp [price, h]
  have hnd : ∀ {p : ℕ} {c' : ZMod M}, p.Prime → IsUnit c' → (p : ZMod M) = c' → ¬ p ∣ M := by
    intro p c' hp hc' hpc
    rw [← ZMod.isUnit_prime_iff_not_dvd hp, hpc]; exact hc'
  have hlcut : ∀ i, (AltR c hc Fr depth R0).Adm i → ∀ ε : ℝ, 0 < ε → ∀ c' : ZMod M, IsUnit c' →
      ⌊(tmpl ε c').tend * sc i⌋₊ ≤ ⌊τ * sc i⌋₊ := by
    intro i _ ε hε c' hc'
    exact Nat.floor_le_floor (mul_le_mul_of_nonneg_right (tend_le ε hε c' hc') (Nat.cast_nonneg _))
  refine hasScaledContent_budgeted_lim (AltR c hc Fr depth R0) sc M
    (fun i => NodeFamily.family_degree Fr (altGeom c hc).geometry depth i) price
    (fun i => max (⌊τ * sc i⌋₊ + 1) (M + 1)) ?_ ?_ B Lam tmpl hmass ?_ ?_ ?_ ?_
    (exc_of_Ecrude (AltR c hc Fr depth R0) sc M price (cFr Fr) ?_)
  · intro i hi p hpF
    by_cases h : p ∣ M
    · simp only [price, h, if_true]
      exact altGeom_gle_Ecrude c hc hc1 Fr depth i hi.1.2 p
    · simp only [price, h, if_false]
      exact lpOptA_gle c hc Fr depth i p ⟨_, altGeom_gle_Ecrude c hc hc1 Fr depth i hi.1.2 p⟩
  · intro i hi p hp hcut
    have hM : ¬ p ∣ M := fun h => by
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) h
      have := (le_max_right (⌊τ * sc i⌋₊ + 1) (M + 1)).trans hcut
      omega
    have hunit : IsUnit (p : ZMod M) := (ZMod.isUnit_prime_iff_not_dvd hp).2 hM
    haveI : Fact p.Prime := ⟨hp⟩
    have hlt : ⌊(tmpl 1 (p : ZMod M)).tend * sc i⌋₊ < p := by
      have := hlcut i hi 1 one_pos _ hunit
      have := (le_max_left (⌊τ * sc i⌋₊ + 1) (M + 1)).trans hcut
      omega
    rw [hpr i p hM]
    exact Nat.le_zero.1 (lpOptA_le c hc Fr depth i p (tail 1 one_pos i hi _ hunit p hp rfl hlt))
  · intro ε hε i hi c' hc' p hp hpc hlt
    haveI : Fact p.Prime := ⟨hp⟩
    rw [hpr i p (hnd hp hc' hpc)]
    exact Nat.le_zero.1 (lpOptA_le c hc Fr depth i p (tail ε hε i hi c' hc' p hp hpc hlt))
  · intro ε hε i hi c' hc'
    have := hlcut i hi ε hε c' hc'
    exact lt_of_le_of_lt this (lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _))
  · intro ε hε i hi c' hc' p h1 hp hpc
    haveI : Fact p.Prime := ⟨hp⟩
    rw [hpr i p (hnd hp hc' hpc)]
    obtain ⟨n, hn, hb⟩ := pre ε hε i hi c' hc' p h1 hp hpc
    exact (Nat.cast_le.2 (lpOptA_le c hc Fr depth i p hn)).trans hb
  · intro ε hε i hi c' hc' P hP p h1 h2 hp hpc
    haveI : Fact p.Prime := ⟨hp⟩
    show (price i p : ℝ) ≤ _
    rw [hpr i p (hnd hp hc' hpc)]
    obtain ⟨n, hn, hb⟩ := cov ε hε i hi c' hc' P hP p h1 h2 hp hpc
    exact (Nat.cast_le.2 (lpOptA_le c hc Fr depth i p hn)).trans hb
  · intro i hi p hp
    have hd := Nat.dvd_of_mem_primeFactors hp
    simp only [price, hd, if_true]
    exact le_rfl

/-- **Lift from large scales.**  Content on the members of scale `≥ R0` gives content on the whole family: the
small scales only need some clearing denominator (the product of the coefficient denominators). -/
theorem hasScaledContent_lift (Fam : PolyFamily) (sc : Fam.ι → ℕ) (Λ : ℝ) (R0 : ℕ)
    (hnat : ∀ n, (Fam.Q n).natDegree ≤ Fam.deg n)
    (h : HasScaledContent (Fam.restrictAdm (fun n => R0 ≤ sc n)) sc Λ) : HasScaledContent Fam sc Λ := by
  classical
  obtain ⟨den, hpos, hint, hlog⟩ := h
  let cden : Fam.ι → ℕ := fun n =>
    ∏ k ∈ Finset.range ((Fam.Q n).natDegree + 1), ((Fam.Q n).coeff k).den
  have hcpos : ∀ n, 0 < cden n := fun n => Finset.prod_pos (fun k _ => ((Fam.Q n).coeff k).den_pos)
  have hcclear : ∀ n i, ∃ z : ℤ, ((cden n : ℕ) : ℚ) * (Fam.Q n).coeff i = z := by
    intro n i
    by_cases hi : i ∈ Finset.range ((Fam.Q n).natDegree + 1)
    · obtain ⟨e, he⟩ := Finset.dvd_prod_of_mem (fun k => ((Fam.Q n).coeff k).den) hi
      refine ⟨(e : ℤ) * ((Fam.Q n).coeff i).num, ?_⟩
      have h1 := Rat.den_mul_eq_num ((Fam.Q n).coeff i)
      have he' : ((cden n : ℕ) : ℚ) = (((Fam.Q n).coeff i).den : ℚ) * (e : ℚ) := by
        rw [show cden n = _ from he]; push_cast; ring
      rw [he']; push_cast
      linear_combination (e : ℚ) * h1
    · have hlt : (Fam.Q n).natDegree < i := by
        rw [Finset.mem_range] at hi; omega
      exact ⟨0, by rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt]; simp⟩
  refine ⟨fun n => if R0 ≤ sc n then den n else cden n, ?_, ?_, ?_⟩
  · intro n
    dsimp only
    split_ifs
    · exact hpos n
    · exact hcpos n
  · intro n hn p q hq
    dsimp only
    split_ifs with hR
    · exact hint n ⟨hn, hR⟩ p q hq
    · exact int_clear' (Fam.Q n) (Fam.deg n) (hnat n) (cden n) (hcclear n) p q hq
  · intro ε hε
    obtain ⟨R1, hR1⟩ := hlog ε hε
    refine ⟨max R0 R1, fun n hn hR => ?_⟩
    have h0 : R0 ≤ sc n := (le_max_left _ _).trans hR
    simp only [if_pos h0]
    exact hR1 n ⟨hn, h0⟩ ((le_max_right _ _).trans hR)

/-! ### The branch and prefix statements consumed by Theorem D -/

/-- **The branch catalogue is valid** for the member frame `Fr` with pole offset `o`.  `P_bad` is the explicit
prime bound used by the check (it enters the constants); `N0` is a further bound that is never evaluated (for example
C2L's choice-built `NFr` of the rank layer): Theorem D only uses the branches at scales so large that every prime of
every piece exceeds it. -/
def CatValid (c : ℚ) (hc : 0 < c) (Fr : Frame) (depth q o Pbad N0 : ℕ) (cat : List Branch) : Prop :=
  ∀ b ∈ cat, ∀ i : (AltEven c hc Fr depth).ι, (AltEven c hc Fr depth).Adm i → 0 < i.1 →
    ∀ (p : ℕ) [Fact p.Prime], Pbad < p → N0 < p →
    q * (i.1 + 2 * (altGeom c hc).borderSize i.1) < p * p →
    ∀ j k : ℕ, q * k = j * p + o → 0 < j → j < q → 0 < k → k < p →
    (∀ cd ∈ b.conds, cd.Holds i.1 p ((altGeom c hc).borderSize i.1) k) →
    ∃ n, GLE p n ((AltEven c hc Fr depth).Q i) ∧
      n ≤ b.τ.evalN i.1 p ((altGeom c hc).borderSize i.1) k + b.debit * delCount (altGeom c hc) i

/-- **The prefix bound** on `p ≤ t0 r` (`pre_gle` of the T layer). -/
def PreValid (c : ℚ) (hc : 0 < c) (Fr : Frame) (depth M : ℕ) (B : SmallBudget) (t0 α0b : ℚ) : Prop :=
  ∀ i : (AltEven c hc Fr depth).ι, (AltEven c hc Fr depth).Adm i → ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ M →
    p ≤ ⌊(t0 : ℝ) * i.1⌋₊ →
    ∃ n, GLE p n ((AltEven c hc Fr depth).Q i) ∧ (n : ℝ) ≤ (α0b : ℝ) * i.1 + B.X i.1 p

/-! ### Unit classes and the class sums -/

theorem unitSum_eq (M : ℕ) (f : ℕ → ℚ) : ∀ n : ℕ,
    ((unitSum M f n : ℚ) : ℝ) = ∑ x ∈ Finset.range n, if M.Coprime x then ((f x : ℚ) : ℝ) else 0
  | 0 => by simp [unitSum]
  | n + 1 => by
    rw [Finset.sum_range_succ, ← unitSum_eq M f n, unitSum]
    by_cases h : Nat.gcd M n = 1
    · have h' : M.Coprime n := h
      simp [h, h']
    · have h' : ¬ M.Coprime n := h
      simp [h, h']

theorem unitCount_eq (M : ℕ) : ∀ n : ℕ,
    unitCount M n = ((Finset.range n).filter (fun x => M.Coprime x)).card
  | 0 => by simp [unitCount]
  | n + 1 => by
    rw [Finset.range_add_one, Finset.filter_insert, unitCount, unitCount_eq M n]
    by_cases h : Nat.gcd M n = 1
    · have h' : M.Coprime n := h
      rw [if_pos h, if_pos h', Finset.card_insert_of_notMem]
      simp
    · have h' : ¬ M.Coprime n := h
      rw [if_neg h, if_neg h']; rfl

theorem unitAll_spec (M : ℕ) (P : ℕ → Bool) : ∀ n : ℕ, unitAll M P n = true →
    ∀ x < n, M.Coprime x → P x = true
  | 0, _, x, hx, _ => absurd hx (Nat.not_lt_zero x)
  | n + 1, h, x, hx, hc => by
    simp only [unitAll, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
      at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hx with hx | hx
    · exact unitAll_spec M P n h.1 x hx hc
    · subst hx
      rcases h.2 with h2 | h2
      · exact absurd hc h2
      · exact h2

theorem sum_unitClasses (M : ℕ) [NeZero M] (F : ℕ → ℝ) :
    ∑ c ∈ unitClasses M, F c.val = ∑ x ∈ Finset.range M, if M.Coprime x then F x else 0 := by
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij' (fun c => c.val) (fun x => (x : ZMod M)) ?_ ?_ ?_ ?_ ?_
  · intro c hc
    rw [mem_unitClasses] at hc
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨ZMod.val_lt c, ?_⟩
    have : IsUnit ((c.val : ℕ) : ZMod M) := by rwa [ZMod.natCast_zmod_val]
    exact ((ZMod.isUnit_iff_coprime c.val M).1 this).symm
  · intro x hx
    rw [Finset.mem_filter, Finset.mem_range] at hx
    rw [mem_unitClasses]
    exact (ZMod.isUnit_iff_coprime x M).2 hx.2.symm
  · intro c _; simp only [ZMod.natCast_zmod_val]
  · intro x hx
    rw [Finset.mem_filter, Finset.mem_range] at hx
    exact ZMod.val_cast_of_lt hx.1
  · intro c _; rfl

/-! ### The class map at a prime -/

/-- From the class `c'` of the prime `p`: the root datum `q k = j p + o`. -/
theorem root_datum {q a M p j c : ℕ} (hq : 2 ≤ q) (hqM : M % q = 0) (ha0 : 0 < a) (haq : a < q)
    (hj : jOf q a c = some j) (hpc : p % M = c) :
    j < q ∧ 0 < j ∧ q * ((j * p) / q + 1) = j * p + (q - a) := by
  obtain ⟨hjq, hjc⟩ := jOf_spec hj
  have hpq : p % q = c % q := by
    rw [← hpc]; exact (Nat.mod_mod_of_dvd p (Nat.dvd_of_mod_eq_zero hqM)).symm
  have hmod : (j * p) % q = a := by
    rw [Nat.mul_mod, hpq, ← Nat.mul_mod, hjc, Nat.mod_eq_of_lt haq]
  refine ⟨hjq, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos j with h0 | h0
    · subst h0; simp at hmod; omega
    · exact h0
  · have h := Nat.div_add_mod (j * p) q
    rw [mul_add, mul_one]
    omega

section TheoremD

variable {D : BankData}

/-- The real rounding facts of a member at a prime. -/
theorem round_of (c : ℚ) (hc : 0 < c) (hcα : c = 2 * D.α) {r p j k a : ℕ} (hr : r % 2 = 0)
    (hq : 2 ≤ D.q) (ha0 : 0 < a) (haq : a < D.q) (hk : D.q * k = j * p + (D.q - a)) :
    Cond.Round D.q r p ((altGeom c hc).borderSize r) k D.α ((j : ℚ) / D.q) := by
  obtain ⟨h1, h2⟩ := TwoTerm.altGeom_border c hc hr
  have hc' : (c : ℝ) = 2 * D.α := by exact_mod_cast hcα
  have h1' : ((c * r - 1 : ℚ) : ℝ) ≤ ((2 * ((altGeom c hc).borderSize r : ℚ) : ℚ) : ℝ) := by
    exact_mod_cast h1
  have h2' : ((2 * ((altGeom c hc).borderSize r : ℚ) : ℚ) : ℝ) < ((c * r + 1 : ℚ) : ℝ) := by
    exact_mod_cast h2
  push_cast at h1' h2'
  rw [hc'] at h1' h2'
  have hq' : (0 : ℝ) < D.q := by exact_mod_cast (show 0 < D.q by omega)
  have hk' : ((D.q * k : ℕ) : ℝ) = ((j * p + (D.q - a) : ℕ) : ℝ) := by rw [hk]
  push_cast [Nat.cast_sub haq.le] at hk'
  have hka : (k : ℝ) - ((j : ℚ) / D.q : ℚ) * p = ((D.q : ℝ) - a) / D.q := by
    push_cast; field_simp; linarith
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha0
  have ha2 : (a : ℝ) + 1 ≤ D.q := by exact_mod_cast haq
  refine ⟨by linarith, by linarith, ?_, ?_⟩
  · rw [hka, div_le_div_iff_of_pos_right hq']; linarith
  · rw [hka, sub_div, div_self hq'.ne']
    have : (1 : ℝ) / D.q ≤ a / D.q := div_le_div_of_nonneg_right ha1 hq'.le
    linarith

/-! ### The scale threshold -/

theorem pieceOK_lt {cat : List Branch} {q : ℕ} {α κ : ℚ} {depth cF Pbad : ℕ} {P : QPiece} {c : Cert}
    (h : pieceOK cat q α κ depth cF Pbad P c = true) : 0 < P.s ∧ P.s < P.t := by
  unfold pieceOK at h
  rcases hb : nth cat c.bi with _ | br <;> simp only [hb, reduceCtorEq, Bool.false_eq_true] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1.1.1.1.1.1.1.1.1.1.1, h.1.1.1.1.1.1.1.1.1.1.1.1.1.2⟩

theorem chain_ge {D : BankData} {κ : ℚ} : ∀ (l : List (QPiece × Cert)) (s0 : ℚ), chainOK s0 l = true →
    (∀ x ∈ l, pieceOK D.cat D.q D.α κ D.depth D.cF D.Pbad x.1 x.2 = true) →
      (∀ x ∈ l, s0 ≤ x.1.s) ∧ s0 ≤ tendQ s0 l
  | [], _, _, _ => ⟨fun _ h => absurd h List.not_mem_nil, le_refl _⟩
  | x :: l, s0, h, hp => by
    simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq] at h
    have hx := pieceOK_lt (hp x List.mem_cons_self)
    obtain ⟨ih1, ih2⟩ := chain_ge l x.1.t h.2 (fun y hy => hp y (List.mem_cons_of_mem _ hy))
    refine ⟨fun y hy => ?_, ?_⟩
    · rcases List.mem_cons.1 hy with rfl | hy
      · exact h.1.ge
      · have := ih1 y hy; linarith [h.1, hx.2]
    · show s0 ≤ tendQ x.1.t l
      linarith [h.1, hx.2]

theorem tlo_list : ∀ l : List (ℕ × QTmpl), (∀ x ∈ l, 0 < x.2.t1) →
    ∃ tlo : ℚ, 0 < tlo ∧ ∀ x ∈ l, tlo ≤ x.2.t1
  | [], _ => ⟨1, one_pos, fun _ h => absurd h List.not_mem_nil⟩
  | x :: l, h => by
    obtain ⟨t, ht0, ht⟩ := tlo_list l (fun y hy => h y (List.mem_cons_of_mem _ hy))
    refine ⟨min x.2.t1 t, lt_min (h x List.mem_cons_self) ht0, fun y hy => ?_⟩
    rcases List.mem_cons.1 hy with rfl | hy
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (ht y hy)

theorem tlo_exists {D : BankData} (hD : check D = true) :
    ∃ tlo : ℚ, 0 < tlo ∧ ∀ j T, findT j D.tmpls = some T → tlo ≤ T.t1 := by
  obtain ⟨t, ht0, ht⟩ := tlo_list D.tmpls (fun x hx => by
    have h := hD
    simp only [check, Bool.and_eq_true, List.all_eq_true] at h
    have := h.1.2 x hx
    simp only [tmplOK, tmplHead, Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1.1.1.1.1.1.1)
  exact ⟨t, ht0, fun j T h => ht (j, T) (findT_mem j D.tmpls h)⟩

set_option maxHeartbeats 1000000 in
/-- **Theorem D** (finite form). -/
theorem hasScaledContent_of_check (D : BankData) (hD : check D = true)
    (c : ℚ) (hc : 0 < c) (hc1 : c ≤ 1) (hcα : c = 2 * D.α)
    (Fr : Frame) (depth : ℕ) (hdepth : depth ≤ D.depth) (hcF : cFr Fr ≤ D.cF)
    (a : ℕ) (ha : a ∈ D.members) (B : SmallBudget)
    (N0 : ℕ) (hcat : CatValid c hc Fr depth D.q (D.q - a) D.Pbad N0 D.cat)
    (hpre : PreValid c hc Fr depth D.M B D.t0 D.α0b) :
    HasScaledContent (AltEven c hc Fr depth) (altGeom c hc).scale (D.Λ : ℝ) := by
  classical
  obtain ⟨hq2, hqP, hM0, hMq, hα, hα0b, hα0⟩ := check_params hD
  haveI : NeZero D.M := ⟨by omega⟩
  have hmem := check_member hD ha
  simp only [classOK, Bool.and_eq_true, decide_eq_true_eq] at hmem
  obtain ⟨⟨⟨⟨ha0, haq⟩, -⟩, hcls⟩, hsum⟩ := hmem
  -- the template of a unit class
  have hclass : ∀ c' : ZMod D.M, IsUnit c' →
      ∃ j T, jOf D.q a c'.val = some j ∧ findT j D.tmpls = some T := by
    intro c' hc'
    have hcop : D.M.Coprime c'.val := by
      have : IsUnit ((c'.val : ℕ) : ZMod D.M) := by rwa [ZMod.natCast_zmod_val]
      exact ((ZMod.isUnit_iff_coprime c'.val D.M).1 this).symm
    have := unitAll_spec D.M _ D.M hcls c'.val (ZMod.val_lt c') hcop
    rcases hj : jOf D.q a c'.val with _ | j <;> simp only [hj, Bool.false_eq_true] at this
    rcases hT : findT j D.tmpls with _ | T <;> simp only [hT, Option.isSome_none, Bool.false_eq_true] at this
    exact ⟨j, T, rfl, hT⟩
  have htmpl : ∀ c' : ZMod D.M, ∀ j T, jOf D.q a c'.val = some j → findT j D.tmpls = some T →
      tmplOf D a c' = mkTemplate D.α0 T := by
    intro c' j T hj hT
    unfold tmplOf; rw [hj]; simp only [hT]
  -- the class datum of a prime in the class `c'`
  have hdatum : ∀ (c' : ZMod D.M) (j : ℕ) (p : ℕ), jOf D.q a c'.val = some j → (p : ZMod D.M) = c' →
      j < D.q ∧ 0 < j ∧ D.q * ((j * p) / D.q + 1) = j * p + (D.q - a) := by
    intro c' j p hj hpc
    have hpc' : p % D.M = c'.val := by rw [← hpc, ZMod.val_natCast]
    exact root_datum hq2 hMq ha0 haq hj hpc'
  -- the scale `R0` beyond which every prime of every piece exceeds `N0`
  obtain ⟨tlo, htlo0, htlo⟩ := tlo_exists hD
  have htl : (0 : ℝ) < tlo := by exact_mod_cast htlo0
  obtain ⟨R0, hR0⟩ : ∃ R0 : ℕ, (N0 : ℝ) < tlo * R0 := by
    obtain ⟨R0, hR⟩ := exists_nat_gt ((N0 : ℝ) / tlo)
    exact ⟨R0, by rwa [div_lt_iff₀ htl, mul_comm] at hR⟩
  have hN0 : ∀ (r p : ℕ) (u : ℚ), R0 ≤ r → tlo ≤ u → (u : ℝ) * r < p → N0 < p := by
    intro r p u hr hu hp
    have h1 : (R0 : ℝ) ≤ r := by exact_mod_cast hr
    have h2 : (tlo : ℝ) ≤ u := by exact_mod_cast hu
    have h3 : (tlo : ℝ) * R0 ≤ u * r := by
      have := mul_le_mul_of_nonneg_left h1 htl.le
      have := mul_le_mul_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ r)
      linarith
    have : (N0 : ℝ) < p := by linarith
    exact_mod_cast this
  -- the branch statements at a member and a prime of the class `c'`
  have hbranches : ∀ (i : (AltEven c hc Fr depth).ι), (AltEven c hc Fr depth).Adm i → 0 < i.1 →
      ∀ (p : ℕ) [Fact p.Prime] (j k : ℕ), j < D.q → 0 < j → D.q * k = j * p + (D.q - a) → N0 < p →
      BranchesValid D.cat D.Pbad D.q i.1 p ((altGeom c hc).borderSize i.1) k (delCount (altGeom c hc) i)
        (fun n => GLE p n ((AltEven c hc Fr depth).Q i)) := by
    intro i hi hr0 p _ j k hjq hj0 hk hN b hb hPb hqN hcond
    have hqp : D.q < p := lt_of_le_of_lt hqP hPb
    have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · subst h0; have : 0 < j * p := Nat.mul_pos hj0 (by omega)
        omega
      · exact h0
    have hkp : k < p := by
      have hlt : D.q - a < p := by omega
      have h1 : D.q * k < D.q * p :=
        calc D.q * k = j * p + (D.q - a) := hk
          _ < j * p + p := Nat.add_lt_add_left hlt (j * p)
          _ = (j + 1) * p := by ring
          _ ≤ D.q * p := Nat.mul_le_mul_right p hjq
      exact Nat.lt_of_mul_lt_mul_left h1
    exact hcat b hb i hi hr0 p hPb hN hqN j k hk hj0 hjq hk0 hkp hcond
  refine hasScaledContent_lift (AltEven c hc Fr depth) (altGeom c hc).scale (D.Λ : ℝ) R0
    (fun i => NodeFamily.family_degree Fr (altGeom c hc).geometry depth i) ?_
  refine altContent_of_bounds c hc hc1 Fr depth R0 D.M D.Λ B (fun _ => tmplOf D a) D.τ ?_ ?_ ?_ ?_ ?_
  · -- hmass (D6)
    intro ε hε
    have hcc : contentConstant D.M (tmplOf D a) = D.Λ := by
      unfold contentConstant
      have h1 : ∀ c' ∈ unitClasses D.M, (tmplOf D a c').mass = ((classMass D a c'.val : ℚ) : ℝ) := by
        intro c' hc'
        obtain ⟨j, T, hj, hT⟩ := hclass c' (mem_unitClasses.1 hc')
        rw [htmpl c' j T hj hT, mass_mkTemplate hD hT]
        simp [classMass, hj, hT]
      rw [Finset.sum_congr rfl h1, sum_unitClasses D.M (fun x => ((classMass D a x : ℚ) : ℝ)),
        ← unitSum_eq, hsum, Nat.totient_eq_card_coprime, ← unitCount_eq]
      have hpos : 0 < unitCount D.M D.M := by
        rw [unitCount_eq, ← Nat.totient_eq_card_coprime]; exact Nat.totient_pos.2 (by omega)
      push_cast
      field_simp
    rw [hcc]; linarith
  · -- tend_le (D4)
    intro ε hε c' hc'
    obtain ⟨j, T, hj, hT⟩ := hclass c' hc'
    rw [htmpl c' j T hj hT, tend_mkTemplate hD hT]
    exact_mod_cast (tmpl_facts hD hT).2.2.2.2.2.2.2
  · -- tail (D4 + branch D6)
    intro ε hε i hi c' hc' p hp hpc hlt _
    have hr2 : i.1 % 2 = 0 := hi.1.2
    rcases Nat.eq_zero_or_pos i.1 with h0 | hr0
    · have := altGeom_gle_Ecrude c hc hc1 Fr depth i hr2 p
      have h00 : Ecrude (cFr Fr) i.1 p = 0 := by simp [Ecrude, h0]
      rw [h00] at this
      exact this
    obtain ⟨j, T, hj, hT⟩ := hclass c' hc'
    obtain ⟨hjq, hj0, hk⟩ := hdatum c' j p hj hpc
    set k := (j * p) / D.q + 1 with hkdef
    rw [htmpl c' j T hj hT, tend_mkTemplate hD hT] at hlt
    obtain ⟨-, -, -, -, hκ, hqt, hPt, -⟩ := tmpl_facts hD hT
    set te := tendQ T.t1 T.pieces
    have hq' : (2 : ℝ) ≤ D.q := by exact_mod_cast hq2
    have hα' : (0 : ℝ) ≤ D.α := by exact_mod_cast hα
    have hqt' : ((D.q : ℚ) * (1 + 2 * D.α) : ℝ) ≤ te := by exact_mod_cast hqt
    have hκ' : ((1 + 2 * D.α : ℚ) : ℝ) ≤ ((j : ℚ) / D.q * te : ℚ) := by exact_mod_cast hκ
    push_cast at hqt' hκ'
    have hA1 : (1 : ℝ) ≤ 1 + 2 * D.α := by linarith
    have hA2 : (1 + 2 * (D.α : ℝ)) ≤ D.q * (1 + 2 * D.α) := by
      have := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ D.q by linarith) (by linarith : (0 : ℝ) ≤ 1 + 2 * D.α)
      linarith
    have hte0 : (0 : ℝ) < te := by linarith
    have hrR : (2 : ℝ) ≤ i.1 := by exact_mod_cast (show 2 ≤ i.1 by omega)
    have hr0' : (0 : ℝ) ≤ i.1 := by linarith
    have hlt' : (te : ℝ) * i.1 < p := (Nat.floor_lt (mul_nonneg hte0.le hr0')).1 hlt
    have hPb : D.Pbad < p := by
      have h1 : ((D.Pbad : ℚ) : ℝ) ≤ 2 * (te : ℝ) := by exact_mod_cast hPt
      have h2 : 2 * (te : ℝ) ≤ te * i.1 := by
        have := mul_le_mul_of_nonneg_left hrR hte0.le
        linarith
      have : (D.Pbad : ℝ) < p := by push_cast at h1; linarith
      exact_mod_cast this
    set m := (altGeom c hc).borderSize i.1 with hm
    obtain ⟨hb1, hb2⟩ := TwoTerm.altGeom_border c hc hr2
    have hc' : (c : ℝ) = 2 * D.α := by exact_mod_cast hcα
    have hb2' : ((2 * (m : ℚ) : ℚ) : ℝ) < ((c * i.1 + 1 : ℚ) : ℝ) := by exact_mod_cast hb2
    push_cast at hb2'
    rw [hc'] at hb2'
    -- (1 + 2α) r ≤ te r < p
    have hAr : (1 + 2 * (D.α : ℝ)) * i.1 ≤ te * i.1 :=
      mul_le_mul_of_nonneg_right (by linarith) hr0'
    -- N ≤ p and N ≤ k
    have hNp : i.1 + 2 * m ≤ p := by
      have : ((i.1 + 2 * m : ℕ) : ℝ) < p + 1 := by push_cast; linarith
      have : i.1 + 2 * m < p + 1 := by exact_mod_cast this
      omega
    have hNk : i.1 + 2 * m ≤ k := by
      have hk' : ((D.q * k : ℕ) : ℝ) = ((j * p + (D.q - a) : ℕ) : ℝ) := by rw [hk]
      push_cast [Nat.cast_sub haq.le] at hk'
      have ha2 : (a : ℝ) < D.q := by exact_mod_cast haq
      have hq0 : (0 : ℝ) < D.q := by linarith
      have hkq : (j : ℝ) / D.q * p < k := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ hq0]; linarith
      have hj' : (0 : ℝ) ≤ (j : ℝ) / D.q := by positivity
      have h1 := mul_le_mul_of_nonneg_left hlt'.le hj'
      have e1 : ((j : ℝ) / D.q * te) * i.1 = (j : ℝ) / D.q * (te * i.1) := by ring
      have h2 : ((1 + 2 * D.α) * i.1 : ℝ) ≤ ((j : ℝ) / D.q * te) * i.1 :=
        mul_le_mul_of_nonneg_right hκ' hr0'
      have : ((i.1 + 2 * m : ℕ) : ℝ) < k + 1 := by push_cast; linarith
      have : i.1 + 2 * m < k + 1 := by exact_mod_cast this
      omega
    have hqN : D.q * (i.1 + 2 * m) < p * p := by
      have hq0 : (0 : ℝ) < D.q := by linarith
      have h1 : (D.q : ℝ) * (1 + 2 * D.α) * i.1 < p := by
        have := mul_le_mul_of_nonneg_right hqt' hr0'
        linarith
      have h3 : (D.q : ℝ) * (i.1 + 2 * m) < D.q * ((1 + 2 * D.α) * i.1 + 1) :=
        mul_lt_mul_of_pos_left (by linarith) hq0
      have h5 : (1 : ℝ) ≤ (1 + 2 * D.α) * i.1 := by
        have := mul_le_mul_of_nonneg_right hA1 hr0'
        linarith
      have h4 : (D.q : ℝ) * ((1 + 2 * D.α) * i.1 + 1) ≤ 2 * (D.q * (1 + 2 * D.α) * i.1) := by
        have := mul_le_mul_of_nonneg_left h5 hq0.le
        linarith
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
      have h6 : (2 : ℝ) * p ≤ p * p := mul_le_mul_of_nonneg_right hp2 (by linarith)
      have h2 : ((D.q * (i.1 + 2 * m) : ℕ) : ℝ) < ((p * p : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast h2
    have hN0p : N0 < p := by
      obtain ⟨ht1, -, hch, hpcs, -⟩ := tmpl_facts hD hT
      have hge := (chain_ge T.pieces T.t1 hch hpcs).2
      have : (te : ℚ) ≥ tlo := le_trans (htlo j T hT) hge
      exact hN0 i.1 p te hi.2 this hlt'
    have hbv := hbranches i hi.1 hr0 p j k hjq hj0 hk hN0p
    obtain ⟨n, hn, hnb⟩ := hbv brD6 (brD6_mem D.extra) hPb hqN (by
      intro cd hcd
      simp only [brD6, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hcd
      rcases hcd with rfl | rfl
      · simp only [Cat.cNlep, Cond.Holds, Cond.L, if_false, Bool.false_eq_true]; push_cast; omega
      · simp only [Cat.cRlek, Cond.Holds, Cond.L, if_false, Bool.false_eq_true]; push_cast; omega)
    simp only [brD6, evalN_tD6] at hnb
    have : n = 0 := by omega
    rw [this] at hn
    exact hn
  · -- pre (D3)
    intro ε hε i hi c' hc' p h1 hp hpc _
    obtain ⟨j, T, hj, hT⟩ := hclass c' hc'
    rw [htmpl c' j T hj hT, mkTemplate_eq hD hT] at h1 ⊢
    obtain ⟨-, ht0, -⟩ := tmpl_facts hD hT
    have hpM : ¬ p ∣ D.M := by
      rw [← ZMod.isUnit_prime_iff_not_dvd hp, hpc]; exact hc'
    have h2 : p ≤ ⌊(D.t0 : ℝ) * i.1⌋₊ := by
      refine h1.trans (Nat.floor_le_floor ?_)
      exact mul_le_mul_of_nonneg_right (by show (T.t1 : ℝ) ≤ D.t0; exact_mod_cast ht0)
        (Nat.cast_nonneg _)
    obtain ⟨n, hn, hb⟩ := hpre i hi.1 p hpM h2
    refine ⟨n, hn, ?_⟩
    have : (D.α0b : ℝ) * i.1 ≤ (D.α0 : ℝ) * i.1 :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hα0b) (Nat.cast_nonneg _)
    show (n : ℝ) ≤ (D.α0 : ℝ) * i.1 + B.X i.1 p
    linarith
  · -- cov (D5, Theorem B)
    intro ε hε i hi c' hc' P hP p h1 h2 hp hpc _
    obtain ⟨j, T, hj, hT⟩ := hclass c' hc'
    rw [htmpl c' j T hj hT, mkTemplate_eq hD hT] at hP
    simp only [QTmpl.real, List.mem_map] at hP
    obtain ⟨x, hx, rfl⟩ := hP
    obtain ⟨-, -, -, hpcs, -⟩ := tmpl_facts hD hT
    have hok := hpcs x hx
    obtain ⟨hjq, hj0, hk⟩ := hdatum c' j p hj hpc
    have hr2 : i.1 % 2 = 0 := hi.1.2
    -- the piece range in real form
    have hs0 : (0 : ℝ) ≤ (x.1.s : ℝ) * i.1 := by
      unfold pieceOK at hok
      rcases hb : nth D.cat x.2.bi with _ | br <;> simp only [hb, reduceCtorEq, Bool.false_eq_true] at hok
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
      have : (0 : ℝ) < x.1.s := by exact_mod_cast hok.1.1.1.1.1.1.1.1.1.1.1.1.1.1
      positivity
    have hs : (x.1.s : ℝ) * i.1 < p := (Nat.floor_lt hs0).1 h1
    have h2' : p ≤ ⌊(x.1.t : ℝ) * i.1⌋₊ := h2
    have ht0 : (0 : ℝ) ≤ (x.1.t : ℝ) * i.1 := by
      by_contra hneg
      push_neg at hneg
      have h0 : ⌊(x.1.t : ℝ) * i.1⌋₊ = 0 := Nat.floor_of_nonpos hneg.le
      have := (Fact.out : p.Prime).two_le
      omega
    have ht : (p : ℝ) ≤ x.1.t * i.1 := (Nat.le_floor_iff ht0).1 h2'
    have hr0 : 0 < i.1 := by
      rcases Nat.eq_zero_or_pos i.1 with h0 | h0
      · rw [h0] at ht; simp at ht; have := (Fact.out : p.Prime).two_le
        have : (2 : ℝ) ≤ p := by exact_mod_cast this
        linarith
      · exact h0
    have hrd := round_of c hc hcα hr2 hq2 ha0 haq hk (r := i.1)
    have hcr : GLE p (2 * i.1 * (3 * Nat.log p (14 * i.1) + D.cF)) ((AltEven c hc Fr depth).Q i) := by
      refine (altGeom_gle_Ecrude c hc hc1 Fr depth i hr2 p).mono ?_
      unfold Ecrude
      exact Nat.mul_le_mul_left _ (by omega)
    have hodd : D.Pbad < p → p % 2 = 1 := by
      intro hPb
      rcases (Fact.out : p.Prime).eq_two_or_odd with h | h
      · omega
      · exact h
    have hdel : delCount (altGeom c hc) i ≤ D.depth :=
      (delCount_le (altGeom c hc) Fr depth i hi.1.1).trans hdepth
    obtain ⟨n, hn, hb⟩ := piece_sound x.1 x.2 hok (by omega) hα (fun n => GLE p n ((AltEven c hc Fr depth).Q i))
      hrd hodd (Fact.out : p.Prime).two_le hdel hcr (hbranches i hi.1 hr0 p j _ hjq hj0 hk (by
        obtain ⟨-, -, hch, hpcs', -⟩ := tmpl_facts hD hT
        have hge := (chain_ge T.pieces T.t1 hch hpcs').1 x hx
        exact hN0 i.1 p x.1.s hi.2 (le_trans (htlo j T hT) hge) hs)) hs ht
    exact ⟨n, hn, hb⟩

end TheoremD

end CatalanCore.Uniform.Content.BankShared.Check
