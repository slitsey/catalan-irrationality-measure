module

public import CatalanCore.Uniform.Bank.Plane1.Dips.Types

@[expose] public section
set_option Elab.async false
set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option maxHeartbeats 1600000

/-! # Counting the potentials of a dip line (wave R1; ledger R01-R03; package R1d)

The sum `Σ ρ + Σ γ` of a line certificate over the hybrid `Fin r ⊕ Fin m` is the sum over the nodes `t < N = r + 2 m`
of the node potential `nodePotAt` (`Fin r` common nodes carry `rc + cc`, the border node `r + 2 i` carries `rb`, the
border node `r + 2 i + 1` carries `cb`).  On a period the node potential is constant on each arc and depends on the
parity of the node; the sum over an arc of length `ℓ` is at most `(f₀ + f₁) ℓ / 2 + |f₀ - f₁| / 2`.  Collecting the
arcs of all periods gives the bound `count_bound` as an affine form in the breakpoints `k_A, k_B, r mod p, N mod p`
and `p`. -/

namespace CatalanCore.Uniform.Bank.Plane1.Dips
open Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Uniform.Bank.Plane1

section Generic

/-- The exact sum over a run, by the number of even and odd nodes. -/
theorem sum_par_eq (f0 f1 : ℚ) (lo hi : ℕ) (hlh : lo ≤ hi) :
    ∑ t ∈ Ico lo hi, (if t % 2 = 0 then f0 else f1) =
      f0 * (((hi + 1) / 2 - (lo + 1) / 2 : ℕ) : ℚ) + f1 * ((hi / 2 - lo / 2 : ℕ) : ℚ) := by
  induction hi, hlh using Nat.le_induction with
  | base => simp
  | succ hi hlh ih =>
    rw [Finset.sum_Ico_succ_top hlh, ih]
    by_cases h : hi % 2 = 0
    · rw [if_pos h]
      have e1 : ((hi + 1 + 1) / 2 - (lo + 1) / 2 : ℕ) = (hi + 1) / 2 - (lo + 1) / 2 + 1 := by omega
      have e2 : ((hi + 1) / 2 - lo / 2 : ℕ) = hi / 2 - lo / 2 := by omega
      rw [e1, e2]; push_cast; ring
    · rw [if_neg h]
      have e1 : ((hi + 1 + 1) / 2 - (lo + 1) / 2 : ℕ) = (hi + 1) / 2 - (lo + 1) / 2 := by omega
      have e2 : ((hi + 1) / 2 - lo / 2 : ℕ) = hi / 2 - lo / 2 + 1 := by omega
      rw [e1, e2]; push_cast; ring

/-- A run of nodes with a potential depending on the parity: at most `(f₀ + f₁) ℓ / 2 + |f₀ - f₁| / 2`. -/
theorem sum_par_le (f0 f1 : ℚ) (lo hi : ℕ) (hlh : lo ≤ hi) :
    ∑ t ∈ Ico lo hi, (if t % 2 = 0 then f0 else f1) ≤ (f0 + f1) / 2 * ((hi : ℚ) - lo) + |f0 - f1| / 2 := by
  rw [sum_par_eq f0 f1 lo hi hlh]
  set c0 : ℕ := (hi + 1) / 2 - (lo + 1) / 2 with hc0
  set c1 : ℕ := hi / 2 - lo / 2 with hc1
  have h1 : c0 + c1 + lo = hi := by omega
  have h2 : c0 ≤ c1 + 1 := by omega
  have h3 : c1 ≤ c0 + 1 := by omega
  have q1 : (c0 : ℚ) + c1 + lo = hi := by exact_mod_cast h1
  have q2 : (c0 : ℚ) ≤ c1 + 1 := by exact_mod_cast h2
  have q3 : (c1 : ℚ) ≤ c0 + 1 := by exact_mod_cast h3
  have e : (hi : ℚ) - lo = c0 + c1 := by linarith
  rw [e]
  rcases le_total f0 f1 with h | h
  · rw [abs_of_nonpos (by linarith)]
    nlinarith [mul_nonneg (sub_nonneg.2 h) (sub_nonneg.2 q3)]
  · rw [abs_of_nonneg (by linarith)]
    nlinarith [mul_nonneg (sub_nonneg.2 h) (sub_nonneg.2 q2)]

end Generic

section Periods

theorem sum_range_periods (F : ℕ → ℚ) (p q' e : ℕ) :
    ∑ t ∈ range (q' * p + e), F t =
      ∑ k ∈ range q', ∑ x ∈ range p, F (k * p + x) + ∑ x ∈ range e, F (q' * p + x) := by
  have h1 : ∀ q : ℕ, ∑ t ∈ range (q * p), F t = ∑ k ∈ range q, ∑ x ∈ range p, F (k * p + x) := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]
  rw [Finset.sum_range_add, h1]

theorem sum_range_arcs (g : ℕ → ℚ) (bs : ℕ → ℕ) (hmono : ∀ j < 5, bs j ≤ bs (j + 1)) (hb0 : bs 0 = 0) :
    ∀ c ≤ 5, ∑ x ∈ range (bs c), g x = ∑ a ∈ range c, ∑ x ∈ Ico (bs a) (bs (a + 1)), g x := by
  intro c
  induction c with
  | zero => intro _; simp [hb0]
  | succ c ih =>
    intro hc
    rw [Finset.sum_range_succ, ← ih (by omega)]
    exact (Finset.sum_range_add_sum_Ico g (hmono c (by omega))).symm

end Periods

section CountPeriod

variable (T : LTab) (σ : Support) (n p r m : ℕ)

/-- The potential of a node of the given role at period `q`, arc `a`, parity `par`: a common node carries its row and its
column, a border node of odd parity its column, of even parity its row. -/
def nodePotAt (q : ℕ) (border : Bool) (a : ℕ) (par : Bool) : ℕ :=
  if border then (if par then potAt T.cb T.arcs.length q a true else potAt T.rb T.arcs.length q a false)
  else potAt T.rc T.arcs.length q a par + potAt T.cc T.arcs.length q a par

/-- The potential of the node `t`. -/
noncomputable def nodePot (t : ℕ) : ℚ :=
  (nodePotAt T (t / p) (decide (r ≤ t)) (arcIdx T (nodeBits σ n p r m t)) (decide (t % 2 = 1)) : ℚ)

/-- The two parity values of a piece. -/
def gAt (k : ℕ) (rl : Bool) (a : ℕ) (e : ℕ) : ℚ := (nodePotAt T k rl a (decide (e = 1)) : ℚ)

variable {T σ n p r m}

theorem inner_bound (hp : 0 < p) (rl : ℕ → ℕ → Bool) (bs : ℕ → ℕ) (k a : ℕ)
    (hlh : bs a ≤ bs (a + 1)) (hbp : bs (a + 1) ≤ p)
    (harc : ∀ x ∈ Ico (bs a) (bs (a + 1)), k * p + x < r + 2 * m →
      arcIdx T (nodeBits σ n p r m (k * p + x)) = a)
    (hrole : ∀ x ∈ Ico (bs a) (bs (a + 1)), k * p + x < r + 2 * m → decide (r ≤ k * p + x) = rl k a)
    (hlt : ∀ x ∈ Ico (bs a) (bs (a + 1)), k * p + x < r + 2 * m) :
    ∑ x ∈ Ico (bs a) (bs (a + 1)), nodePot T σ n p r m (k * p + x) ≤
      (gAt T k (rl k a) a 0 + gAt T k (rl k a) a 1) / 2 * ((bs (a + 1) : ℚ) - bs a) +
        |gAt T k (rl k a) a 0 - gAt T k (rl k a) a 1| / 2 := by
  have hpt : ∀ x ∈ Ico (bs a) (bs (a + 1)), nodePot T σ n p r m (k * p + x) =
      (if (k * p + x) % 2 = 0 then gAt T k (rl k a) a 0 else gAt T k (rl k a) a 1) := by
    intro x hx
    have hx' := Finset.mem_Ico.1 hx
    have hxp : x < p := lt_of_lt_of_le hx'.2 hbp
    have hdiv : (k * p + x) / p = k := by
      rw [add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt hxp, zero_add]
    unfold nodePot gAt
    rw [hdiv, harc x hx (hlt x hx), hrole x hx (hlt x hx)]
    by_cases h : (k * p + x) % 2 = 0
    · simp [h]
    · have : (k * p + x) % 2 = 1 := by omega
      simp [this]
  rw [Finset.sum_congr rfl hpt]
  have := sum_par_le (gAt T k (rl k a) a 0) (gAt T k (rl k a) a 1) (k * p + bs a) (k * p + bs (a + 1))
    (by omega)
  have e : ∑ x ∈ Ico (bs a) (bs (a + 1)), (if (k * p + x) % 2 = 0 then gAt T k (rl k a) a 0
      else gAt T k (rl k a) a 1) = ∑ t ∈ Ico (k * p + bs a) (k * p + bs (a + 1)),
      (if t % 2 = 0 then gAt T k (rl k a) a 0 else gAt T k (rl k a) a 1) := by
    have := Finset.sum_Ico_add (fun t => if t % 2 = 0 then gAt T k (rl k a) a 0 else gAt T k (rl k a) a 1)
      (bs a) (bs (a + 1)) (k * p)
    rw [this, add_comm (bs a), add_comm (bs (a + 1))]
  rw [e]
  push_cast at this
  linarith

end CountPeriod

section CountPeriod2

variable {T : LTab} {σ : Support} {n p r m : ℕ}

/-- The bound of one piece (period `k`, arc `a` of length `b1 - b0`). -/
noncomputable def pieceB (T : LTab) (rl : ℕ → ℕ → Bool) (k a b0 b1 : ℕ) : ℚ :=
  (gAt T k (rl k a) a 0 + gAt T k (rl k a) a 1) / 2 * ((b1 : ℚ) - b0) + |gAt T k (rl k a) a 0 - gAt T k (rl k a) a 1| / 2

theorem bs_le (bs : ℕ → ℕ) (hmono : ∀ j < 5, bs j ≤ bs (j + 1)) :
    ∀ i j, i ≤ j → j ≤ 5 → bs i ≤ bs j := by
  intro i j hij
  induction j, hij using Nat.le_induction with
  | base => intro _; exact le_rfl
  | succ j hij ih =>
    intro hj
    exact le_trans (ih (by omega)) (hmono j (by omega))

theorem count_period (hp : 0 < p) (bs : ℕ → ℕ) (hmono : ∀ j < 5, bs j ≤ bs (j + 1)) (hb0 : bs 0 = 0)
    (hb5 : bs 5 = p) (q' pN : ℕ) (hpN : pN ≤ 5) (hN : r + 2 * m = q' * p + bs pN) (rl : ℕ → ℕ → Bool)
    (harc : ∀ t < r + 2 * m, ∀ a < 5, bs a ≤ t % p → t % p < bs (a + 1) →
      arcIdx T (nodeBits σ n p r m t) = a)
    (hrole : ∀ t < r + 2 * m, ∀ a < 5, bs a ≤ t % p → t % p < bs (a + 1) → decide (r ≤ t) = rl (t / p) a) :
    ∑ t ∈ range (r + 2 * m), nodePot T σ n p r m t ≤
      ∑ k ∈ range q', ∑ a ∈ range 5, pieceB T rl k a (bs a) (bs (a + 1)) +
        ∑ a ∈ range pN, pieceB T rl q' a (bs a) (bs (a + 1)) := by
  have hmod : ∀ k x, x < p → (k * p + x) % p = x := fun k x hx => by
    rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx]
  have hdiv : ∀ k x, x < p → (k * p + x) / p = k := fun k x hx => by
    rw [add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt hx, zero_add]
  rw [hN, sum_range_periods]
  refine add_le_add (Finset.sum_le_sum fun k hk => ?_) ?_
  · have hk' := Finset.mem_range.1 hk
    have hkN : (k + 1) * p ≤ q' * p := Nat.mul_le_mul_right p hk'
    have e5 : range p = range (bs 5) := by rw [hb5]
    rw [e5, sum_range_arcs (fun x => nodePot T σ n p r m (k * p + x)) bs hmono hb0 5 le_rfl]
    refine Finset.sum_le_sum fun a ha => ?_
    have ha' := Finset.mem_range.1 ha
    have hbp : bs (a + 1) ≤ bs 5 := bs_le bs hmono (a + 1) 5 (by omega) le_rfl
    rw [hb5] at hbp
    have hlt : ∀ x ∈ Ico (bs a) (bs (a + 1)), k * p + x < r + 2 * m := by
      intro x hx
      have := Finset.mem_Ico.1 hx
      rw [hN]; nlinarith
    exact inner_bound hp rl bs k a (hmono a ha') hbp
      (fun x hx hltx => by
        have hxp : x < p := lt_of_lt_of_le (Finset.mem_Ico.1 hx).2 hbp
        have := harc (k * p + x) hltx a ha' (by rw [hmod k x hxp]; exact (Finset.mem_Ico.1 hx).1)
          (by rw [hmod k x hxp]; exact (Finset.mem_Ico.1 hx).2)
        exact this)
      (fun x hx hltx => by
        have hxp : x < p := lt_of_lt_of_le (Finset.mem_Ico.1 hx).2 hbp
        have := hrole (k * p + x) hltx a ha' (by rw [hmod k x hxp]; exact (Finset.mem_Ico.1 hx).1)
          (by rw [hmod k x hxp]; exact (Finset.mem_Ico.1 hx).2)
        rwa [hdiv k x hxp] at this)
      hlt
  · rw [sum_range_arcs (fun x => nodePot T σ n p r m (q' * p + x)) bs hmono hb0 pN hpN]
    refine Finset.sum_le_sum fun a ha => ?_
    have ha' := Finset.mem_range.1 ha
    have hbp : bs (a + 1) ≤ p := by
      rw [← hb5]; exact bs_le bs hmono (a + 1) 5 (by omega) le_rfl
    have hbN : bs (a + 1) ≤ bs pN := bs_le bs hmono (a + 1) pN (by omega) hpN
    have hlt : ∀ x ∈ Ico (bs a) (bs (a + 1)), q' * p + x < r + 2 * m := by
      intro x hx
      have := Finset.mem_Ico.1 hx
      rw [hN]; omega
    exact inner_bound hp rl bs q' a (hmono a (by omega)) hbp
      (fun x hx hltx => by
        have hxp : x < p := lt_of_lt_of_le (Finset.mem_Ico.1 hx).2 hbp
        exact harc (q' * p + x) hltx a (by omega) (by rw [hmod q' x hxp]; exact (Finset.mem_Ico.1 hx).1)
          (by rw [hmod q' x hxp]; exact (Finset.mem_Ico.1 hx).2))
      (fun x hx hltx => by
        have hxp : x < p := lt_of_lt_of_le (Finset.mem_Ico.1 hx).2 hbp
        have := hrole (q' * p + x) hltx a (by omega) (by rw [hmod q' x hxp]; exact (Finset.mem_Ico.1 hx).1)
          (by rw [hmod q' x hxp]; exact (Finset.mem_Ico.1 hx).2)
        rwa [hdiv q' x hxp] at this)
      hlt

end CountPeriod2

section SumHyb

variable {T : LTab} {σ : Support} {n p r m : ℕ}

theorem sum_range_two_mul (f : ℕ → ℚ) (m : ℕ) :
    ∑ j ∈ range (2 * m), f j = ∑ i ∈ range m, (f (2 * i) + f (2 * i + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring

theorem sum_hyb (hr : r % 2 = 0) :
    ∑ x, rhoF σ n p r m T x + ∑ y, gammaF σ n p r m T y = ∑ t ∈ range (r + 2 * m), nodePot T σ n p r m t := by
  rw [← Finset.sum_add_distrib, Fintype.sum_sum_type, Finset.sum_range_add]
  congr 1
  · rw [← Fin.sum_univ_eq_sum_range (fun t => nodePot T σ n p r m t) r]
    refine Finset.sum_congr rfl fun ci _ => ?_
    have h : ¬ (r ≤ ci.1) := by have := ci.2; omega
    simp [rhoF, gammaF, nodePot, nodePotAt, h]
  · rw [sum_range_two_mul, ← Fin.sum_univ_eq_sum_range
      (fun i => nodePot T σ n p r m (r + 2 * i) + nodePot T σ n p r m (r + (2 * i + 1))) m]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e1 : (r + 2 * i.1) % 2 = 0 := by omega
    have e2 : (r + 2 * i.1 + 1) % 2 = 1 := by omega
    have e3 : r + (2 * i.1 + 1) = r + 2 * i.1 + 1 := by omega
    rw [e3]
    simp [rhoF, gammaF, nodePot, nodePotAt, e1, e2]
    intro h; omega

end SumHyb

section Collect

variable {T : LTab} {σ : Support} {n p r m : ℕ}

/-- The total weight of arc `a` over the periods. -/
noncomputable def Wcoef (T : LTab) (rl : ℕ → ℕ → Bool) (q' pN a : ℕ) : ℚ :=
  ∑ k ∈ range q', (gAt T k (rl k a) a 0 + gAt T k (rl k a) a 1) / 2 +
    (if a < pN then (gAt T q' (rl q' a) a 0 + gAt T q' (rl q' a) a 1) / 2 else 0)

/-- The total parity slack. -/
noncomputable def Sslack (T : LTab) (rl : ℕ → ℕ → Bool) (q' pN : ℕ) : ℚ :=
  ∑ k ∈ range q', ∑ a ∈ range 5, |gAt T k (rl k a) a 0 - gAt T k (rl k a) a 1| / 2 +
    ∑ a ∈ range pN, |gAt T q' (rl q' a) a 0 - gAt T q' (rl q' a) a 1| / 2

theorem sum_range_lt (f : ℕ → ℚ) {pN : ℕ} (h : pN ≤ 5) :
    ∑ a ∈ range pN, f a = ∑ a ∈ range 5, (if a < pN then f a else 0) := by
  rw [← Finset.sum_filter]
  congr 1
  ext a
  simp only [Finset.mem_range, Finset.mem_filter]
  omega

theorem collect (T : LTab) (rl : ℕ → ℕ → Bool) (bs : ℕ → ℕ) (q' pN : ℕ) (hpN : pN ≤ 5) :
    ∑ k ∈ range q', ∑ a ∈ range 5, pieceB T rl k a (bs a) (bs (a + 1)) +
        ∑ a ∈ range pN, pieceB T rl q' a (bs a) (bs (a + 1)) =
      ∑ a ∈ range 5, Wcoef T rl q' pN a * ((bs (a + 1) : ℚ) - bs a) + Sslack T rl q' pN := by
  unfold pieceB Wcoef Sslack
  simp only [Finset.sum_add_distrib]
  rw [sum_range_lt (fun a => (gAt T q' (rl q' a) a 0 + gAt T q' (rl q' a) a 1) / 2 * ((bs (a + 1) : ℚ) - bs a)) hpN,
    sum_range_lt (fun a => |gAt T q' (rl q' a) a 0 - gAt T q' (rl q' a) a 1| / 2) hpN]
  have e1 : ∑ k ∈ range q', ∑ a ∈ range 5, (gAt T k (rl k a) a 0 + gAt T k (rl k a) a 1) / 2 *
      ((bs (a + 1) : ℚ) - bs a) = ∑ a ∈ range 5, (∑ k ∈ range q', (gAt T k (rl k a) a 0 +
      gAt T k (rl k a) a 1) / 2) * ((bs (a + 1) : ℚ) - bs a) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul]
  have e2 : ∑ a ∈ range 5, (∑ k ∈ range q', (gAt T k (rl k a) a 0 + gAt T k (rl k a) a 1) / 2 +
      (if a < pN then (gAt T q' (rl q' a) a 0 + gAt T q' (rl q' a) a 1) / 2 else 0)) *
      ((bs (a + 1) : ℚ) - bs a) = ∑ a ∈ range 5, (∑ k ∈ range q', (gAt T k (rl k a) a 0 +
      gAt T k (rl k a) a 1) / 2) * ((bs (a + 1) : ℚ) - bs a) +
      ∑ a ∈ range 5, (if a < pN then (gAt T q' (rl q' a) a 0 + gAt T q' (rl q' a) a 1) / 2 *
        ((bs (a + 1) : ℚ) - bs a) else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs <;> ring
  rw [e1, e2]
  ring

end Collect

end CatalanCore.Uniform.Bank.Plane1.Dips
