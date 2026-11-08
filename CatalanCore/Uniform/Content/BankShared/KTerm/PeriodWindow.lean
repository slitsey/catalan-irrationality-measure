module

public import CatalanCore.Uniform.Content.BankShared.KTerm.PeriodCell
public import CatalanCore.Uniform.Content.BankShared.KTerm.Prefix

@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 1600000

/-! # Lemma T: the piece bound of a certified cell for every strip at once (wave H5a-closed)

Let `c` be a cell of the period table (`PeriodCell`) with `c.ok α κ0 κ1`, `n' ≥ 1` a strip, and `(r, p, m, kv)` an
integer point with `r / p ∈ [b n' + u0, b n' + u1)`, `|m - α r| ≤ 1/2` and the two pole indices `kv i = κ_i p + e_i`,
`0 ≤ e_i ≤ 1`.  Then

* `pre_bound`: the prefix branch `kbrPre (a n' + nu) j0 [j1, j2]` of the cell has
  `evalN ≤ (2 + 2 α - g1) r + (b n' g1 - g0) p + 3`;
* `d1x_bound`: the branch `D1x` (`kD1xE`) has the same bound on a `d1x` cell.

This is the piece bound `n_p ≤ (a + b θ) r + C` of the expansion piece `expPiece α b 3 n' c` for the branch
that realises it, for every strip `n'` at once: nothing depends on `n'` but the index of the prefix branch.
The constant `3` is `1` (rounding of `m`, twice: the lower cut and the upper cut) `+ 1` (pole index) `+ 1`. -/

namespace CatalanCore.Uniform.Content.BankShared.KTerm
open KExpr

/-- `D1x`: `2 r + 2 m - δ_p(m)` as a `k`-expression. -/
def kD1xE : KExpr := .tsub (.add (.smul 2 .vr) (.smul 2 .vm)) (.dist .vm)

theorem kMn_exists (r p m : ℕ) (k : ℕ → ℕ) : ∀ (l : List KExpr) (a : KExpr),
    ∃ x ∈ a :: l, (kMn a l).evalN r p m k = x.evalN r p m k
  | [], a => ⟨a, List.mem_cons_self, rfl⟩
  | y :: l, a => by
    obtain ⟨x, hx, h⟩ := kMn_exists r p m k l (.mn a y)
    rcases List.mem_cons.1 hx with rfl | hx
    · rcases min_choice (a.evalN r p m k) (y.evalN r p m k) with hm | hm
      · exact ⟨a, List.mem_cons_self, h.trans hm⟩
      · exact ⟨y, List.mem_cons_of_mem _ List.mem_cons_self, h.trans hm⟩
    · exact ⟨x, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx), h⟩

theorem kMx_exists (r p m : ℕ) (k : ℕ → ℕ) : ∀ (l : List KExpr) (a : KExpr),
    ∃ x ∈ a :: l, (kMx a l).evalN r p m k = x.evalN r p m k
  | [], a => ⟨a, List.mem_cons_self, rfl⟩
  | y :: l, a => by
    obtain ⟨x, hx, h⟩ := kMx_exists r p m k l (.mx a y)
    rcases List.mem_cons.1 hx with rfl | hx
    · rcases max_choice (a.evalN r p m k) (y.evalN r p m k) with hm | hm
      · exact ⟨a, List.mem_cons_self, h.trans hm⟩
      · exact ⟨y, List.mem_cons_of_mem _ List.mem_cons_self, h.trans hm⟩
    · exact ⟨x, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx), h⟩

theorem natsub_cast_ge (a b : ℕ) : (a : ℚ) - b ≤ ((a - b : ℕ) : ℚ) := by
  rcases le_total b a with h | h
  · rw [Nat.cast_sub h]
  · rw [Nat.sub_eq_zero_of_le h]
    have : (a : ℚ) ≤ b := by exact_mod_cast h
    simp only [Nat.cast_zero]
    linarith

theorem natsub_cast_le (a b : ℕ) (B : ℚ) (h : (a : ℚ) - b ≤ B) (h0 : 0 ≤ B) : ((a - b : ℕ) : ℚ) ≤ B := by
  rcases le_total b a with hb | hb
  · rw [Nat.cast_sub hb]; exact h
  · rw [Nat.sub_eq_zero_of_le hb]; simpa using h0

/-- The data of one integer point in one cell of one strip. -/
structure CellCtx (α κ0 κ1 : ℚ) (a b n' : ℕ) (c : PCell) (r p m : ℕ) (kv : ℕ → ℕ) : Prop where
  hα : 0 ≤ α
  hab : α * b = a
  hb : 1 ≤ b
  hn : 1 ≤ n'
  hok : c.ok α κ0 κ1 = true
  hp : 0 < p
  hm1 : -1 / 2 ≤ (m : ℚ) - α * r
  hm2 : (m : ℚ) - α * r ≤ 1 / 2
  hk0 : κ0 * p ≤ kv 0
  hk0' : (kv 0 : ℚ) ≤ κ0 * p + 1
  hk1 : κ1 * p ≤ kv 1
  hk1' : (kv 1 : ℚ) ≤ κ1 * p + 1
  hr0 : ((b : ℚ) * n' + c.u0) * p ≤ r
  hr1 : (r : ℚ) < ((b : ℚ) * n' + c.u1) * p

/-- The coordinates of the point: `u = r / p - b n'`, `⌊r / p⌋ = b n' + kc`. -/
theorem CellCtx.facts {α κ0 κ1 : ℚ} {a b n' : ℕ} {c : PCell} {r p m : ℕ} {kv : ℕ → ℕ}
    (h : CellCtx α κ0 κ1 a b n' c r p m kv) :
    ∃ u : ℚ, c.u0 ≤ u ∧ u < c.u1 ∧ (r : ℚ) = p * (u + b * n') ∧ r / p = b * n' + c.kc ∧
      α * r - ((a * n' + c.nu : ℕ) : ℚ) * p = p * (α * u - c.nu) := by
  obtain ⟨hlt, hk0, hk1, hnu0, hnu1, -⟩ := c.ok_spec h.hok
  have hpQ : (0 : ℚ) < p := by exact_mod_cast h.hp
  obtain ⟨u, hu⟩ : ∃ u : ℚ, u = (r : ℚ) / p - b * n' := ⟨_, rfl⟩
  have hru : (r : ℚ) = p * (u + b * n') := by rw [hu]; field_simp; ring
  refine ⟨u, ?_, ?_, hru, ?_, ?_⟩
  · by_contra hcon
    push Not at hcon
    nlinarith [mul_pos hpQ (sub_pos.2 hcon), h.hr0]
  · by_contra hcon
    push Not at hcon
    nlinarith [mul_nonneg hpQ.le (sub_nonneg.2 hcon), h.hr1]
  · apply Nat.div_eq_of_lt_le
    · have : (((b * n' + c.kc) * p : ℕ) : ℚ) ≤ r := by
        push_cast
        nlinarith [h.hr0, mul_nonneg (sub_nonneg.2 hk0) hpQ.le]
      exact_mod_cast this
    · have : (r : ℚ) < (((b * n' + c.kc + 1) * p : ℕ) : ℚ) := by
        push_cast
        nlinarith [h.hr1, mul_nonneg (sub_nonneg.2 hk1) hpQ.le]
      exact_mod_cast this
  · have hab := h.hab
    rw [hru]
    push_cast
    linear_combination ((n' : ℚ) * p) * hab

/-- The lower bound `p (αu - ν) ≥ 0` etc. that every cell point satisfies. -/
theorem CellCtx.nu_le {α κ0 κ1 : ℚ} {a b n' : ℕ} {c : PCell} {r p m : ℕ} {kv : ℕ → ℕ}
    (h : CellCtx α κ0 κ1 a b n' c r p m kv) {u : ℚ} (hu0 : c.u0 ≤ u) : (c.nu : ℚ) ≤ α * u := by
  obtain ⟨-, -, -, hnu0, -, -⟩ := c.ok_spec h.hok
  nlinarith [mul_le_mul_of_nonneg_left hu0 h.hα]

/-! ### The prefix branch -/

section Pre

variable {α κ0 κ1 : ℚ} {a b n' : ℕ} {c : PCell} {r p m : ℕ} {kv : ℕ → ℕ}

theorem pre_hi (h : CellCtx α κ0 κ1 a b n' c r p m kv) {j0 j1 j2 : ℕ} (hbr : c.br = .pre j0 j1 j2)
    {u : ℚ} (hru : (r : ℚ) = p * (u + b * n')) (hdiv : r / p = b * n' + c.kc)
    (hαr : α * r - ((a * n' + c.nu : ℕ) : ℚ) * p = p * (α * u - c.nu)) :
    ∃ hh ∈ c.hiL α κ0 κ1, (p : ℚ) * (b * n' + c.kc) + p * lnEval hh u - 1 ≤
      ((kPreHi (a * n' + c.nu) j0 [j1, j2]).evalN r p m kv : ℕ) := by
  have hiE : kPreHi (a * n' + c.nu) j0 [j1, j2] = kMn (kNn (a * n' + c.nu))
      [KExpr.add KExpr.vr KExpr.vp, KExpr.add KExpr.ap (KExpr.smul (j0 + 1) KExpr.vp),
        KExpr.add KExpr.ap (KExpr.add (KExpr.vk 0) (KExpr.smul j1 KExpr.vp)),
        KExpr.add KExpr.ap (KExpr.add (KExpr.vk 1) (KExpr.smul j2 KExpr.vp))] := rfl
  obtain ⟨x, hx, heq⟩ := kMn_exists r p m kv _ (kNn (a * n' + c.nu))
  rw [hiE, heq]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  have hpQ : (0 : ℚ) < p := by exact_mod_cast h.hp
  have hm1 := h.hm1
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · refine ⟨(-(c.kc : ℚ) - 2 * (c.nu : ℚ), 1 + 2 * α), by simp [PCell.hiL, hbr], ?_⟩
    have h1 := natsub_cast_ge m ((a * n' + c.nu) * p)
    push_cast at h1 hαr
    simp only [kNn, KExpr.evalN, lnEval]
    push_cast
    nlinarith
  · refine ⟨(1 - (c.kc : ℚ), 1), by simp [PCell.hiL, hbr], ?_⟩
    simp only [KExpr.evalN, lnEval]
    push_cast
    nlinarith
  · refine ⟨((j0 : ℚ) + 1, 0), by simp [PCell.hiL, hbr], ?_⟩
    simp only [KExpr.evalN, lnEval, hdiv]
    push_cast
    nlinarith
  · refine ⟨(κ0 + (j1 : ℚ), 0), by simp [PCell.hiL, hbr], ?_⟩
    have := h.hk0
    simp only [KExpr.evalN, lnEval, hdiv]
    push_cast
    nlinarith
  · refine ⟨(κ1 + (j2 : ℚ), 0), by simp [PCell.hiL, hbr], ?_⟩
    have := h.hk1
    simp only [KExpr.evalN, lnEval, hdiv]
    push_cast
    nlinarith

theorem pre_lo (h : CellCtx α κ0 κ1 a b n' c r p m kv) {j0 j1 j2 : ℕ} (hbr : c.br = .pre j0 j1 j2)
    {u : ℚ} (hu0 : c.u0 ≤ u) (hru : (r : ℚ) = p * (u + b * n')) (hdiv : r / p = b * n' + c.kc)
    (hαr : α * r - ((a * n' + c.nu : ℕ) : ℚ) * p = p * (α * u - c.nu)) :
    ∃ ll ∈ c.loL α κ0 κ1, ((kPreLo (a * n' + c.nu) j0 [j1, j2]).evalN r p m kv : ℕ) ≤
      (p : ℚ) * (b * n' + c.kc) + p * lnEval ll u + 1 := by
  have loE : kPreLo (a * n' + c.nu) j0 [j1, j2] = kMx (KExpr.tsub (kNn (a * n' + c.nu)) KExpr.vp)
      [KExpr.vr, KExpr.add KExpr.ap (KExpr.smul j0 KExpr.vp),
        (if j1 = 0 then KExpr.vr else KExpr.add KExpr.ap (KExpr.add (KExpr.vk 0) (KExpr.smul (j1 - 1) KExpr.vp))),
        (if j2 = 0 then KExpr.vr else KExpr.add KExpr.ap (KExpr.add (KExpr.vk 1) (KExpr.smul (j2 - 1) KExpr.vp)))] :=
    rfl
  obtain ⟨x, hx, heq⟩ := kMx_exists r p m kv _ (KExpr.tsub (kNn (a * n' + c.nu)) KExpr.vp)
  rw [loE, heq]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  have hpQ : (0 : ℚ) < p := by exact_mod_cast h.hp
  have hm2 := h.hm2
  have hbn : (1 : ℚ) ≤ (b : ℚ) * n' := by
    have h1 : (1 : ℚ) ≤ b := by exact_mod_cast h.hb
    have h2 : (1 : ℚ) ≤ n' := by exact_mod_cast h.hn
    nlinarith
  obtain ⟨-, hk, -, -, -, -⟩ := c.ok_spec h.hok
  have hkc : (0 : ℚ) ≤ c.kc := Nat.cast_nonneg _
  have hw : (c.nu : ℚ) ≤ α * u := h.nu_le hu0
  have hu00 : 0 ≤ u := by linarith
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · refine ⟨(-(c.kc : ℚ) - 2 * (c.nu : ℚ) - 1, 1 + 2 * α), by simp [PCell.loL, hbr], ?_⟩
    -- the truncated `m - n p`
    have hT : (((m - (a * n' + c.nu) * p : ℕ) : ℚ)) ≤ p * (α * u - c.nu) + 1 / 2 := by
      apply natsub_cast_le
      · push_cast at hαr ⊢
        linarith
      · nlinarith [mul_nonneg hpQ.le (sub_nonneg.2 hw)]
    simp only [kNn, KExpr.evalN, lnEval]
    apply natsub_cast_le
    · push_cast at hT ⊢
      nlinarith
    · push_cast
      nlinarith [mul_nonneg hpQ.le (sub_nonneg.2 hw), mul_nonneg hpQ.le hu00, mul_nonneg hpQ.le (sub_nonneg.2 hbn),
        mul_nonneg hpQ.le (sub_nonneg.2 hk)]
  · refine ⟨(-(c.kc : ℚ), 1), by simp [PCell.loL, hbr], ?_⟩
    simp only [KExpr.evalN, lnEval]
    nlinarith
  · refine ⟨((j0 : ℚ), 0), by simp [PCell.loL, hbr], ?_⟩
    simp only [KExpr.evalN, lnEval, hdiv]
    push_cast
    nlinarith
  · by_cases hj : j1 = 0
    · refine ⟨(-(c.kc : ℚ), 1), by simp [PCell.loL, hbr, hj], ?_⟩
      simp only [hj, if_true, KExpr.evalN, lnEval]
      nlinarith
    · refine ⟨(κ0 + (j1 : ℚ) - 1, 0), by simp [PCell.loL, hbr, hj], ?_⟩
      have := h.hk0'
      have hj1 : (1 : ℚ) ≤ j1 := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hj
      simp only [hj, if_false, KExpr.evalN, lnEval, hdiv]
      push_cast [Nat.cast_sub (Nat.one_le_iff_ne_zero.2 hj)]
      nlinarith
  · by_cases hj : j2 = 0
    · refine ⟨(-(c.kc : ℚ), 1), by simp [PCell.loL, hbr, hj], ?_⟩
      simp only [hj, if_true, KExpr.evalN, lnEval]
      nlinarith
    · refine ⟨(κ1 + (j2 : ℚ) - 1, 0), by simp [PCell.loL, hbr, hj], ?_⟩
      have := h.hk1'
      have hj1 : (1 : ℚ) ≤ j2 := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hj
      simp only [hj, if_false, KExpr.evalN, lnEval, hdiv]
      push_cast [Nat.cast_sub (Nat.one_le_iff_ne_zero.2 hj)]
      nlinarith

/-- **Lemma T, prefix cells**: the price of `kbrPre (a n' + nu) j0 [j1, j2]` at a point of the cell in the strip
`n'`. -/
theorem pre_bound (h : CellCtx α κ0 κ1 a b n' c r p m kv) {j0 j1 j2 : ℕ} (hbr : c.br = .pre j0 j1 j2) :
    (((kbrPre (a * n' + c.nu) j0 [j1, j2]).τ.evalN r p m kv : ℕ) : ℚ) ≤
      (2 + 2 * α - c.g1) * r + ((b : ℚ) * n' * c.g1 - c.g0) * p + 3 := by
  obtain ⟨u, hu0, hu1, hru, hdiv, hαr⟩ := h.facts
  have hpQ : (0 : ℚ) < p := by exact_mod_cast h.hp
  obtain ⟨hh, hhm, hhi⟩ := pre_hi h hbr hru hdiv hαr
  obtain ⟨ll, llm, llo⟩ := pre_lo h hbr hu0 hru hdiv hαr
  have hpair := c.ok_pair h.hok hu0 hu1.le hhm llm
  have hline := c.line_le h.hok h.hα hu0 hu1.le
  have hev : (kbrPre (a * n' + c.nu) j0 [j1, j2]).τ.evalN r p m kv =
      2 * r + (2 * m - ((kPreHi (a * n' + c.nu) j0 [j1, j2]).evalN r p m kv -
        (kPreLo (a * n' + c.nu) j0 [j1, j2]).evalN r p m kv)) := rfl
  rw [hev]
  generalize (kPreHi (a * n' + c.nu) j0 [j1, j2]).evalN r p m kv = hi at hhi ⊢
  generalize (kPreLo (a * n' + c.nu) j0 [j1, j2]).evalN r p m kv = lo at llo ⊢
  have hW := natsub_cast_ge hi lo
  generalize hi - lo = W at hW ⊢
  have hpu : (p : ℚ) * u = r - b * n' * p := by rw [hru]; ring
  have hm2 := h.hm2
  have hbnp : (0 : ℚ) ≤ (b : ℚ) * n' * p := by positivity
  have hpl := mul_le_mul_of_nonneg_left hpair hpQ.le
  have hpl2 := mul_le_mul_of_nonneg_left hline hpQ.le
  have hα := h.hα
  have hr0 : (0 : ℚ) ≤ r := Nat.cast_nonneg _
  have hpg : (p : ℚ) * (c.g0 + c.g1 * u) = p * c.g0 + c.g1 * (r - b * n' * p) := by rw [← hpu]; ring
  have hpa : (p : ℚ) * (2 * α * u) = 2 * α * (r - b * n' * p) := by rw [← hpu]; ring
  simp only [lnEval] at hhi llo hpl
  have h2 := natsub_cast_le (2 * m) W ((2 * α - c.g1) * r + ((b : ℚ) * n' * c.g1 - c.g0) * p + 3)
    (by push_cast; nlinarith)
    (by nlinarith [mul_nonneg hα hbnp, mul_nonneg hα hr0])
  push_cast
  linarith

end Pre

/-! ### The `D1x` branch -/

/-- The distance of `m` to the nearest multiple of `p` is `≥ p min (w, 1 - w) - 1/2`. -/
theorem dist_lower {m p n : ℕ} (hp : 0 < p) {w : ℚ} (hm1 : (n : ℚ) * p + p * w - 1 / 2 ≤ m)
    (hm2 : (m : ℚ) ≤ n * p + p * w + 1 / 2) :
    ((p : ℚ) * w - 1 / 2 ≤ ((min (m % p) (p - m % p) : ℕ) : ℚ)) ∨
      ((p : ℚ) * (1 - w) - 1 / 2 ≤ ((min (m % p) (p - m % p) : ℕ) : ℚ)) := by
  have hdm := Nat.div_add_mod m p
  have hρ := Nat.mod_lt m hp
  obtain ⟨q0, hq0⟩ : ∃ q0, q0 = m / p := ⟨_, rfl⟩
  obtain ⟨ρ, hρd⟩ : ∃ ρ, ρ = m % p := ⟨_, rfl⟩
  rw [← hq0, ← hρd] at hdm
  rw [← hρd] at hρ ⊢
  have hdmQ : (p : ℚ) * q0 + ρ = m := by exact_mod_cast hdm
  have hρQ : (ρ : ℚ) < p := by exact_mod_cast hρ
  have hpQ : (0 : ℚ) < p := by exact_mod_cast hp
  have hρ0 : (0 : ℚ) ≤ ρ := Nat.cast_nonneg _
  have hsub : ((p - ρ : ℕ) : ℚ) = p - ρ := Nat.cast_sub hρ.le
  rcases min_choice ρ (p - ρ) with hmin | hmin
  · rw [hmin]
    rcases le_or_gt q0 n with hq | hq
    · left
      have : (p : ℚ) * q0 ≤ p * n := mul_le_mul_of_nonneg_left (by exact_mod_cast hq) hpQ.le
      linarith
    · right
      have hq' : (n : ℚ) + 1 ≤ q0 := by exact_mod_cast hq
      have : (p : ℚ) * (n + 1) ≤ p * q0 := mul_le_mul_of_nonneg_left hq' hpQ.le
      nlinarith
  · rw [hmin, hsub]
    rcases le_or_gt n q0 with hq | hq
    · right
      have hq' : (n : ℚ) ≤ q0 := by exact_mod_cast hq
      have : (p : ℚ) * n ≤ p * q0 := mul_le_mul_of_nonneg_left hq' hpQ.le
      nlinarith
    · left
      have hq' : (q0 : ℚ) + 1 ≤ n := by exact_mod_cast hq
      have : (p : ℚ) * (q0 + 1) ≤ p * n := mul_le_mul_of_nonneg_left hq' hpQ.le
      nlinarith

section D1x

variable {α κ0 κ1 : ℚ} {a b n' : ℕ} {c : PCell} {r p m : ℕ} {kv : ℕ → ℕ}

/-- **Lemma T, `D1x` cells**. -/
theorem d1x_bound (h : CellCtx α κ0 κ1 a b n' c r p m kv) (hbr : c.br = .d1x) :
    ((kD1xE.evalN r p m kv : ℕ) : ℚ) ≤
      (2 + 2 * α - c.g1) * r + ((b : ℚ) * n' * c.g1 - c.g0) * p + 3 := by
  obtain ⟨u, hu0, hu1, hru, hdiv, hαr⟩ := h.facts
  have hpQ : (0 : ℚ) < p := by exact_mod_cast h.hp
  have hm1 := h.hm1
  have hm2 := h.hm2
  push_cast at hαr
  have hd := dist_lower (m := m) (p := p) (n := a * n' + c.nu) h.hp (w := α * u - c.nu)
    (by push_cast; nlinarith) (by push_cast; nlinarith)
  have hpu : (p : ℚ) * u = r - b * n' * p := by rw [hru]; ring
  have hbnp : (0 : ℚ) ≤ (b : ℚ) * n' * p := by positivity
  have hα := h.hα
  have hr0 : (0 : ℚ) ≤ r := Nat.cast_nonneg _
  have hline := c.line_le h.hok h.hα hu0 hu1.le
  have hpl2 := mul_le_mul_of_nonneg_left hline hpQ.le
  have hmem1 : ((-(c.nu : ℚ), α) : ℚ × ℚ) ∈ c.hiL α κ0 κ1 := by simp [PCell.hiL, hbr]
  have hmem2 : (((c.nu : ℚ) + 1, -α) : ℚ × ℚ) ∈ c.hiL α κ0 κ1 := by simp [PCell.hiL, hbr]
  have hmem0 : (((0 : ℚ), (0 : ℚ)) : ℚ × ℚ) ∈ c.loL α κ0 κ1 := by simp [PCell.loL, hbr]
  have p1 := c.ok_pair h.hok hu0 hu1.le hmem1 hmem0
  have p2 := c.ok_pair h.hok hu0 hu1.le hmem2 hmem0
  simp only [lnEval] at p1 p2
  have hD : (p : ℚ) * (c.g0 + c.g1 * u) - 1 / 2 ≤ ((min (m % p) (p - m % p) : ℕ) : ℚ) := by
    rcases hd with hd | hd
    · have := mul_le_mul_of_nonneg_left p1 hpQ.le
      nlinarith
    · have := mul_le_mul_of_nonneg_left p2 hpQ.le
      nlinarith
  have hev : kD1xE.evalN r p m kv = (2 * r + 2 * m) - min (m % p) (p - m % p) := rfl
  have hpg : (p : ℚ) * (c.g0 + c.g1 * u) = p * c.g0 + c.g1 * (r - b * n' * p) := by rw [← hpu]; ring
  have hpa : (p : ℚ) * (2 * α * u) = 2 * α * (r - b * n' * p) := by rw [← hpu]; ring
  rw [hev]
  apply natsub_cast_le
  · simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    nlinarith
  · nlinarith [mul_nonneg hα hbnp, mul_nonneg hα hr0]

end D1x

end CatalanCore.Uniform.Content.BankShared.KTerm
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.pre_bound
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.d1x_bound
