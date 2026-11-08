module

public import CatalanCore.Uniform.Bank.Plane1.Dips.Count
public import CatalanCore.Uniform.Bank.Plane1.Content

@[expose] public section
set_option Elab.async false
set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option maxHeartbeats 1600000

/-! # Dip lines: certificates, the sum bound and the price (wave R1; ledger R01-R03; package R1d, R1e)

A **dip line** `DipLine` is the data of one catalogue branch of a dip row: the class `n` (`3 k_A = n p + ρ`), the period
counts `q = r / p`, `q' = (r + 2 m) / p`, the order `o1 .. o4` of the four breakpoints `k_A, k_B, r mod p, N mod p`
(labels `0 .. 3`) in the period, the four potential tables of `LTab`, and the price `τ = cm m + cg G + c0` with
`G = |k_B - k_A| = p / 6 + O(1)`.  `DipLine.ok` is the finite check: the potentials are feasible (`LTab.ok`), the sorted
order is a permutation, and the affine bound of the sum of potentials (`count_bound`) is below the price. -/

namespace CatalanCore.Uniform.Bank.Plane1.Dips
open Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Uniform.Bank.Plane1

/-- One dip line. -/
structure DipLine where
  n : ℕ
  q : ℕ
  q' : ℕ
  o1 : ℕ
  o2 : ℕ
  o3 : ℕ
  o4 : ℕ
  rc : List ℕ
  cc : List ℕ
  rb : List ℕ
  cb : List ℕ
  cm : ℕ
  cgp : ℕ
  cgn : ℕ
  c0 : ℕ

namespace DipLine
variable (L : DipLine)

/-- The label at slot `j ∈ {1, .., 4}`. -/
def oAt (j : ℕ) : ℕ := if j = 1 then L.o1 else if j = 2 then L.o2 else if j = 3 then L.o3 else L.o4

/-- The slot of a label. -/
def slotOf (l : ℕ) : ℕ := if L.o1 = l then 1 else if L.o2 = l then 2 else if L.o3 = l then 3 else 4

/-- The bit vector of arc `a`. -/
def abits (a : ℕ) : Bits :=
  (decide (L.slotOf 0 ≤ a), decide (L.slotOf 1 ≤ a), decide (L.slotOf 2 ≤ a), decide (L.slotOf 3 ≤ a))

/-- The tables of the line. -/
def tab : LTab := ⟨L.q', (List.range 5).map L.abits, L.rc, L.cc, L.rb, L.cb⟩

/-- The role of the piece `(k, a)`: border from the first arc past `r mod p` in period `q` on. -/
def rl (k a : ℕ) : Bool := decide (L.q < k ∨ (L.q = k ∧ L.slotOf 2 ≤ a))

/-- The labels are a permutation of `0 .. 3`. -/
def permOK : Bool :=
  decide (L.o1 < 4 ∧ L.o2 < 4 ∧ L.o3 < 4 ∧ L.o4 < 4 ∧ L.o1 ≠ L.o2 ∧ L.o1 ≠ L.o3 ∧ L.o1 ≠ L.o4 ∧ L.o2 ≠ L.o3 ∧
    L.o2 ≠ L.o4 ∧ L.o3 ≠ L.o4)

theorem exists_slot (h : L.permOK = true) {l : ℕ} (hl : l < 4) : L.oAt (L.slotOf l) = l ∧ 1 ≤ L.slotOf l ∧ L.slotOf l ≤ 4 := by
  simp only [permOK, decide_eq_true_eq] at h
  obtain ⟨h1, h2, h3, h4, h12, h13, h14, h23, h24, h34⟩ := h
  unfold oAt slotOf
  by_cases e1 : L.o1 = l
  · simp [e1]
  by_cases e2 : L.o2 = l
  · simp [e1, e2]
  by_cases e3 : L.o3 = l
  · simp [e1, e2, e3]
  have e4 : L.o4 = l := by omega
  simp [e1, e2, e3, e4]

end DipLine

namespace DipLine

section Arcs
variable (L : DipLine)

/-- The breakpoint values by label (`0 = k_A`, `1 = k_B`, `2 = r mod p`, `3 = N mod p`). -/
def valL (kA kB xr xN : ℕ) (l : ℕ) : ℕ := if l = 0 then kA else if l = 1 then kB else if l = 2 then xr else xN

/-- The sorted breakpoints `0 = b₀ ≤ b₁ ≤ … ≤ b₄ ≤ b₅ = p`. -/
def bsF (kA kB xr xN p : ℕ) (j : ℕ) : ℕ :=
  if j = 0 then 0 else if j = 5 then p else valL kA kB xr xN (L.oAt j)

theorem bsF_slot (h : L.permOK = true) (kA kB xr xN p : ℕ) {l : ℕ} (hl : l < 4) :
    L.bsF kA kB xr xN p (L.slotOf l) = valL kA kB xr xN l := by
  obtain ⟨h1, h2, h3⟩ := L.exists_slot h hl
  unfold bsF
  rw [if_neg (by omega), if_neg (by omega), h1]

theorem bsF_mono (kA kB xr xN p : ℕ)
    (hs : valL kA kB xr xN L.o1 ≤ valL kA kB xr xN L.o2 ∧ valL kA kB xr xN L.o2 ≤ valL kA kB xr xN L.o3 ∧
      valL kA kB xr xN L.o3 ≤ valL kA kB xr xN L.o4 ∧ valL kA kB xr xN L.o4 ≤ p) :
    ∀ j < 5, L.bsF kA kB xr xN p j ≤ L.bsF kA kB xr xN p (j + 1) := by
  obtain ⟨h1, h2, h3, h4⟩ := hs
  intro j hj
  interval_cases j <;> simp [bsF, oAt, h1, h2, h3, h4]

theorem bit_arc (h : L.permOK = true) (kA kB xr xN p : ℕ)
    (hmono : ∀ j < 5, L.bsF kA kB xr xN p j ≤ L.bsF kA kB xr xN p (j + 1)) {a ξ : ℕ} (ha : a < 5)
    (h1 : L.bsF kA kB xr xN p a ≤ ξ) (h2 : ξ < L.bsF kA kB xr xN p (a + 1)) {l : ℕ} (hl : l < 4) :
    decide (valL kA kB xr xN l ≤ ξ) = decide (L.slotOf l ≤ a) := by
  obtain ⟨-, hs1, hs4⟩ := L.exists_slot h hl
  have e := L.bsF_slot h kA kB xr xN p hl
  by_cases hsa : L.slotOf l ≤ a
  · have : valL kA kB xr xN l ≤ ξ := by
      rw [← e]
      exact le_trans (bs_le _ hmono _ _ hsa (by omega)) h1
    simp [this, hsa]
  · have hge : a + 1 ≤ L.slotOf l := by omega
    have : ¬ valL kA kB xr xN l ≤ ξ := by
      rw [← e]
      have := bs_le _ hmono _ _ hge (by omega)
      omega
    simp [this, hsa]

theorem arcIdx_abits (hnd : L.tab.arcs.Nodup) {a : ℕ} (ha : a < 5) : arcIdx L.tab (L.abits a) = a := by
  have hlen : a < L.tab.arcs.length := by simp [tab, ha]
  have := hnd.idxOf_getElem a hlen
  simpa [arcIdx, tab] using this

end Arcs

end DipLine

namespace DipLine

section ArcFacts
variable (L : DipLine)

theorem nodeBits_arc (hperm : L.permOK = true) {σ : Support} {n p r m t a : ℕ}
    (hs : valL ((n * p + σ.rho) / 3) ((p + 1) / 2) (r % p) ((r + 2 * m) % p) L.o1 ≤
        valL ((n * p + σ.rho) / 3) ((p + 1) / 2) (r % p) ((r + 2 * m) % p) L.o2 ∧
      valL ((n * p + σ.rho) / 3) ((p + 1) / 2) (r % p) ((r + 2 * m) % p) L.o2 ≤
        valL ((n * p + σ.rho) / 3) ((p + 1) / 2) (r % p) ((r + 2 * m) % p) L.o3 ∧
      valL ((n * p + σ.rho) / 3) ((p + 1) / 2) (r % p) ((r + 2 * m) % p) L.o3 ≤
        valL ((n * p + σ.rho) / 3) ((p + 1) / 2) (r % p) ((r + 2 * m) % p) L.o4 ∧
      valL ((n * p + σ.rho) / 3) ((p + 1) / 2) (r % p) ((r + 2 * m) % p) L.o4 ≤ p)
    (ha : a < 5)
    (h1 : L.bsF ((n * p + σ.rho) / 3) ((p + 1) / 2) (r % p) ((r + 2 * m) % p) p a ≤ t % p)
    (h2 : t % p < L.bsF ((n * p + σ.rho) / 3) ((p + 1) / 2) (r % p) ((r + 2 * m) % p) p (a + 1)) :
    nodeBits σ n p r m t = L.abits a := by
  set kA := (n * p + σ.rho) / 3 with hkA
  set kB := (p + 1) / 2 with hkB
  set xr := r % p with hxr
  set xN := (r + 2 * m) % p with hxN
  have hmono := L.bsF_mono kA kB xr xN p hs
  have e0 : decide (kA ≤ t % p) = decide (L.slotOf 0 ≤ a) := by
    simpa [valL] using L.bit_arc hperm kA kB xr xN p hmono ha h1 h2 (show 0 < 4 by norm_num)
  have e1 : decide (kB ≤ t % p) = decide (L.slotOf 1 ≤ a) := by
    simpa [valL] using L.bit_arc hperm kA kB xr xN p hmono ha h1 h2 (show 1 < 4 by norm_num)
  have e2 : decide (xr ≤ t % p) = decide (L.slotOf 2 ≤ a) := by
    simpa [valL] using L.bit_arc hperm kA kB xr xN p hmono ha h1 h2 (show 2 < 4 by norm_num)
  have e3 : decide (xN ≤ t % p) = decide (L.slotOf 3 ≤ a) := by
    simpa [valL] using L.bit_arc hperm kA kB xr xN p hmono ha h1 h2 (show 3 < 4 by norm_num)
  simp only [nodeBits, abits, cA, cB, ← hkA, ← hkB, ← hxr, ← hxN, Prod.mk.injEq]
  exact ⟨e0, e1, e2, e3⟩

/-- Every residue lies in an arc. -/
theorem exists_arc (bs : ℕ → ℕ) (hmono : ∀ j < 5, bs j ≤ bs (j + 1)) (hb0 : bs 0 = 0) {p ξ : ℕ}
    (hb5 : bs 5 = p) (hξ : ξ < p) : ∃ a < 5, bs a ≤ ξ ∧ ξ < bs (a + 1) := by
  by_contra h
  push_neg at h
  have : ∀ j ≤ 5, bs j ≤ ξ := by
    intro j
    induction j with
    | zero => intro _; omega
    | succ j ih => intro hj; exact h j (by omega) (ih (by omega))
  have := this 5 le_rfl
  omega

end ArcFacts

section SumLe
variable (L : DipLine) {σ : Support} {n p r m : ℕ}

/-- The values of the breakpoints, as rationals, in slot order. -/
noncomputable def sv (kA kB xr xN : ℕ) (j : ℕ) : ℚ := (valL kA kB xr xN (L.oAt j) : ℚ)

/-- The affine bound of the sum of the potentials, in slot form. -/
noncomputable def sumBd (kA kB xr xN p : ℕ) : ℚ :=
  let W := fun a => Wcoef L.tab L.rl L.q' (L.slotOf 3) a
  W 0 * (L.sv kA kB xr xN 1 - 0) + W 1 * (L.sv kA kB xr xN 2 - L.sv kA kB xr xN 1) +
    W 2 * (L.sv kA kB xr xN 3 - L.sv kA kB xr xN 2) + W 3 * (L.sv kA kB xr xN 4 - L.sv kA kB xr xN 3) +
    W 4 * ((p : ℚ) - L.sv kA kB xr xN 4) + Sslack L.tab L.rl L.q' (L.slotOf 3)

theorem line_sum_le (hp : 0 < p) (hperm : L.permOK = true) (hnd : L.tab.arcs.Nodup) (hr : r % 2 = 0)
    (hq : r / p = L.q) (hq' : (r + 2 * m) / p = L.q')
    (hs : valL ((n * p + σ.rho) / 3) ((p + 1) / 2) (r % p) ((r + 2 * m) % p) L.o1 ≤
        valL ((n * p + σ.rho) / 3) ((p + 1) / 2) (r % p) ((r + 2 * m) % p) L.o2 ∧
      valL ((n * p + σ.rho) / 3) ((p + 1) / 2) (r % p) ((r + 2 * m) % p) L.o2 ≤
        valL ((n * p + σ.rho) / 3) ((p + 1) / 2) (r % p) ((r + 2 * m) % p) L.o3 ∧
      valL ((n * p + σ.rho) / 3) ((p + 1) / 2) (r % p) ((r + 2 * m) % p) L.o3 ≤
        valL ((n * p + σ.rho) / 3) ((p + 1) / 2) (r % p) ((r + 2 * m) % p) L.o4 ∧
      valL ((n * p + σ.rho) / 3) ((p + 1) / 2) (r % p) ((r + 2 * m) % p) L.o4 ≤ p) :
    ∑ x, rhoF σ n p r m L.tab x + ∑ y, gammaF σ n p r m L.tab y ≤
      L.sumBd ((n * p + σ.rho) / 3) ((p + 1) / 2) (r % p) ((r + 2 * m) % p) p := by
  set kA := (n * p + σ.rho) / 3 with hkA
  set kB := (p + 1) / 2 with hkB
  set xr := r % p with hxr
  set xN := (r + 2 * m) % p with hxN
  have hmono := L.bsF_mono kA kB xr xN p hs
  rw [sum_hyb hr]
  have hb0 : L.bsF kA kB xr xN p 0 = 0 := by simp [bsF]
  have hb5 : L.bsF kA kB xr xN p 5 = p := by simp [bsF]
  obtain ⟨-, hs1, hs4⟩ := L.exists_slot hperm (show 3 < 4 by norm_num)
  have hbN : L.bsF kA kB xr xN p (L.slotOf 3) = xN := by
    rw [L.bsF_slot hperm kA kB xr xN p (by norm_num)]; simp [valL]
  have hN : r + 2 * m = L.q' * p + L.bsF kA kB xr xN p (L.slotOf 3) := by
    have h1 := Nat.div_add_mod (r + 2 * m) p
    rw [hq'] at h1
    rw [hbN, Nat.mul_comm L.q' p]
    omega
  have hbits : ∀ t a, a < 5 → L.bsF kA kB xr xN p a ≤ t % p → t % p < L.bsF kA kB xr xN p (a + 1) →
      nodeBits σ n p r m t = L.abits a := fun t a ha h1 h2 =>
    L.nodeBits_arc hperm hs ha h1 h2
  have hcount := count_period (T := L.tab) (σ := σ) (n := n) (r := r) (m := m) hp (L.bsF kA kB xr xN p) hmono hb0 hb5
    L.q' (L.slotOf 3) (by omega) hN L.rl
    (fun t ht a ha h1 h2 => by rw [hbits t a ha h1 h2]; exact L.arcIdx_abits hnd ha)
    (fun t ht a ha h1 h2 => by
      have eR : decide (xr ≤ t % p) = decide (L.slotOf 2 ≤ a) := by
        simpa [valL] using L.bit_arc hperm kA kB xr xN p hmono ha h1 h2 (show 2 < 4 by norm_num)
      have et := Nat.div_add_mod t p
      have er := Nat.div_add_mod r p
      rw [hq] at er
      have hxp : r % p < p := Nat.mod_lt r hp
      have hxi : t % p < p := Nat.mod_lt t hp
      unfold rl
      rcases lt_trichotomy L.q (t / p) with hlt | heq | hgt
      · have hm1 : p * (L.q + 1) ≤ p * (t / p) := Nat.mul_le_mul_left p hlt
        rw [Nat.mul_succ] at hm1
        have : r ≤ t := by omega
        simp [hlt, this]
      · rw [← heq] at et
        have : r ≤ t ↔ xr ≤ t % p := by omega
        simp only [heq, decide_eq_decide.2 this]
        rw [eR]
        simp [heq]
      · have hm1 : p * (t / p + 1) ≤ p * L.q := Nat.mul_le_mul_left p hgt
        rw [Nat.mul_succ] at hm1
        have : ¬ r ≤ t := by omega
        simp [hgt.not_gt, this, hgt.ne'])
  rw [collect L.tab L.rl _ L.q' (L.slotOf 3) (by omega)] at hcount
  refine le_trans hcount (le_of_eq ?_)
  unfold sumBd sv
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  simp only [hb0, hb5, bsF, oAt]
  norm_num

end SumLe

end DipLine

/-- An affine form `A m + B G + C + D e`. -/
structure Aff where
  A : ℚ
  B : ℚ
  C : ℚ
  D : ℚ

namespace Aff
def ev (x : Aff) (m G e : ℚ) : ℚ := x.A * m + x.B * G + x.C + x.D * e
end Aff

namespace DipLine

section Affine
variable (L : DipLine)

/-- `β`: `k_B = 3 G + β`, `k_A = α G + β`, `p = 6 G + 2 β - 1`, with `G = |k_B - k_A|` (class `n`, shift `ρ`). -/
def beta (n ρ : ℕ) : ℚ := if n = 1 then (ρ : ℚ) - 1 else 2 - (ρ : ℚ)
def alphaA (n : ℕ) : ℚ := if n = 1 then 2 else 4

/-- The label `l` as an affine form (`r = 12 m + e`, `q = r / p`, `q' = N / p`). -/
def labAff (n ρ q q' : ℕ) (l : ℕ) : Aff :=
  if l = 0 then ⟨0, alphaA n, beta n ρ, 0⟩
  else if l = 1 then ⟨0, 3, beta n ρ, 0⟩
  else if l = 2 then ⟨12, -6 * (q : ℚ), -(q : ℚ) * (2 * beta n ρ - 1), 1⟩
  else ⟨14, -6 * (q' : ℚ), -(q' : ℚ) * (2 * beta n ρ - 1), 1⟩

/-- `p` as an affine form. -/
def pAff (n ρ : ℕ) : Aff := ⟨0, 6, 2 * beta n ρ - 1, 0⟩

/-- The slot `j ∈ 0 .. 5` as an affine form. -/
def slotAff (ρ : ℕ) (j : ℕ) : Aff :=
  if j = 0 then ⟨0, 0, 0, 0⟩ else if j = 5 then pAff L.n ρ else labAff L.n ρ L.q L.q' (L.oAt j)

/-- The total affine form of the bound. -/
noncomputable def totAff (ρ : ℕ) : Aff :=
  let W := fun a => Wcoef L.tab L.rl L.q' (L.slotOf 3) a
  ⟨∑ a ∈ range 5, W a * ((L.slotAff ρ (a + 1)).A - (L.slotAff ρ a).A),
   ∑ a ∈ range 5, W a * ((L.slotAff ρ (a + 1)).B - (L.slotAff ρ a).B),
   ∑ a ∈ range 5, W a * ((L.slotAff ρ (a + 1)).C - (L.slotAff ρ a).C) +
     Sslack L.tab L.rl L.q' (L.slotOf 3),
   ∑ a ∈ range 5, W a * ((L.slotAff ρ (a + 1)).D - (L.slotAff ρ a).D)⟩

/-- The price check: coefficients of `m` and `G` below the price and the constant at the worse end of `e ∈ [-5, 6]`. -/
noncomputable def affOK (ρ : ℕ) : Bool :=
  decide ((L.totAff ρ).A ≤ L.cm ∧ (L.totAff ρ).B ≤ (L.cgp : ℚ) - L.cgn ∧
    (L.totAff ρ).C + max (-5 * (L.totAff ρ).D) (6 * (L.totAff ρ).D) ≤ L.c0)

theorem sumBd_eq_ev (hperm : L.permOK = true) (ρ : ℕ) (kA kB xr xN p : ℕ) (m G e : ℚ)
    (h0 : (kA : ℚ) = (labAff L.n ρ L.q L.q' 0).ev m G e) (h1 : (kB : ℚ) = (labAff L.n ρ L.q L.q' 1).ev m G e)
    (h2 : (xr : ℚ) = (labAff L.n ρ L.q L.q' 2).ev m G e) (h3 : (xN : ℚ) = (labAff L.n ρ L.q L.q' 3).ev m G e)
    (hp : (p : ℚ) = (pAff L.n ρ).ev m G e) :
    L.sumBd kA kB xr xN p = (L.totAff ρ).ev m G e := by
  have hsv : ∀ j, 1 ≤ j → j ≤ 4 → L.sv kA kB xr xN j = (L.slotAff ρ j).ev m G e := by
    intro j hj1 hj4
    unfold sv slotAff
    rw [if_neg (by omega), if_neg (by omega)]
    have hlt : L.oAt j < 4 := by
      simp only [permOK, decide_eq_true_eq] at hperm
      obtain ⟨h1, h2, h3, h4, -⟩ := hperm
      unfold oAt
      split_ifs <;> assumption
    unfold valL
    split_ifs with a b c
    · rw [a]; exact h0
    · rw [b]; exact h1
    · rw [c]; exact h2
    · have : L.oAt j = 3 := by omega
      rw [this]; exact h3
  have hs5 : (L.slotAff ρ 5).ev m G e = p := by rw [hp]; simp [slotAff]
  have hs0 : (L.slotAff ρ 0) = ⟨0, 0, 0, 0⟩ := by simp [slotAff]
  unfold sumBd totAff
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [hsv 1 (by norm_num) (by norm_num), hsv 2 (by norm_num) (by norm_num), hsv 3 (by norm_num) (by norm_num),
    hsv 4 (by norm_num) (by norm_num), ← hs5]
  rw [hs0]
  simp only [Aff.ev]
  norm_num
  ring

end Affine

end DipLine

namespace DipLine

theorem affOK_bound (L : DipLine) {ρ : ℕ} (hok : L.affOK ρ = true) (m G e : ℚ) (hm : 0 ≤ m) (hG : 0 ≤ G)
    (he1 : -5 ≤ e) (he2 : e ≤ 6) :
    (L.totAff ρ).ev m G e ≤ (L.cm : ℚ) * m + ((L.cgp : ℚ) - L.cgn) * G + L.c0 := by
  unfold affOK at hok
  obtain ⟨hA, hB, hC⟩ := of_decide_eq_true hok
  unfold Aff.ev
  have hD : (L.totAff ρ).D * e ≤ max (-5 * (L.totAff ρ).D) (6 * (L.totAff ρ).D) := by
    rcases le_total 0 (L.totAff ρ).D with h | h
    · exact le_trans (by nlinarith) (le_max_right _ _)
    · exact le_trans (by nlinarith) (le_max_left _ _)
  nlinarith [mul_le_mul_of_nonneg_right hA hm, mul_le_mul_of_nonneg_right hB hG]

end DipLine

namespace DipLine
open CatalanCore.Uniform.Content.BankShared.KTerm

section Branch
variable (L : DipLine)

/-- `(c_r, c_p, c_m, c_{k_0}, c_{k_1})` of the breakpoint with label `l`. -/
def lVec (q q' : ℕ) (l : ℕ) : ℤ × ℤ × ℤ × ℤ × ℤ :=
  if l = 0 then (0, 0, 0, 1, 0) else if l = 1 then (0, 0, 0, 0, 1)
  else if l = 2 then (1, -(q : ℤ), 0, 0, 0) else (1, -(q' : ℤ), 2, 0, 0)

/-- `value(l') - value(l) ≥ 0`. -/
def chainCond (q q' l l' : ℕ) : KCond :=
  ⟨(lVec q q' l').1 - (lVec q q' l).1, (lVec q q' l').2.1 - (lVec q q' l).2.1,
    (lVec q q' l').2.2.1 - (lVec q q' l).2.2.1, [(lVec q q' l').2.2.2.1 - (lVec q q' l).2.2.2.1,
      (lVec q q' l').2.2.2.2 - (lVec q q' l).2.2.2.2], 0, false⟩

/-- The class condition: `k_A < k_B` (class `n = 1`) or `k_A > k_B` (class `n = 2`). -/
def classCond (n : ℕ) : KCond :=
  if n = 1 then ⟨0, 0, 0, [-1, 1], -1, false⟩ else ⟨0, 0, 0, [1, -1], -1, false⟩

/-- The validity conditions of a dip line. -/
def conds (ρ : ℕ) : List KCond :=
  [⟨1, -(L.q : ℤ), 0, [0, 0], 0, false⟩, ⟨-1, (L.q : ℤ) + 1, 0, [0, 0], -1, false⟩,
   ⟨1, -(L.q' : ℤ), 2, [0, 0], 0, false⟩, ⟨-1, (L.q' : ℤ) + 1, -2, [0, 0], -1, false⟩,
   classCond L.n, ⟨0, 1, -2, [0, 0], -1, false⟩,
   chainCond L.q L.q' L.o1 L.o2, chainCond L.q L.q' L.o2 L.o3, chainCond L.q L.q' L.o3 L.o4]

open KExpr in
/-- `G = |k_B - k_A|` as an expression. -/
def gExpr : KExpr := if L.n = 1 then tsub (vk 1) (vk 0) else tsub (vk 0) (vk 1)

open KExpr in
/-- The price `cm m + cgp G + c0 - cgn G`. -/
def tau : KExpr := tsub (add (add (smul L.cm vm) (smul L.cgp L.gExpr)) (cst L.c0)) (smul L.cgn L.gExpr)

/-- The catalogue branch (debit 2). -/
def toBranch (ρ : ℕ) : KBranch := ⟨L.tau, L.conds ρ, 2⟩

/-- The finite check of a line. -/
noncomputable def ok (ρ : ℕ) (a b c : ℤ) : Bool :=
  L.tab.ok a b c L.n && L.permOK && decide L.tab.arcs.Nodup && decide (L.n = 1 ∨ L.n = 2) &&
    decide (L.q' = L.q ∨ L.q' = L.q + 1) && L.affOK ρ

end Branch

end DipLine

namespace DipLine
open CatalanCore.Uniform.Content.BankShared.KTerm

theorem val_lin {l : ℕ} (hl : l < 4) (q q' r p m kA kB xr xN : ℕ) (hxr : (xr : ℤ) = r - q * p)
    (hxN : (xN : ℤ) = r + 2 * m - q' * p) :
    ((valL kA kB xr xN l : ℕ) : ℤ) = (lVec q q' l).1 * r + (lVec q q' l).2.1 * p + (lVec q q' l).2.2.1 * m +
      (lVec q q' l).2.2.2.1 * kA + (lVec q q' l).2.2.2.2 * kB := by
  interval_cases l <;> simp [valL, lVec] <;> linarith

theorem chainCond_sound {q q' l l' : ℕ} (hl : l < 4) (hl' : l' < 4) {r p m : ℕ} {kv : ℕ → ℕ} (xr xN : ℕ)
    (hxr : (xr : ℤ) = r - q * p) (hxN : (xN : ℤ) = r + 2 * m - q' * p)
    (h : (chainCond q q' l l').Holds r p m kv) :
    valL (kv 0) (kv 1) xr xN l ≤ valL (kv 0) (kv 1) xr xN l' := by
  have v1 := val_lin hl q q' r p m (kv 0) (kv 1) xr xN hxr hxN
  have v2 := val_lin hl' q q' r p m (kv 0) (kv 1) xr xN hxr hxN
  simp only [KCond.Holds, KCond.L, chainCond, dot, Bool.false_eq_true, if_false] at h
  have : (valL (kv 0) (kv 1) xr xN l : ℤ) ≤ valL (kv 0) (kv 1) xr xN l' := by
    rw [v1, v2]
    linarith
  exact_mod_cast this

end DipLine

namespace DipLine
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared CatalanCore.Uniform.Content.Shape
  CatalanCore.Uniform.Content.Member CatalanCore.Rect

theorem nat_sub_le_q (X Y : ℕ) : (X : ℚ) - Y ≤ ((X - Y : ℕ) : ℚ) := by
  rcases le_total Y X with h | h
  · rw [Nat.cast_sub h]
  · rw [Nat.sub_eq_zero_of_le h]
    have : (X : ℚ) ≤ Y := by exact_mod_cast h
    simp; linarith

/-- **A dip line is a valid catalogue branch** for the plane frame `(a, b, c)` on the support `σ`. -/
theorem line_valid (σ : Support) (a b c : ℤ) (h0 : a + b + c = 0) (depth Q0 Pbad N0 : ℕ) (hQ0 : 3 ≤ Q0)
    (hP : 6 ≤ Pbad) (L : DipLine) (hL : L.ok σ.rho a b c = true) :
    KCatValid planeC planeC_pos (planeFrame σ a b c h0) depth (planeBundle σ a b c h0).shifts Q0 Pbad N0
      [L.toBranch σ.rho] := by
  intro br hbr i hi hr0 p hpf hPb _ hqN kv hroots hcond
  rw [List.mem_singleton] at hbr
  subst hbr
  obtain ⟨r, S⟩ := i
  have hr : r % 2 = 0 := hi.2
  have hr0' : 0 < r := hr0
  unfold ok at hL
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hL
  obtain ⟨⟨⟨⟨⟨hok, hperm⟩, hnd⟩, hn⟩, hq'⟩, haff⟩ := hL
  have h7 : 7 ≤ p := by omega
  have hp0 : 0 < p := by omega
  set m := (altGeom planeC planeC_pos).borderSize r with hmdef
  have hsq : 3 * (r + 2 * m) < p * p := lt_of_le_of_lt (Nat.mul_le_mul_right _ hQ0) hqN
  obtain ⟨⟨jA, eA, hjA0, hjA3, hkA0, hkAp⟩, ⟨jB, eB, hjB0, hjB2, hkB0, hkBp⟩⟩ :=
    (planeBundle σ a b c h0).roots_facts hroots
  have eA' : 3 * kv 0 = jA * p + σ.rho := eA
  have eB' : 2 * kv 1 = jB * p + 1 := eB
  have jB1 : jB = 1 := by omega
  subst jB1
  obtain ⟨hb1, hb2⟩ := plane_border (r := r) hr
  -- the conditions
  have hc := fun (cd : KCond) (hmem : cd ∈ L.conds σ.rho) => hcond cd hmem
  have c1 := hc ⟨1, -(L.q : ℤ), 0, [0, 0], 0, false⟩ (by simp [conds])
  have c2 := hc ⟨-1, (L.q : ℤ) + 1, 0, [0, 0], -1, false⟩ (by simp [conds])
  have c3 := hc ⟨1, -(L.q' : ℤ), 2, [0, 0], 0, false⟩ (by simp [conds])
  have c4 := hc ⟨-1, (L.q' : ℤ) + 1, -2, [0, 0], -1, false⟩ (by simp [conds])
  have c5 := hc (classCond L.n) (by simp [conds])
  have c7 := hc ⟨0, 1, -2, [0, 0], -1, false⟩ (by simp [conds])
  have c8 := hc (chainCond L.q L.q' L.o1 L.o2) (by simp [conds])
  have c9 := hc (chainCond L.q L.q' L.o2 L.o3) (by simp [conds])
  have c10 := hc (chainCond L.q L.q' L.o3 L.o4) (by simp [conds])
  simp only [KCond.Holds, KCond.L, dot, Bool.false_eq_true, if_false] at c1 c2 c3 c4 c7
  simp only [zero_add] at c1 c2 c3 c4 c7
  have hmp : 2 * m < p := by omega
  have hq1 : L.q * p ≤ r := by zify; linarith
  have hq2 : r < (L.q + 1) * p := by zify; push_cast; linarith
  have hq3 : L.q' * p ≤ r + 2 * m := by zify; linarith
  have hq4 : r + 2 * m < (L.q' + 1) * p := by zify; push_cast; linarith
  have hqd : r / p = L.q := Nat.div_eq_of_lt_le hq1 hq2
  have hqd' : (r + 2 * m) / p = L.q' := Nat.div_eq_of_lt_le hq3 hq4
  have hcls : 3 * kv 0 = L.n * p + σ.rho := by
    rcases hn with h1 | h2
    · simp only [classCond, h1, if_true, KCond.Holds, KCond.L, dot, Bool.false_eq_true, if_false, zero_add] at c5
      have c5' : kv 0 + 1 ≤ kv 1 := by omega
      have hρ1 := rho_pos σ
      have hρ2 := rho_le σ
      rw [h1]
      interval_cases jA <;> omega
    · have h1 : ¬ L.n = 1 := by omega
      simp only [classCond, h1, if_false, KCond.Holds, KCond.L, dot, Bool.false_eq_true, zero_add] at c5
      have c5' : kv 1 + 1 ≤ kv 0 := by omega
      have hρ1 := rho_pos σ
      have hρ2 := rho_le σ
      rw [h2]
      interval_cases jA <;> omega
  have h3 : 3 ∣ L.n * p + σ.rho := ⟨kv 0, hcls.symm⟩
  have hkA : kv 0 = (L.n * p + σ.rho) / 3 := by omega
  have hkB : kv 1 = (p + 1) / 2 := by omega
  have hxr : (((r % p : ℕ)) : ℤ) = r - L.q * p := by
    have h := Nat.div_add_mod r p
    rw [hqd] at h
    have h' : ((p * L.q + r % p : ℕ) : ℤ) = r := by rw [h]
    rw [Nat.cast_add, Nat.cast_mul] at h'
    linarith
  have hxN : ((((r + 2 * m) % p : ℕ)) : ℤ) = r + 2 * m - L.q' * p := by
    have h := Nat.div_add_mod (r + 2 * m) p
    rw [hqd'] at h
    have h' : ((p * L.q' + (r + 2 * m) % p : ℕ) : ℤ) = r + 2 * m := by rw [h]; push_cast; ring
    rw [Nat.cast_add, Nat.cast_mul] at h'
    linarith
  have hperm' := hperm
  simp only [permOK, decide_eq_true_eq] at hperm'
  obtain ⟨po1, po2, po3, po4, -⟩ := hperm'
  have hs : valL ((L.n * p + σ.rho) / 3) ((p + 1) / 2) (r % p) ((r + 2 * m) % p) L.o1 ≤
        valL ((L.n * p + σ.rho) / 3) ((p + 1) / 2) (r % p) ((r + 2 * m) % p) L.o2 ∧
      valL ((L.n * p + σ.rho) / 3) ((p + 1) / 2) (r % p) ((r + 2 * m) % p) L.o2 ≤
        valL ((L.n * p + σ.rho) / 3) ((p + 1) / 2) (r % p) ((r + 2 * m) % p) L.o3 ∧
      valL ((L.n * p + σ.rho) / 3) ((p + 1) / 2) (r % p) ((r + 2 * m) % p) L.o3 ≤
        valL ((L.n * p + σ.rho) / 3) ((p + 1) / 2) (r % p) ((r + 2 * m) % p) L.o4 ∧
      valL ((L.n * p + σ.rho) / 3) ((p + 1) / 2) (r % p) ((r + 2 * m) % p) L.o4 ≤ p := by
    rw [← hkA, ← hkB]
    refine ⟨chainCond_sound po1 po2 _ _ hxr hxN c8, chainCond_sound po2 po3 _ _ hxr hxN c9,
      chainCond_sound po3 po4 _ _ hxr hxN c10, ?_⟩
    have h1 := Nat.mod_lt r hp0
    have h2 := Nat.mod_lt (r + 2 * m) hp0
    have : ∀ l < 4, valL (kv 0) (kv 1) (r % p) ((r + 2 * m) % p) l ≤ p := by
      intro l hl
      interval_cases l <;> simp [valL] <;> omega
    exact this _ po4
  have hρ1 := rho_pos σ
  have hρ2 := rho_le σ
  haveI := hpf
  have hyb := hybPiv_plane (σ := σ) (a := a) (b := b) (c := c) (h0 := h0) (p := p) (n := L.n)
    (fl := flagB a b c L.n) (r := r) (m := m) h7 hn h3 (flagB_ok a b c L.n) hsq hmp
  have hQ := altGeom_member_commonMinor planeC planeC_pos (planeFrame σ a b c h0) depth hr S
  have hcard : (retainedFin (altGeom_hybShape planeC planeC_pos hr) S).card = S.card := card_retainedFin _ _
  have hdel : delCount (altGeom planeC planeC_pos) ⟨r, S⟩ = r - S.card := by
    have hC : (((altGeom planeC planeC_pos).geometry r).C).card = r := by
      rw [altGeom_C]; exact Finset.card_range r
    unfold delCount
    show (((altGeom planeC planeC_pos).geometry r).C).card - S.card = r - S.card
    rw [hC]
  -- feasibility of the potentials
  have hmono := L.bsF_mono ((L.n * p + σ.rho) / 3) ((p + 1) / 2) (r % p) ((r + 2 * m) % p) p hs
  have hb0 : L.bsF ((L.n * p + σ.rho) / 3) ((p + 1) / 2) (r % p) ((r + 2 * m) % p) p 0 = 0 := by simp [bsF]
  have hb5 : L.bsF ((L.n * p + σ.rho) / 3) ((p + 1) / 2) (r % p) ((r + 2 * m) % p) p 5 = p := by simp [bsF]
  have hnodes : ∀ t < r + 2 * m, nodeBits σ L.n p r m t ∈ L.tab.arcs := by
    intro t ht
    obtain ⟨a', ha', h1, h2⟩ := exists_arc _ hmono hb0 hb5 (Nat.mod_lt t hp0)
    rw [L.nodeBits_arc hperm hs ha' h1 h2]
    simp only [tab, List.mem_map, List.mem_range]
    exact ⟨a', ha', rfl⟩
  have hfeas := fun x y => feasible_of_ok (σ := σ) (a := a) (b := b) (c := c) (h0 := h0) (p := p) (n := L.n)
    (r := r) (m := m) h7 hn h3 hmp hr L.tab hok (by rw [hqd']; exact le_rfl) hnodes x y
  have hsum := L.line_sum_le hp0 hperm hnd hr hqd hqd' hs
  -- the numbers
  have hGdef : L.gExpr.evalN r p m kv = if L.n = 1 then kv 1 - kv 0 else kv 0 - kv 1 := by
    unfold gExpr; split_ifs <;> simp [KExpr.evalN]
  have hrat : ((kv 0 : ℕ) : ℚ) = (alphaA L.n) * (L.gExpr.evalN r p m kv : ℕ) + beta L.n σ.rho ∧
      ((kv 1 : ℕ) : ℚ) = 3 * (L.gExpr.evalN r p m kv : ℕ) + beta L.n σ.rho ∧
      (p : ℚ) = 6 * (L.gExpr.evalN r p m kv : ℕ) + (2 * beta L.n σ.rho - 1) := by
    rcases hn with hn1 | hn2
    · rw [hGdef, if_pos hn1]
      rw [hn1] at hcls
      have e0 : ((kv 0 : ℕ) : ℤ) = 2 * ((kv 1 - kv 0 : ℕ) : ℤ) + σ.rho - 1 := by omega
      have e1 : ((kv 1 : ℕ) : ℤ) = 3 * ((kv 1 - kv 0 : ℕ) : ℤ) + σ.rho - 1 := by omega
      have e2 : ((p : ℕ) : ℤ) = 6 * ((kv 1 - kv 0 : ℕ) : ℤ) + 2 * σ.rho - 3 := by omega
      have f0 : ((kv 0 : ℕ) : ℚ) = 2 * ((kv 1 - kv 0 : ℕ) : ℚ) + σ.rho - 1 := by exact_mod_cast e0
      have f1 : ((kv 1 : ℕ) : ℚ) = 3 * ((kv 1 - kv 0 : ℕ) : ℚ) + σ.rho - 1 := by exact_mod_cast e1
      have f2 : ((p : ℕ) : ℚ) = 6 * ((kv 1 - kv 0 : ℕ) : ℚ) + 2 * σ.rho - 3 := by exact_mod_cast e2
      simp only [alphaA, beta, hn1, if_true]
      refine ⟨by rw [f0]; ring, by rw [f1]; ring, by rw [f2]; ring⟩
    · have hn1 : ¬ L.n = 1 := by omega
      rw [hGdef, if_neg hn1]
      rw [hn2] at hcls
      have e0 : ((kv 0 : ℕ) : ℤ) = 4 * ((kv 0 - kv 1 : ℕ) : ℤ) + 2 - σ.rho := by omega
      have e1 : ((kv 1 : ℕ) : ℤ) = 3 * ((kv 0 - kv 1 : ℕ) : ℤ) + 2 - σ.rho := by omega
      have e2 : ((p : ℕ) : ℤ) = 6 * ((kv 0 - kv 1 : ℕ) : ℤ) + 3 - 2 * σ.rho := by omega
      have f0 : ((kv 0 : ℕ) : ℚ) = 4 * ((kv 0 - kv 1 : ℕ) : ℚ) + 2 - σ.rho := by exact_mod_cast e0
      have f1 : ((kv 1 : ℕ) : ℚ) = 3 * ((kv 0 - kv 1 : ℕ) : ℚ) + 2 - σ.rho := by exact_mod_cast e1
      have f2 : ((p : ℕ) : ℚ) = 6 * ((kv 0 - kv 1 : ℕ) : ℚ) + 3 - 2 * σ.rho := by exact_mod_cast e2
      simp only [alphaA, beta, hn1, if_false]
      refine ⟨by rw [f0]; ring, by rw [f1]; ring, by rw [f2]; ring⟩
  obtain ⟨hk0, hk1, hpp⟩ := hrat
  set Gn := L.gExpr.evalN r p m kv with hGn
  have he1 : (-5 : ℚ) ≤ (r : ℚ) - 12 * m := by
    have : (12 * m : ℤ) ≤ r + 5 := by omega
    have h' : ((12 * m : ℤ) : ℚ) ≤ ((r + 5 : ℤ) : ℚ) := by exact_mod_cast this
    push_cast at h'; linarith
  have he2 : (r : ℚ) - 12 * m ≤ 6 := by
    have : (r : ℤ) ≤ 12 * m + 6 := by omega
    have h' : ((r : ℤ) : ℚ) ≤ ((12 * m + 6 : ℤ) : ℚ) := by exact_mod_cast this
    push_cast at h'; linarith
  have hxrQ : (((r % p : ℕ)) : ℚ) = (r : ℚ) - L.q * p := by
    have : (((r % p : ℕ)) : ℤ) = r - L.q * p := hxr
    exact_mod_cast this
  have hxNQ : ((((r + 2 * m) % p : ℕ)) : ℚ) = (r : ℚ) + 2 * m - L.q' * p := by
    have : ((((r + 2 * m) % p : ℕ)) : ℤ) = r + 2 * m - L.q' * p := hxN
    exact_mod_cast this
  have hev := L.sumBd_eq_ev hperm σ.rho ((L.n * p + σ.rho) / 3) ((p + 1) / 2) (r % p) ((r + 2 * m) % p) p
    (m : ℚ) (Gn : ℚ) ((r : ℚ) - 12 * m)
    (by rw [← hkA, hk0]; simp [labAff, Aff.ev, alphaA])
    (by rw [← hkB, hk1]; simp [labAff, Aff.ev])
    (by rw [hxrQ, hpp]; simp [labAff, Aff.ev]; ring)
    (by rw [hxNQ, hpp]; simp [labAff, Aff.ev]; ring)
    (by rw [hpp]; simp [pAff, Aff.ev])
  have haffb := L.affOK_bound haff (m : ℚ) (Gn : ℚ) ((r : ℚ) - 12 * m) (Nat.cast_nonneg _) (Nat.cast_nonneg _) he1 he2
  have hXYq : ((L.cm : ℚ) * m + L.cgp * Gn + L.c0) - L.cgn * Gn ≤
      (((L.cm * m + L.cgp * Gn + L.c0) - L.cgn * Gn : ℕ) : ℚ) := by
    have := nat_sub_le_q (L.cm * m + L.cgp * Gn + L.c0) (L.cgn * Gn)
    push_cast at this
    exact this
  have hτ : L.tau.evalN r p m kv = (L.cm * m + L.cgp * Gn + L.c0) - L.cgn * Gn := by
    simp [tau, KExpr.evalN, hGn]
  refine ⟨L.tau.evalN r p m kv + 2 * (r - S.card), ?_, ?_⟩
  · have hG0 : GLE p (L.tau.evalN r p m kv + 2 * (r - S.card))
        (commonMinorPoly (planeFrame σ a b c h0) r m
          (retainedFin (altGeom_hybShape planeC planeC_pos hr) S)) := by
      refine member_gle hyb (retainedFin (altGeom_hybShape planeC planeC_pos hr) S) (rhoF σ L.n p r m L.tab)
        (gammaF σ L.n p r m L.tab) ?_ ?_ hfeas ?_
      · intro x; cases x <;> simp [rhoF]
      · intro x; cases x <;> simp [gammaF]
      · rw [hcard]
        have h1 := le_trans hsum (le_of_eq hev)
        have h2 := le_trans h1 haffb
        have h3 : ∑ x, rhoF σ L.n p r m L.tab x + ∑ y, gammaF σ L.n p r m L.tab y ≤ (L.tau.evalN r p m kv : ℚ) := by
          rw [hτ]; push_cast at h2 ⊢; linarith
        push_cast
        linarith
    exact hQ ▸ hG0
  · rw [hdel]
    exact le_rfl

end DipLine

end CatalanCore.Uniform.Bank.Plane1.Dips
