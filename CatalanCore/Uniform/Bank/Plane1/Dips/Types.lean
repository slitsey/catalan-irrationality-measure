module

public import CatalanCore.Uniform.Bank.Plane1.Dips.PlanePiv

@[expose] public section
set_option Elab.async false
set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option maxHeartbeats 1600000

/-! # The node types of a dip line and the feasibility check (wave R1; ledger R01-R03; package R1c)

A **line certificate** assigns to every node `t < N = r + 2 m` a potential that depends only on its **type**
`(role, q, arc, parity)`: `q = t / p`, the arc is the bit vector `(eA, eB, eR, eN) = ([kA ≤ ξ], [kB ≤ ξ], [r mod p ≤ ξ],
[N mod p ≤ ξ])`, `ξ = t mod p` (an arc is a maximal interval of `ξ` between the breakpoints `kA, kB, r mod p, N mod p`),
the parity is that of `t`, the role says common (`t < r`: a row and a column) or border (`t ≥ r`: row if `t` even,
column if `t` odd).

`LTab.ok` is the finite Boolean check that `Wty ≤ ρ + γ` on every pair of types, where `Wty` is the weight of
Lemma 5.1' at the type level: the in-fibre weight (`inW`, only for pairs of equal arc and compatible parity: two nodes
with the same `ξ`) and the off-fibre weight `offW = [V* ≠ V*]`, with the pivot pair (`x` and `x - p`) exempt from the
in-fibre weight.  The pivot rule is canonical (`flagB`: pivot whenever admissible).  `feasible_of_ok` is the
soundness: `ok = true` gives `Wd ≤ ρ x + γ y` for every pair of the hybrid, the hypothesis `hfeas` of `member_gle`. -/

namespace CatalanCore.Uniform.Bank.Plane1.Dips
open Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Uniform.Bank.Plane1

/-! ### Definitions -/

/-- The canonical pivot rule on cells: pivot whenever admissible (`FlagOK`), `λ` with denominator dividing `30^6`. -/
noncomputable def flagB (a b c : ℤ) (n q : ℕ) (eA eB : Bool) : Bool :=
  decide (1 ≤ q) && decide (Utab a b c n (q - 1) eA eB ≠ 0) && decide (lamTab a b c n q eA eB ≠ 1) &&
    decide ((lamTab a b c n q eA eB).den ∣ 30 ^ 6)

theorem smooth5_of_den {x : ℚ} (h : x.den ∣ 30 ^ 6) : Smooth5 x := by
  obtain ⟨e, he⟩ := h
  refine ⟨6, x.num * e, ?_⟩
  have hd : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.den_nz
  have he' : ((30 : ℚ) ^ 6) = x.den * e := by exact_mod_cast he
  have he0 : (e : ℚ) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at he'
    norm_num at he'
  push_cast
  rw [he', mul_div_mul_right _ _ he0, Rat.num_div_den]

theorem flagB_ok (a b c : ℤ) (n : ℕ) : FlagOK a b c n (flagB a b c n) := by
  refine ⟨fun q eA eB h => ?_⟩
  simp only [flagB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, smooth5_of_den h4⟩

/-- The four bits of a node: `[kA ≤ ξ]`, `[kB ≤ ξ]`, `[r mod p ≤ ξ]`, `[N mod p ≤ ξ]`, `ξ = t mod p`, `N = r + 2 m`. -/
abbrev Bits := Bool × Bool × Bool × Bool

def nodeBits (σ : Support) (n p r m t : ℕ) : Bits :=
  (cA σ n p t, cB p t, decide (r % p ≤ t % p), decide ((r + 2 * m) % p ≤ t % p))

/-- The tables of a line: the list of arcs and the potentials of the four kinds of lines, indexed `(q, arc, parity)`. -/
structure LTab where
  qmax : ℕ
  arcs : List Bits
  rc : List ℕ
  cc : List ℕ
  rb : List ℕ
  cb : List ℕ

/-- Table lookup. -/
def potAt (l : List ℕ) (A k a : ℕ) (par : Bool) : ℕ := l.getD ((k * A + a) * 2 + (if par then 1 else 0)) 0

section TypeWeights

variable (a b c : ℤ) (n : ℕ)

/-- A node of a border line is pivoted when it lies in a flagged cell. -/
noncomputable def pivB (border : Bool) (q : ℕ) (eA eB : Bool) : Bool := border && flagB a b c n q eA eB

/-- The effective level of a node of the given role at the cell. -/
noncomputable def levT (border : Bool) (q : ℕ) (eA eB : Bool) : ℚ :=
  if border then (if flagB a b c n q eA eB then vsTab a b c n q eA eB else Vtab a b c n q eA eB)
  else Vtab a b c n q eA eB

/-- The in-fibre weight of two nodes of the same fibre at periods `q1`, `q2`. -/
noncomputable def w0T (q1 q2 : ℕ) (eA eB : Bool) : ℕ :=
  open Classical in
  if q1 = q2 then (if Utab a b c n q1 eA eB = 0 then 0 else 2)
  else (if Vtab a b c n q1 eA eB = Vtab a b c n q2 eA eB then 0 else 2)

def anc (pv : Bool) (q : ℕ) : ℕ := if pv then q - 1 else q

/-- The in-fibre weight `max` over the nodes and their pivots. -/
noncomputable def inW (b1 b2 : Bool) (q1 q2 : ℕ) (eA eB : Bool) : ℕ :=
  max (max (w0T a b c n q1 q2 eA eB) (w0T a b c n q1 (anc (pivB a b c n b2 q2 eA eB) q2) eA eB))
    (max (w0T a b c n (anc (pivB a b c n b1 q1 eA eB) q1) q2 eA eB)
      (w0T a b c n (anc (pivB a b c n b1 q1 eA eB) q1) (anc (pivB a b c n b2 q2 eA eB) q2) eA eB))

/-- The off-fibre weight. -/
noncomputable def offW (b1 b2 : Bool) (q1 q2 : ℕ) (bt1 bt2 : Bits) : ℕ :=
  open Classical in
  if levT a b c n b1 q1 bt1.1 bt1.2.1 = levT a b c n b2 q2 bt2.1 bt2.2.1 then 0 else 1

/-- The pivot pair: a pivoted border line and the common line of its pivot. -/
noncomputable def pivRel (b1 b2 : Bool) (q1 q2 : ℕ) (bt1 bt2 : Bits) : Bool :=
  (pivB a b c n b1 q1 bt1.1 bt1.2.1 && !b2 && decide (q2 + 1 = q1) && decide (bt1 = bt2)) ||
  (pivB a b c n b2 q2 bt2.1 bt2.2.1 && !b1 && decide (q1 + 1 = q2) && decide (bt1 = bt2))

/-- **The weight at the type level.** -/
noncomputable def Wty (b1 b2 : Bool) (q1 q2 : ℕ) (bt1 bt2 : Bits) (par1 par2 : Bool) : ℕ :=
  if pivRel a b c n b1 b2 q1 q2 bt1 bt2 = true then offW a b c n b1 b2 q1 q2 bt1 bt2
  else if (decide (bt1 = bt2) && decide ((par1.toNat + q1) % 2 = (par2.toNat + q2) % 2)) = true then
    max (inW a b c n b1 b2 q1 q2 bt1.1 bt1.2.1) (offW a b c n b1 b2 q1 q2 bt1 bt2)
  else offW a b c n b1 b2 q1 q2 bt1 bt2

end TypeWeights

/-- The check: `Wty ≤ ρ + γ` for every pair of types (border rows have even nodes, border columns odd nodes). -/
noncomputable def LTab.ok (a b c : ℤ) (n : ℕ) (T : LTab) : Bool :=
  let A := T.arcs.length
  (List.range (T.qmax + 1)).all fun q1 => (List.range A).all fun a1 => [false, true].all fun par1 =>
  (List.range (T.qmax + 1)).all fun q2 => (List.range A).all fun a2 => [false, true].all fun par2 =>
  [false, true].all fun b1 => [false, true].all fun b2 =>
    !(decide (b1 = true → par1 = false) && decide (b2 = true → par2 = true)) ||
    decide (Wty a b c n b1 b2 q1 q2 (T.arcs.getD a1 (false, false, false, false))
      (T.arcs.getD a2 (false, false, false, false)) par1 par2 ≤
      (if b1 then potAt T.rb A q1 a1 par1 else potAt T.rc A q1 a1 par1) +
      (if b2 then potAt T.cb A q2 a2 par2 else potAt T.cc A q2 a2 par2))

/-! ### From the hybrid to node data -/

section Sound

variable {σ : Support} {a b c : ℤ} {h0 : a + b + c = 0} {p : ℕ} [hp : Fact p.Prime] {n : ℕ} {r m : ℕ}

theorem isPiv_eq (t : ℕ) :
    isPiv σ n p (flagB a b c n) t = flagB a b c n (t / p) (cA σ n p t) (cB p t) := by
  unfold isPiv
  by_cases h : flagB a b c n (t / p) (cA σ n p t) (cB p t) = true
  · have h1 : 1 ≤ t / p := by
      simp only [flagB, Bool.and_eq_true, decide_eq_true_eq] at h
      exact h.1.1.1
    have : p ≤ t := (Nat.le_div_iff_mul_le hp.out.pos).1 h1 |> fun h => by simpa using h
    simp [this, h]
  · have h' : flagB a b c n (t / p) (cA σ n p t) (cB p t) = false := by simpa using h
    simp [h']

/-- Border flag. -/
def bd : Fin r ⊕ Fin m → Bool := Sum.elim (fun _ => false) (fun _ => true)

variable (σ a b c h0 n p r m)

/-- The gauge data of the hybrid with the canonical pivot rule. -/
noncomputable def Gd (hm : 2 * m < p) : GData (Fin r ⊕ Fin m) :=
  hfData r m (pRd σ n p (flagB a b c n) r m hm) (pCd σ n p (flagB a b c n) r m hm)
    (fun i => lamNode σ a b c n p (flagB a b c n) (r + 2 * i.1))
    (fun i => lamNode σ a b c n p (flagB a b c n) (r + 2 * i.1 + 1))

/-- The effective levels of rows. -/
noncomputable def VRd (hm : 2 * m < p) : Fin r ⊕ Fin m → ℚ :=
  hfVr r m p (planeFrame σ a b c h0) (fun i => vsNode σ a b c h0 n p (flagB a b c n) (r + 2 * i.1))

/-- The effective levels of columns. -/
noncomputable def VCd (hm : 2 * m < p) : Fin r ⊕ Fin m → ℚ :=
  hfVr r m p (planeFrame σ a b c h0) (fun i => vsNode σ a b c h0 n p (flagB a b c n) (r + 2 * i.1 + 1))

variable {σ a b c h0 n p r m}

section Nodes2

variable (hm : 2 * m < p)

/-- Pivoted node. -/
noncomputable def pvN (σ : Support) (a b c : ℤ) (n p : ℕ) (t : ℕ) : Bool := isPiv σ n p (flagB a b c n) t

/-- The ancestor of a node of the given role. -/
noncomputable def ancN (σ : Support) (a b c : ℤ) (n p : ℕ) (bo : Bool) (t : ℕ) : ℕ :=
  if bo && pvN σ a b c n p t then t - p else t

/-- The effective level of a node of the given role. -/
noncomputable def levN (σ : Support) (a b c : ℤ) (h0 : a + b + c = 0) (n p : ℕ) (bo : Bool) (t : ℕ) : ℚ :=
  if bo then vsNode σ a b c h0 n p (flagB a b c n) t else Vp p (planeFrame σ a b c h0) t

theorem pRd_eq_some {i : Fin m} {ci : Fin r} :
    pRd σ n p (flagB a b c n) r m hm i = some ci ↔
      pvN σ a b c n p (r + 2 * i.1) = true ∧ ci.1 = r + 2 * i.1 - p := by
  unfold pRd pvN
  by_cases h : isPiv σ n p (flagB a b c n) (r + 2 * i.1) = true
  · simp only [h, dif_pos, Option.some.injEq, true_and]
    constructor
    · intro e; rw [← e]
    · intro e; exact Fin.ext e.symm
  · simp [h]

theorem pCd_eq_some {i : Fin m} {ci : Fin r} :
    pCd σ n p (flagB a b c n) r m hm i = some ci ↔
      pvN σ a b c n p (r + 2 * i.1 + 1) = true ∧ ci.1 = r + 2 * i.1 + 1 - p := by
  unfold pCd pvN
  by_cases h : isPiv σ n p (flagB a b c n) (r + 2 * i.1 + 1) = true
  · simp only [h, dif_pos, Option.some.injEq, true_and]
    constructor
    · intro e; rw [← e]
    · intro e; exact Fin.ext e.symm
  · simp [h]

theorem pRd_eq_none {i : Fin m} :
    pRd σ n p (flagB a b c n) r m hm i = none ↔ ¬ pvN σ a b c n p (r + 2 * i.1) = true := by
  unfold pRd pvN
  by_cases h : isPiv σ n p (flagB a b c n) (r + 2 * i.1) = true <;> simp [h]

theorem pCd_eq_none {i : Fin m} :
    pCd σ n p (flagB a b c n) r m hm i = none ↔ ¬ pvN σ a b c n p (r + 2 * i.1 + 1) = true := by
  unfold pCd pvN
  by_cases h : isPiv σ n p (flagB a b c n) (r + 2 * i.1 + 1) = true <;> simp [h]

theorem rn_aR_inl (ci : Fin r) :
    (Gd σ a b c p n r m hm).rn ((Gd σ a b c p n r m hm).aR (Sum.inl ci)) = ci.1 := rfl

theorem cn_aC_inl (ci : Fin r) :
    (Gd σ a b c p n r m hm).cn ((Gd σ a b c p n r m hm).aC (Sum.inl ci)) = ci.1 := rfl

theorem rn_aR_inr (i : Fin m) :
    (Gd σ a b c p n r m hm).rn ((Gd σ a b c p n r m hm).aR (Sum.inr i)) =
      ancN σ a b c n p true (r + 2 * i.1) := by
  unfold GData.aR ancN
  have e : (Gd σ a b c p n r m hm).π (Sum.inr i) = (pRd σ n p (flagB a b c n) r m hm i).map Sum.inl := rfl
  rw [e]
  rcases h : pRd σ n p (flagB a b c n) r m hm i with _ | ci
  · have := (pRd_eq_none (hm := hm)).1 h
    simp [this]
    rfl
  · obtain ⟨h1, h2⟩ := (pRd_eq_some (hm := hm)).1 h
    simp [h1]
    exact h2

theorem cn_aC_inr (i : Fin m) :
    (Gd σ a b c p n r m hm).cn ((Gd σ a b c p n r m hm).aC (Sum.inr i)) =
      ancN σ a b c n p true (r + 2 * i.1 + 1) := by
  unfold GData.aC ancN
  have e : (Gd σ a b c p n r m hm).π' (Sum.inr i) = (pCd σ n p (flagB a b c n) r m hm i).map Sum.inl := rfl
  rw [e]
  rcases h : pCd σ n p (flagB a b c n) r m hm i with _ | ci
  · have := (pCd_eq_none (hm := hm)).1 h
    simp [this]
    rfl
  · obtain ⟨h1, h2⟩ := (pCd_eq_some (hm := hm)).1 h
    simp [h1]
    exact h2

end Nodes2

section WdNode

variable (hm : 2 * m < p)

/-- The weight of a pair of nodes with roles. -/
noncomputable def WdN (σ : Support) (a b c : ℤ) (h0 : a + b + c = 0) (p n : ℕ) (b1 : Bool) (t1 : ℕ) (b2 : Bool)
    (t2 : ℕ) : ℕ :=
  open Classical in
  if ((b1 && !b2 && pvN σ a b c n p t1 && decide (t1 = t2 + p)) ||
      (b2 && !b1 && pvN σ a b c n p t2 && decide (t2 = t1 + p))) = true then 0
  else if (t1 : ℤ) ≡ t2 [ZMOD p] then
    max (max (w0 p (planeFrame σ a b c h0) t1 t2) (w0 p (planeFrame σ a b c h0) t1 (ancN σ a b c n p b2 t2)))
      (max (w0 p (planeFrame σ a b c h0) (ancN σ a b c n p b1 t1) t2)
        (w0 p (planeFrame σ a b c h0) (ancN σ a b c n p b1 t1) (ancN σ a b c n p b2 t2)))
  else if levN σ a b c h0 n p b1 t1 = levN σ a b c h0 n p b2 t2 then 0 else 1

theorem Wd_eq (x y : Fin r ⊕ Fin m) :
    Wd p (planeFrame σ a b c h0) (Gd σ a b c p n r m hm) (VRd σ a b c h0 p n r m hm) (VCd σ a b c h0 p n r m hm) x y =
      WdN σ a b c h0 p n (bd x) ((Gd σ a b c p n r m hm).rn x) (bd y) ((Gd σ a b c p n r m hm).cn y) := by
  have hcond : ((Gd σ a b c p n r m hm).π x = some y ∨ (Gd σ a b c p n r m hm).π' y = some x) ↔
      (((bd x && !bd y && pvN σ a b c n p ((Gd σ a b c p n r m hm).rn x) &&
          decide ((Gd σ a b c p n r m hm).rn x = (Gd σ a b c p n r m hm).cn y + p)) ||
        (bd y && !bd x && pvN σ a b c n p ((Gd σ a b c p n r m hm).cn y) &&
          decide ((Gd σ a b c p n r m hm).cn y = (Gd σ a b c p n r m hm).rn x + p))) = true) := by
    rcases x with xi | xi <;> rcases y with yi | yi
    · simp [Gd, hfData, bd]
    · constructor
      · rintro (h | h)
        · exact absurd h (by simp [Gd, hfData])
        · have h' : (pCd σ n p (flagB a b c n) r m hm yi).map Sum.inl = some (Sum.inl xi) := h
          rw [Option.map_eq_some_iff] at h'
          obtain ⟨c', hc', hc''⟩ := h'
          have := Sum.inl.inj hc''
          subst this
          obtain ⟨h1, h2⟩ := (pCd_eq_some (hm := hm)).1 hc'
          have hle : p ≤ r + 2 * yi.1 + 1 := isPiv_le h1
          simp [bd, Gd, hfData, pvN, h1]
          exact ⟨h1, decide_eq_true (by omega)⟩
      · intro h
        right
        simp [bd, Gd, hfData, pvN] at h
        obtain ⟨h1, h2'⟩ := h
        have h2 := of_decide_eq_true h2'
        have hle : p ≤ r + 2 * yi.1 + 1 := isPiv_le h1
        show (pCd σ n p (flagB a b c n) r m hm yi).map Sum.inl = some (Sum.inl xi)
        rw [(pCd_eq_some (hm := hm) (ci := xi)).2 ⟨h1, by omega⟩]
        rfl
    · constructor
      · rintro (h | h)
        · have h' : (pRd σ n p (flagB a b c n) r m hm xi).map Sum.inl = some (Sum.inl yi) := h
          rw [Option.map_eq_some_iff] at h'
          obtain ⟨c', hc', hc''⟩ := h'
          have := Sum.inl.inj hc''
          subst this
          obtain ⟨h1, h2⟩ := (pRd_eq_some (hm := hm)).1 hc'
          have hle : p ≤ r + 2 * xi.1 := isPiv_le h1
          simp [bd, Gd, hfData, pvN, h1]
          exact ⟨h1, decide_eq_true (by omega)⟩
        · exact absurd h (by simp [Gd, hfData])
      · intro h
        left
        simp [bd, Gd, hfData, pvN] at h
        obtain ⟨h1, h2'⟩ := h
        have h2 := of_decide_eq_true h2'
        have hle : p ≤ r + 2 * xi.1 := isPiv_le h1
        show (pRd σ n p (flagB a b c n) r m hm xi).map Sum.inl = some (Sum.inl yi)
        rw [(pRd_eq_some (hm := hm) (ci := yi)).2 ⟨h1, by omega⟩]
        rfl
    · simp [Gd, hfData, bd]
  have e1 : (Gd σ a b c p n r m hm).rn ((Gd σ a b c p n r m hm).aR x) =
      ancN σ a b c n p (bd x) ((Gd σ a b c p n r m hm).rn x) := by
    rcases x with xi | xi
    · rw [rn_aR_inl]; simp [ancN, bd, Gd, hfData]
    · rw [rn_aR_inr]; simp [ancN, bd, Gd, hfData]
  have e2 : (Gd σ a b c p n r m hm).cn ((Gd σ a b c p n r m hm).aC y) =
      ancN σ a b c n p (bd y) ((Gd σ a b c p n r m hm).cn y) := by
    rcases y with yi | yi
    · rw [cn_aC_inl]; simp [ancN, bd, Gd, hfData]
    · rw [cn_aC_inr]; simp [ancN, bd, Gd, hfData]
  have e3 : VRd σ a b c h0 p n r m hm x = levN σ a b c h0 n p (bd x) ((Gd σ a b c p n r m hm).rn x) := by
    rcases x with xi | xi <;> simp [VRd, hfVr, levN, bd, Gd, hfData]
  have e4 : VCd σ a b c h0 p n r m hm y = levN σ a b c h0 n p (bd y) ((Gd σ a b c p n r m hm).cn y) := by
    rcases y with yi | yi <;> simp [VCd, hfVr, levN, bd, Gd, hfData]
  unfold Wd WdN
  by_cases hc : ((bd x && !bd y && pvN σ a b c n p ((Gd σ a b c p n r m hm).rn x) &&
          decide ((Gd σ a b c p n r m hm).rn x = (Gd σ a b c p n r m hm).cn y + p)) ||
        (bd y && !bd x && pvN σ a b c n p ((Gd σ a b c p n r m hm).cn y) &&
          decide ((Gd σ a b c p n r m hm).cn y = (Gd σ a b c p n r m hm).rn x + p))) = true
  · rw [if_pos (hcond.2 hc), if_pos hc]
  · rw [if_neg (fun h => hc (hcond.1 h)), if_neg hc, e1, e2, e3, e4]

end WdNode

section NodeLe

variable (hp7 : 7 ≤ p) (hn : n = 1 ∨ n = 2) (h3 : 3 ∣ n * p + σ.rho)

theorem cA_mod {t t' : ℕ} (h : t % p = t' % p) : cA σ n p t = cA σ n p t' := by simp [cA, h]
theorem cB_mod {t t' : ℕ} (h : t % p = t' % p) : cB p t = cB p t' := by simp [cB, h]

theorem pvN_eq (t : ℕ) : pvN σ a b c n p t = flagB a b c n (t / p) (cA σ n p t) (cB p t) := isPiv_eq t

theorem flagB_q {q : ℕ} {eA eB : Bool} (h : flagB a b c n q eA eB = true) : 1 ≤ q := by
  simp only [flagB, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1

theorem ancN_div (bo : Bool) (t : ℕ) :
    ancN σ a b c n p bo t / p = anc (pivB a b c n bo (t / p) (cA σ n p t) (cB p t)) (t / p) ∧
      ancN σ a b c n p bo t % p = t % p := by
  unfold ancN anc pivB
  rw [pvN_eq]
  by_cases h : (bo && flagB a b c n (t / p) (cA σ n p t) (cB p t)) = true
  · have hf : flagB a b c n (t / p) (cA σ n p t) (cB p t) = true := by
      simp only [Bool.and_eq_true] at h
      exact h.2
    have hq := flagB_q hf
    have hle : p ≤ t := (Nat.le_div_iff_mul_le hp.out.pos).1 hq |> fun h => by simpa using h
    obtain ⟨e1, e2⟩ := cell_pred (p := p) hle
    simp [h, e1, e2]
  · simp [h]

include hp7 hn h3 in
theorem levN_eq (bo : Bool) (t : ℕ) :
    levN σ a b c h0 n p bo t = levT a b c n bo (t / p) (cA σ n p t) (cB p t) := by
  unfold levN levT vsNode
  rw [planeV_eq hp7 hn h3]
  simp only [isPiv_eq, cA, cB]
  cases bo
  · simp
  · by_cases h : flagB a b c n (t / p) (decide ((n * p + σ.rho) / 3 ≤ t % p)) (decide ((p + 1) / 2 ≤ t % p)) = true
    · simp [h]
    · simp [h]

include hp7 hn h3 in
theorem w0_eq {U V : ℕ} (hUV : U % p = V % p) :
    w0 p (planeFrame σ a b c h0) U V = w0T a b c n (U / p) (V / p) (cA σ n p U) (cB p U) := by
  have hq : U = V ↔ U / p = V / p := by
    constructor
    · rintro rfl; rfl
    · intro h
      have h1 := Nat.div_add_mod U p
      have h2 := Nat.div_add_mod V p
      rw [h, hUV] at h1
      omega
  have hAV : decide ((n * p + σ.rho) / 3 ≤ V % p) = decide ((n * p + σ.rho) / 3 ≤ U % p) := by rw [hUV]
  have hBV : decide ((p + 1) / 2 ≤ V % p) = decide ((p + 1) / 2 ≤ U % p) := by rw [hUV]
  unfold w0 w0T
  rw [planeV_eq hp7 hn h3, planeV_eq hp7 hn h3, planeU_eq hp7 hn h3]
  simp only [cA, cB, hAV, hBV, hq]
  split_ifs <;> simp_all

end NodeLe

section WdLe

theorem Wty_ge_off (a b c : ℤ) (n : ℕ) (b1 b2 : Bool) (q1 q2 : ℕ) (bt1 bt2 : Bits) (par1 par2 : Bool) :
    offW a b c n b1 b2 q1 q2 bt1 bt2 ≤ Wty a b c n b1 b2 q1 q2 bt1 bt2 par1 par2 := by
  unfold Wty
  split_ifs
  · exact le_rfl
  · exact le_max_right _ _
  · exact le_rfl

theorem par_compat {p : ℕ} (hp2 : p % 2 = 1) {t1 t2 : ℕ} (hmod : t1 % p = t2 % p) :
    (t1 % 2 + t1 / p) % 2 = (t2 % 2 + t2 / p) % 2 := by
  have key : ∀ q ξ : ℕ, (p * q + ξ) % 2 = (q + ξ) % 2 := fun q ξ => by
    rw [Nat.add_mod, Nat.mul_mod, hp2]; omega
  have e1 := Nat.div_add_mod t1 p
  have e2 := Nat.div_add_mod t2 p
  have k1 := key (t1 / p) (t1 % p)
  have k2 := key (t2 / p) (t2 % p)
  rw [e1] at k1
  rw [e2] at k2
  rw [hmod] at k1
  omega

variable (hp7 : 7 ≤ p) (hn : n = 1 ∨ n = 2) (h3 : 3 ∣ n * p + σ.rho)

include hp7 hn h3 in
theorem WdN_le (r m : ℕ) (b1 b2 : Bool) (t1 t2 : ℕ) :
    WdN σ a b c h0 p n b1 t1 b2 t2 ≤ Wty a b c n b1 b2 (t1 / p) (t2 / p) (nodeBits σ n p r m t1)
      (nodeBits σ n p r m t2) (decide (t1 % 2 = 1)) (decide (t2 % 2 = 1)) := by
  have hp2 : p % 2 = 1 := by
    rcases hp.out.eq_two_or_odd with h | h
    · omega
    · exact h
  unfold WdN
  by_cases hpv : ((b1 && !b2 && pvN σ a b c n p t1 && decide (t1 = t2 + p)) ||
      (b2 && !b1 && pvN σ a b c n p t2 && decide (t2 = t1 + p))) = true
  · rw [if_pos hpv]; exact Nat.zero_le _
  rw [if_neg hpv]
  by_cases hcg : (t1 : ℤ) ≡ t2 [ZMOD p]
  · rw [if_pos hcg]
    have hmod : t1 % p = t2 % p := Int.natCast_modEq_iff.1 hcg
    have hbits : nodeBits σ n p r m t1 = nodeBits σ n p r m t2 := by
      unfold nodeBits cA cB; rw [hmod]
    have hA : cA σ n p t2 = cA σ n p t1 := (cA_mod hmod).symm
    have hB : cB p t2 = cB p t1 := (cB_mod hmod).symm
    have hpar : (t1 % 2 + t1 / p) % 2 = (t2 % 2 + t2 / p) % 2 := par_compat hp2 hmod
    -- not a pivot pair at the type level
    have hnp : pivRel a b c n b1 b2 (t1 / p) (t2 / p) (nodeBits σ n p r m t1) (nodeBits σ n p r m t2) = false := by
      by_contra hcon
      have hcon' : pivRel a b c n b1 b2 (t1 / p) (t2 / p) (nodeBits σ n p r m t1) (nodeBits σ n p r m t2) = true := by
        simpa using hcon
      apply hpv
      have e1 := Nat.div_add_mod t1 p
      have e2 := Nat.div_add_mod t2 p
      unfold pivRel at hcon'
      simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hcon' ⊢
      rcases hcon' with ⟨⟨⟨h1, h2⟩, h3'⟩, h4⟩ | ⟨⟨⟨h1, h2⟩, h3'⟩, h4⟩
      · left
        have hq : t1 / p = t2 / p + 1 := by omega
        have : t1 = t2 + p := by
          rw [hq, Nat.mul_succ] at e1
          omega
        simp only [pivB, nodeBits, Bool.and_eq_true] at h1
        refine ⟨⟨⟨h1.1, h2⟩, ?_⟩, this⟩
        rw [pvN_eq]; exact h1.2
      · right
        have hq : t2 / p = t1 / p + 1 := by omega
        have : t2 = t1 + p := by
          rw [hq, Nat.mul_succ] at e2
          omega
        simp only [pivB, nodeBits, Bool.and_eq_true] at h1
        refine ⟨⟨⟨h1.1, h2⟩, ?_⟩, this⟩
        rw [pvN_eq]
        have := h1.2
        simpa [hA, hB] using this
    have hW : Wty a b c n b1 b2 (t1 / p) (t2 / p) (nodeBits σ n p r m t1) (nodeBits σ n p r m t2)
        (decide (t1 % 2 = 1)) (decide (t2 % 2 = 1)) =
        max (inW a b c n b1 b2 (t1 / p) (t2 / p) (nodeBits σ n p r m t1).1 (nodeBits σ n p r m t1).2.1)
          (offW a b c n b1 b2 (t1 / p) (t2 / p) (nodeBits σ n p r m t1) (nodeBits σ n p r m t2)) := by
      unfold Wty
      rw [if_neg (by simp [hnp]), if_pos]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨hbits, ?_⟩
      have h1 : (decide (t1 % 2 = 1)).toNat = t1 % 2 := by
        by_cases h : t1 % 2 = 1 <;> simp [h] <;> omega
      have h2 : (decide (t2 % 2 = 1)).toNat = t2 % 2 := by
        by_cases h : t2 % 2 = 1 <;> simp [h] <;> omega
      rw [h1, h2]; exact hpar
    rw [hW]
    refine le_trans ?_ (le_max_left _ _)
    -- the four in-fibre weights
    have c1 := ancN_div (σ := σ) (a := a) (b := b) (c := c) (n := n) (p := p) b1 t1
    have c2 := ancN_div (σ := σ) (a := a) (b := b) (c := c) (n := n) (p := p) b2 t2
    have m1 : ancN σ a b c n p b1 t1 % p = t2 % p := c1.2.trans hmod
    have m2 : t1 % p = ancN σ a b c n p b2 t2 % p := hmod.trans c2.2.symm
    have m3 : ancN σ a b c n p b1 t1 % p = ancN σ a b c n p b2 t2 % p := c1.2.trans m2
    have w1 := w0_eq (σ := σ) (a := a) (b := b) (c := c) (h0 := h0) hp7 hn h3 hmod
    have w2 := w0_eq (σ := σ) (a := a) (b := b) (c := c) (h0 := h0) hp7 hn h3 m2
    have w3 := w0_eq (σ := σ) (a := a) (b := b) (c := c) (h0 := h0) hp7 hn h3 m1
    have w4 := w0_eq (σ := σ) (a := a) (b := b) (c := c) (h0 := h0) hp7 hn h3 m3
    have a1 : cA σ n p (ancN σ a b c n p b1 t1) = cA σ n p t1 := cA_mod c1.2
    have b1' : cB p (ancN σ a b c n p b1 t1) = cB p t1 := cB_mod c1.2
    rw [w1, w2, w3, w4, a1, b1', c1.1, c2.1, hA, hB]
    unfold inW nodeBits
    simp only [hA, hB]
    exact le_rfl
  · rw [if_neg hcg]
    by_cases hl : levN σ a b c h0 n p b1 t1 = levN σ a b c h0 n p b2 t2
    · rw [if_pos hl]; exact Nat.zero_le _
    · rw [if_neg hl]
      refine le_trans ?_ (Wty_ge_off a b c n b1 b2 _ _ _ _ _ _)
      unfold offW
      rw [levN_eq hp7 hn h3, levN_eq hp7 hn h3] at hl
      simp only [nodeBits]
      split_ifs <;> simp_all

end WdLe

section Feasible

/-- The index of an arc. -/
def arcIdx (T : LTab) (bt : Bits) : ℕ := T.arcs.idxOf bt

/-- The row potentials of the hybrid: common rows by `rc`, border rows (even nodes) by `rb`. -/
noncomputable def rhoF (σ : Support) (n p r m : ℕ) (T : LTab) : Fin r ⊕ Fin m → ℚ
  | Sum.inl ci => (potAt T.rc T.arcs.length (ci.1 / p) (arcIdx T (nodeBits σ n p r m ci.1))
      (decide (ci.1 % 2 = 1)) : ℚ)
  | Sum.inr i => (potAt T.rb T.arcs.length ((r + 2 * i.1) / p) (arcIdx T (nodeBits σ n p r m (r + 2 * i.1)))
      false : ℚ)

/-- The column potentials of the hybrid: common columns by `cc`, border columns (odd nodes) by `cb`. -/
noncomputable def gammaF (σ : Support) (n p r m : ℕ) (T : LTab) : Fin r ⊕ Fin m → ℚ
  | Sum.inl ci => (potAt T.cc T.arcs.length (ci.1 / p) (arcIdx T (nodeBits σ n p r m ci.1))
      (decide (ci.1 % 2 = 1)) : ℚ)
  | Sum.inr i => (potAt T.cb T.arcs.length ((r + 2 * i.1 + 1) / p)
      (arcIdx T (nodeBits σ n p r m (r + 2 * i.1 + 1))) true : ℚ)

theorem ok_spec {a b c : ℤ} {n : ℕ} {T : LTab} (h : T.ok a b c n = true) {q1 a1 q2 a2 : ℕ} {par1 par2 b1 b2 : Bool}
    (hq1 : q1 ≤ T.qmax) (ha1 : a1 < T.arcs.length) (hq2 : q2 ≤ T.qmax) (ha2 : a2 < T.arcs.length)
    (hb1 : b1 = true → par1 = false) (hb2 : b2 = true → par2 = true) :
    Wty a b c n b1 b2 q1 q2 (T.arcs.getD a1 (false, false, false, false)) (T.arcs.getD a2 (false, false, false, false))
        par1 par2 ≤
      (if b1 then potAt T.rb T.arcs.length q1 a1 par1 else potAt T.rc T.arcs.length q1 a1 par1) +
      (if b2 then potAt T.cb T.arcs.length q2 a2 par2 else potAt T.cc T.arcs.length q2 a2 par2) := by
  unfold LTab.ok at h
  have h1 := (List.all_eq_true.1 h) q1 (List.mem_range.2 (by omega))
  have h2 := (List.all_eq_true.1 h1) a1 (List.mem_range.2 ha1)
  have h3 := (List.all_eq_true.1 h2) par1 (by cases par1 <;> simp)
  have h4 := (List.all_eq_true.1 h3) q2 (List.mem_range.2 (by omega))
  have h5 := (List.all_eq_true.1 h4) a2 (List.mem_range.2 ha2)
  have h6 := (List.all_eq_true.1 h5) par2 (by cases par2 <;> simp)
  have h7 := (List.all_eq_true.1 h6) b1 (by cases b1 <;> simp)
  have h8 := (List.all_eq_true.1 h7) b2 (by cases b2 <;> simp)
  rcases Bool.or_eq_true_iff.1 h8 with h9 | h9
  · exfalso
    have hg : (decide (b1 = true → par1 = false) && decide (b2 = true → par2 = true)) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hb1, hb2⟩
    rw [hg] at h9
    exact absurd h9 (by simp)
  · exact of_decide_eq_true h9

end Feasible

section FeasibleMain

theorem arcIdx_lt {T : LTab} {bt : Bits} (h : bt ∈ T.arcs) : arcIdx T bt < T.arcs.length :=
  List.idxOf_lt_length_iff.2 h

theorem getD_arcIdx {T : LTab} {bt : Bits} (h : bt ∈ T.arcs) :
    T.arcs.getD (arcIdx T bt) (false, false, false, false) = bt := by
  have hl := arcIdx_lt h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]
  simp [arcIdx]

variable {σ : Support} {a b c : ℤ} {h0 : a + b + c = 0} {p : ℕ} [hp : Fact p.Prime] {n : ℕ} {r m : ℕ}
variable (hp7 : 7 ≤ p) (hn : n = 1 ∨ n = 2) (h3 : 3 ∣ n * p + σ.rho)

include hp7 hn h3 in
/-- **Soundness of the type-level check**: `ok = true` gives `Wd ≤ ρ x + γ y` on the whole hybrid. -/
theorem feasible_of_ok (hm : 2 * m < p) (hr : r % 2 = 0) (T : LTab) (hok : T.ok a b c n = true)
    (hq : (r + 2 * m) / p ≤ T.qmax) (hnodes : ∀ t < r + 2 * m, nodeBits σ n p r m t ∈ T.arcs)
    (x y : Fin r ⊕ Fin m) :
    ((Wd p (planeFrame σ a b c h0) (Gd σ a b c p n r m hm) (VRd σ a b c h0 p n r m hm) (VCd σ a b c h0 p n r m hm)
      x y : ℕ) : ℚ) ≤ rhoF σ n p r m T x + gammaF σ n p r m T y := by
  rw [Wd_eq hm x y]
  have hW := WdN_le (σ := σ) (a := a) (b := b) (c := c) (h0 := h0) (p := p) (n := n) hp7 hn h3 r m (bd x) (bd y)
    ((Gd σ a b c p n r m hm).rn x) ((Gd σ a b c p n r m hm).cn y)
  have hlt1 : (Gd σ a b c p n r m hm).rn x < r + 2 * m := by
    rcases x with xi | xi
    · have := xi.2; show xi.1 < _; omega
    · have := xi.2; show r + 2 * xi.1 < _; omega
  have hlt2 : (Gd σ a b c p n r m hm).cn y < r + 2 * m := by
    rcases y with yi | yi
    · have := yi.2; show yi.1 < _; omega
    · have := yi.2; show r + 2 * yi.1 + 1 < _; omega
  have hq1 : (Gd σ a b c p n r m hm).rn x / p ≤ T.qmax :=
    le_trans (Nat.div_le_div_right hlt1.le) hq
  have hq2 : (Gd σ a b c p n r m hm).cn y / p ≤ T.qmax :=
    le_trans (Nat.div_le_div_right hlt2.le) hq
  have hs := ok_spec hok hq1 (arcIdx_lt (hnodes _ hlt1)) hq2 (arcIdx_lt (hnodes _ hlt2))
    (par1 := decide ((Gd σ a b c p n r m hm).rn x % 2 = 1)) (par2 := decide ((Gd σ a b c p n r m hm).cn y % 2 = 1))
    (b1 := bd x) (b2 := bd y) ?_ ?_
  · rw [getD_arcIdx (hnodes _ hlt1), getD_arcIdx (hnodes _ hlt2)] at hs
    have hle := le_trans hW hs
    clear hs hW
    rcases x with xi | xi <;> rcases y with yi | yi
    · have e := hle
      simp [bd, Gd, hfData, rhoF, gammaF] at e ⊢
      exact_mod_cast e
    · have e := hle
      have e2 : (r + 2 * yi.1 + 1) % 2 = 1 := by omega
      simp [bd, Gd, hfData, rhoF, gammaF, e2] at e ⊢
      exact_mod_cast e
    · have e := hle
      have e1 : (r + 2 * xi.1) % 2 = 0 := by omega
      simp [bd, Gd, hfData, rhoF, gammaF, e1] at e ⊢
      exact_mod_cast e
    · have e := hle
      have e1 : (r + 2 * xi.1) % 2 = 0 := by omega
      have e2 : (r + 2 * yi.1 + 1) % 2 = 1 := by omega
      simp [bd, Gd, hfData, rhoF, gammaF, e1, e2] at e ⊢
      exact_mod_cast e
  · intro hb
    rcases x with xi | xi
    · simp [bd] at hb
    · simp only [Gd, hfData]
      have : (r + 2 * xi.1) % 2 = 0 := by omega
      simp [this]
  · intro hb
    rcases y with yi | yi
    · simp [bd] at hb
    · simp only [Gd, hfData]
      have : (r + 2 * yi.1 + 1) % 2 = 1 := by omega
      simp [this]

end FeasibleMain

end Sound

end CatalanCore.Uniform.Bank.Plane1.Dips
