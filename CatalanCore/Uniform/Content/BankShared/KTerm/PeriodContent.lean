module

public import CatalanCore.Uniform.Content.BankShared.KTerm.Content
public import CatalanCore.Uniform.Content.BankShared.KTerm.PeriodWindow

@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 1600000

/-! # Theorem C3: the content of a bank whose periodic layer is the closed form (wave H5a-closed)

`KTmplC` is a class template `expansion(N) ++ head`: the strips `n' = N, …, 1` of the periodic layer as the
expansion of a period table of cells (`PeriodCell`), then the head pieces (`θ > 1 / b`), each of the head
with its `pieceOK` certificate.  `KBankDataC` is a `KBankData` with such templates; `KBankDataC.toK` lists the
pieces explicitly.  `kcheckC` is `kcheck` with `pieceOK` for the head only and `PCell.ok` for the cells of each class.

`hasScaledContent_of_facts` is `hasScaledContent_of_kcheckFam` with the three uses of `pieceOK` on the pieces of
a template replaced by: `PieceBasic` (the chain), and `PieceCov` (the piece bound `n_p ≤ a r + b p + C`
at every admissible point of the piece, with `p > P_bad` and `q (r + 2 m) < p²` supplied by the scale `R0`).
`head_cov` proves `PieceCov` for a `pieceOK` piece (Theorem B, `piece_sound`); `exp_cov` for an expansion piece
(Lemma T, `PeriodWindow`, with the prefix branch of the cell as the valid branch).  `hasScaledContent_of_kcheckC`
is Theorem C3. -/

namespace CatalanCore.Uniform.Content.BankShared.KTerm
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.BankShared
  CatalanCore.Uniform.Content.SmallPrimes CatalanCore.Uniform.Content.Member CatalanCore.Arith.Hybrid
  CatalanCore.Basic Filter Finset Polynomial CatalanCore.Uniform.Content.BankShared.Check

/-! ### Data -/

/-- A class template with a closed-form periodic layer. -/
structure KTmplC where
  t1 : ℚ
  N : ℕ
  cells : List PCell
  head : List (QPiece × Cert)
  tb : ℕ

/-- The certificate carried by expansion pieces (never inspected). -/
def dummyCert : Cert := ⟨0, [], [], 1⟩

/-- The slack of an expansion piece. -/
def expC : ℚ := 3

/-- The explicit template. -/
def KTmplC.toK (α : ℚ) (T : KTmplC) : KTmpl :=
  ⟨T.t1, (expList α α.den expC T.N T.cells).map (fun q => (q, dummyCert)) ++ T.head, T.tb⟩

/-- The data of a `k`-shift bank with closed-form templates. -/
structure KBankDataC where
  Q : ℕ
  M : ℕ
  α : ℚ
  a : ℕ
  shifts : List Shift
  depth : ℕ
  cF : ℕ
  Pbad : ℕ
  α0 : ℚ
  τ : ℚ
  Λ : ℚ
  α0b : ℚ
  t0 : ℚ
  Rt : ℚ
  kcat : List KBranch
  tmpls : List (ℕ × KTmplC)

/-- The explicit bank. -/
def KBankDataC.toK (E : KBankDataC) : KBankData :=
  ⟨E.Q, E.M, E.α, E.a, E.shifts, E.depth, E.cF, E.Pbad, E.α0, E.τ, E.Λ, E.α0b, E.t0, E.Rt, E.kcat,
    E.tmpls.map (fun x => (x.1, x.2.toK E.α))⟩

/-- The position `j_i / q_i` of the `i`-th pole in the root class `j`. -/
def kappaOf (D : KBankData) (j t : ℕ) : ℚ := ((shAt D.shifts t).jj j : ℚ) / ((shAt D.shifts t).q : ℚ)

/-- Frame checks of a closed bank. -/
def kcParams (E : KBankDataC) : Bool :=
  kcheckParams E.toK && decide (2 ≤ E.shifts.length) && decide (0 < E.α)

/-- (D2)-(D4) of every template, and `N ≥ 1`. -/
def kcHeads (E : KBankDataC) : Bool :=
  E.tmpls.all (fun x => ktmplHead E.toK x.1 (x.2.toK E.α) && decide (1 ≤ x.2.N))

/-- The cell certificates of every template. -/
def kcCells (E : KBankDataC) : Bool :=
  E.tmpls.all (fun x => x.2.cells.all (fun c => c.ok E.α (kappaOf E.toK x.1 0) (kappaOf E.toK x.1 1)))

/-- `pieceOK` of the head pieces. -/
def kcPieces (E : KBankDataC) : Bool :=
  E.tmpls.all (fun x => kpieceAll E.toK x.1 x.2.head)

/-- (D1), (D6): every unit class has a template, and the mass. -/
def kcClass (E : KBankDataC) : Bool := kclassOK E.toK

/-- **The closed `k`-shift bank check.** -/
def kcheckC (E : KBankDataC) : Bool :=
  kcParams E && kcHeads E && kcCells E && kcPieces E && kcClass E

/-! ### Facts of a bank check -/

/-- The frame facts of `kcheck`. -/
def KParams (D : KBankData) : Prop :=
  2 ≤ D.Q ∧ D.Q ≤ D.Pbad ∧ 0 < D.M ∧ D.M % D.Q = 0 ∧ 0 < D.a ∧ D.a < D.Q ∧ 0 ≤ D.α ∧ D.α0b ≤ D.α0 ∧
    0 ≤ D.α0 ∧ (∀ x ∈ D.shifts, shiftOK D.Q D.oM x = true)

theorem kparams_of {D : KBankData} (h : kcheckParams D = true) : KParams D := by
  simp only [kcheckParams, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, -⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

/-- The facts of `ktmplHead`. -/
theorem ktmplHead_facts {D : KBankData} {j : ℕ} {T : KTmpl} (h : ktmplHead D j T = true) :
    0 < T.t1 ∧ T.t1 ≤ D.t0 ∧ chainOK T.t1 T.pieces = true ∧
    (∀ x ∈ D.shifts, x.s * j % x.q ≠ 0) ∧
    tailOK D j (tendQ T.t1 T.pieces) T.tb = true ∧ tendQ T.t1 T.pieces ≤ D.τ := by
  simp only [ktmplHead, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem chain_real_basic {cat : List Branch} {q : ℕ} {α κ : ℚ} {depth cF Pbad : ℕ} :
    ∀ (l : List (QPiece × Cert)) (s0 : ℚ), chainOK s0 l = true → (∀ x ∈ l, PieceBasic x.1) →
      Chain (s0 : ℝ) (l.map (fun x => x.1.toPiece))
  | [], _, _, _ => trivial
  | x :: l, s0, h, hp => by
    simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hs0, hst, hC0, ha0, ha1⟩ := hp x List.mem_cons_self
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [QPiece.toPiece, h.1]
    · show (0 : ℝ) < (x.1.s : ℝ); exact_mod_cast hs0
    · show (x.1.s : ℝ) ≤ x.1.t; exact_mod_cast hst.le
    · show (0 : ℝ) ≤ (x.1.C : ℝ); exact_mod_cast hC0
    · show (0 : ℝ) ≤ (x.1.a : ℝ) + x.1.b * x.1.s; exact_mod_cast ha0
    · show (0 : ℝ) ≤ (x.1.a : ℝ) + x.1.b * x.1.t; exact_mod_cast ha1
    · exact chain_real_basic (cat := cat) (q := q) (α := α) (κ := κ) (depth := depth) (cF := cF) (Pbad := Pbad)
        l x.1.t h.2 (fun y hy => hp y (List.mem_cons_of_mem _ hy))

theorem kchain_ge' : ∀ (l : List (QPiece × Cert)) (s0 : ℚ), chainOK s0 l = true →
    (∀ x ∈ l, PieceBasic x.1) → (∀ x ∈ l, s0 ≤ x.1.s) ∧ s0 ≤ tendQ s0 l
  | [], _, _, _ => ⟨fun _ h => absurd h List.not_mem_nil, le_refl _⟩
  | x :: l, s0, h, hp => by
    simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq] at h
    have hx := hp x List.mem_cons_self
    obtain ⟨ih1, ih2⟩ := kchain_ge' l x.1.t h.2 (fun y hy => hp y (List.mem_cons_of_mem _ hy))
    refine ⟨fun y hy => ?_, ?_⟩
    · rcases List.mem_cons.1 hy with rfl | hy
      · exact h.1.ge
      · have := ih1 y hy; linarith [h.1, hx.2.1]
    · show s0 ≤ tendQ x.1.t l
      linarith [h.1, hx.2.1]

/-- The chain of a template whose pieces satisfy (K0). -/
theorem ktmpl_chain' {T : KTmpl} (hch : chainOK T.t1 T.pieces = true)
    (hb : ∀ x ∈ T.pieces, PieceBasic x.1) : Chain (T.t1 : ℝ) T.toQ.real :=
  chain_real_basic (cat := []) (q := 0) (α := 0) (κ := 0) (depth := 0) (cF := 0) (Pbad := 0)
    T.pieces T.t1 hch hb

theorem ktlo_exists' {D : KBankData} (hh : ∀ x ∈ D.tmpls, ktmplHead D x.1 x.2 = true) :
    ∃ tlo : ℚ, 0 < tlo ∧ ∀ j T, findK j D.tmpls = some T → tlo ≤ T.t1 := by
  obtain ⟨t, ht0, ht⟩ := ktlo_list D.tmpls (fun x hx => (ktmplHead_facts (hh x hx)).1)
  exact ⟨t, ht0, fun j T h => ht (j, T) (findK_mem j D.tmpls h)⟩

theorem pieceBasic_of_ok {cat : List Branch} {q : ℕ} {α κ : ℚ} {depth cF Pbad : ℕ} {P : QPiece} {c : Cert}
    (h : pieceOK cat q α κ depth cF Pbad P c = true) : PieceBasic P := by
  unfold pieceOK at h
  rcases hb : nth cat c.bi with _ | br <;> simp only [hb, reduceCtorEq, Bool.false_eq_true] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hs0, hst⟩, ha0⟩, ha1⟩, hC0⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h
  exact ⟨hs0, hst, hC0, ha0, ha1⟩

/-! ### The scale -/

theorem exists_R0 (N0 : ℕ) (Rt P q : ℚ) {tlo : ℚ} (htlo : 0 < tlo) :
    ∃ R0 : ℕ, (N0 : ℝ) < tlo * R0 ∧ (Rt : ℝ) ≤ R0 ∧ (P : ℝ) ≤ R0 ∧ (q : ℝ) ≤ R0 := by
  have htl : (0 : ℝ) < tlo := by exact_mod_cast htlo
  obtain ⟨R1, hR⟩ := exists_nat_gt ((N0 : ℝ) / tlo)
  refine ⟨max R1 (max ⌈(Rt : ℝ)⌉₊ (max ⌈(P : ℝ)⌉₊ ⌈(q : ℝ)⌉₊)), ?_, ?_, ?_, ?_⟩
  · have h1 : (N0 : ℝ) < tlo * R1 := by rwa [div_lt_iff₀ htl, mul_comm] at hR
    have h2 : (R1 : ℝ) ≤ (max R1 (max ⌈(Rt : ℝ)⌉₊ (max ⌈(P : ℝ)⌉₊ ⌈(q : ℝ)⌉₊)) : ℕ) := by
      exact_mod_cast le_max_left _ _
    have := mul_le_mul_of_nonneg_left h2 htl.le
    linarith
  · have h2 : (⌈(Rt : ℝ)⌉₊ : ℝ) ≤ (max R1 (max ⌈(Rt : ℝ)⌉₊ (max ⌈(P : ℝ)⌉₊ ⌈(q : ℝ)⌉₊)) : ℕ) := by
      exact_mod_cast le_max_of_le_right (le_max_left _ _)
    exact (Nat.le_ceil _).trans h2
  · have h2 : (⌈(P : ℝ)⌉₊ : ℝ) ≤ (max R1 (max ⌈(Rt : ℝ)⌉₊ (max ⌈(P : ℝ)⌉₊ ⌈(q : ℝ)⌉₊)) : ℕ) := by
      exact_mod_cast le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
    exact (Nat.le_ceil _).trans h2
  · have h2 : (⌈(q : ℝ)⌉₊ : ℝ) ≤ (max R1 (max ⌈(Rt : ℝ)⌉₊ (max ⌈(P : ℝ)⌉₊ ⌈(q : ℝ)⌉₊)) : ℕ) := by
      exact_mod_cast le_max_of_le_right (le_max_of_le_right (le_max_right _ _))
    exact (Nat.le_ceil _).trans h2

/-- `q (r + 2 m) < p²` from `p > t r` and `q (2 + 2 α) / t² ≤ r`. -/
theorem qN_of {Q : ℕ} {α : ℚ} {r p m : ℕ} {te : ℚ} (hQ : 0 < Q) (hα : 0 ≤ α) (hr0 : 0 < r) (hte : 0 < te)
    (hm : (m : ℝ) < α * r + 1 / 2) (h1 : (Q : ℚ) * (2 + 2 * α) / (te * te) ≤ r) (hlt : (te : ℝ) * r < p) :
    Q * (r + 2 * m) < p * p := by
  have h1' : (((Q : ℚ) * (2 + 2 * α) / (te * te) : ℚ) : ℝ) ≤ r := by exact_mod_cast h1
  push_cast at h1'
  have hteR : (0 : ℝ) < te := by exact_mod_cast hte
  rw [div_le_iff₀ (mul_pos hteR hteR)] at h1'
  have hq0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr0
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr0
  have hα' : (0 : ℝ) ≤ α := by exact_mod_cast hα
  have e1 : (Q : ℝ) * (r + 2 * m) < Q * ((1 + 2 * α) * r + 1) :=
    mul_lt_mul_of_pos_left (by linarith) hq0
  have e2 : (Q : ℝ) * ((1 + 2 * α) * r + 1) ≤ Q * (2 + 2 * α) * r := by
    have := mul_le_mul_of_nonneg_left hr1 hq0.le
    linarith
  have e3 : (Q : ℝ) * (2 + 2 * α) * r ≤ (te * r) * (te * r) := by
    have := mul_le_mul_of_nonneg_right h1' hrR.le
    linarith
  have hsr : (0 : ℝ) ≤ te * r := mul_nonneg hteR.le hrR.le
  have e4 : ((te : ℝ) * r) * (te * r) < p * p := mul_self_lt_mul_self hsr hlt
  have : ((Q * (r + 2 * m) : ℕ) : ℝ) < ((p * p : ℕ) : ℝ) := by push_cast; linarith
  exact_mod_cast this

/-! ### The pole indices of the master root -/

/-- At a master root `Q k = j p + oM` the transported pole indices are roots of the shifts. -/
theorem kv_roots {D : KBankData} (hpar : KParams D) {j k p : ℕ}
    (hjs : ∀ x ∈ D.shifts, x.s * j % x.q ≠ 0) (hk : D.Q * k = j * p + D.oM) (hPb : D.Pbad < p) :
    (∀ n, D.bS j n * p + D.cS n ≤ D.tS n * k) ∧
    ∀ n < D.shifts.length, 0 < (shAt D.shifts n).q ∧ 0 < (shAt D.shifts n).o ∧
      (shAt D.shifts n).o < (shAt D.shifts n).q ∧
      (shAt D.shifts n).q * (D.tS n * k - (D.bS j n * p + D.cS n)) =
        (shAt D.shifts n).jj j * p + (shAt D.shifts n).o ∧
      0 < (shAt D.shifts n).jj j ∧ (shAt D.shifts n).jj j < (shAt D.shifts n).q ∧
      0 < D.tS n * k - (D.bS j n * p + D.cS n) ∧ D.tS n * k - (D.bS j n * p + D.cS n) < p := by
  obtain ⟨hq2, hqP, -, -, -, -, -, -, -, hsh⟩ := hpar
  have hle : ∀ n, D.bS j n * p + D.cS n ≤ D.tS n * k := by
    intro n
    by_cases hn : n < D.shifts.length
    · have hx := hsh _ (shAt_mem D.shifts n hn)
      simp only [shiftOK, Bool.and_eq_true, decide_eq_true_eq] at hx
      obtain ⟨⟨⟨⟨⟨hq0, hQ⟩, -⟩, -⟩, ho⟩, hc'⟩ := hx
      exact (Shift.kOf_spec hq0 hQ ho hc' hk).1
    · have e := shAt_out D.shifts n (by omega)
      show (shAt D.shifts n).b j * p + (shAt D.shifts n).c D.oM ≤ (shAt D.shifts n).t D.Q * k
      rw [e]
      exact kOf_out D.Q D.oM j k p
  refine ⟨hle, fun n hn => ?_⟩
  have hmem := shAt_mem D.shifts n hn
  have hx := hsh _ hmem
  simp only [shiftOK, Bool.and_eq_true, decide_eq_true_eq] at hx
  obtain ⟨⟨⟨⟨⟨hq0, hQ⟩, ho0⟩, hoq⟩, ho⟩, hc'⟩ := hx
  have hspec : (shAt D.shifts n).q * (D.tS n * k - (D.bS j n * p + D.cS n)) =
      (shAt D.shifts n).jj j * p + (shAt D.shifts n).o := (Shift.kOf_spec hq0 hQ ho hc' hk).2
  have hjj : 0 < (shAt D.shifts n).jj j := Nat.pos_of_ne_zero (hjs _ hmem)
  have hjq : (shAt D.shifts n).jj j < (shAt D.shifts n).q := Nat.mod_lt _ hq0
  refine ⟨hq0, ho0, hoq, hspec, hjj, hjq, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos (D.tS n * k - (D.bS j n * p + D.cS n)) with h0 | h0
    · rw [h0, Nat.mul_zero] at hspec
      have : 0 < (shAt D.shifts n).jj j * p + (shAt D.shifts n).o :=
        Nat.lt_of_lt_of_le ho0 (Nat.le_add_left _ _)
      rw [← hspec] at this
      exact absurd this (lt_irrefl 0)
    · exact h0
  · have hqQ : (shAt D.shifts n).q ≤ D.Q := Nat.le_of_dvd (by omega) (Nat.dvd_of_mod_eq_zero hQ)
    have hop : (shAt D.shifts n).o < p := by omega
    have h1 : (shAt D.shifts n).q * (D.tS n * k - (D.bS j n * p + D.cS n)) < (shAt D.shifts n).q * p :=
      calc _ = (shAt D.shifts n).jj j * p + (shAt D.shifts n).o := hspec
        _ < (shAt D.shifts n).jj j * p + p := Nat.add_lt_add_left hop _
        _ = ((shAt D.shifts n).jj j + 1) * p := by ring
        _ ≤ (shAt D.shifts n).q * p := Nat.mul_le_mul_right p hjq
    exact Nat.lt_of_mul_lt_mul_left h1

/-- **The compiled catalogue satisfies the branch hypothesis of Theorem B** at a master root (`branches_of_kcat`
with the frame facts as a hypothesis). -/
theorem branches_of_kcat' {D : KBankData} (hpar : KParams D) {c : ℚ} {hc : 0 < c} {const : ℝ}
    {Q : NodeFamily.Index (altGeom c hc).geometry → ℚ[X]} {depth N0 : ℕ}
    (hcat : KCatValidFam c hc const depth Q D.shifts D.Q D.Pbad N0 D.kcat)
    {j : ℕ} (hjs : ∀ x ∈ D.shifts, x.s * j % x.q ≠ 0)
    (i : (AltEvenFam c hc const depth Q).ι) (hi : (AltEvenFam c hc const depth Q).Adm i) (hr0 : 0 < i.1)
    (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : D.Q * k = j * p + D.oM) (hN : N0 < p) :
    BranchesValid (D.cat j) D.Pbad D.Q i.1 p ((altGeom c hc).borderSize i.1) k (delCount (altGeom c hc) i)
      (fun n => GLE p n ((AltEvenFam c hc const depth Q).Q i)) := by
  intro b hb hPb hqN hcond
  obtain ⟨kb, hkb, rfl⟩ := List.mem_map.1 hb
  obtain ⟨hle, hr⟩ := kv_roots hpar hjs hk hPb
  have hroots : ∀ n < D.shifts.length, ∃ jn,
      (shAt D.shifts n).q * (D.tS n * k - (D.bS j n * p + D.cS n)) = jn * p + (shAt D.shifts n).o ∧
      0 < jn ∧ jn < (shAt D.shifts n).q ∧ 0 < D.tS n * k - (D.bS j n * p + D.cS n) ∧
      D.tS n * k - (D.bS j n * p + D.cS n) < p := fun n hn => by
    obtain ⟨-, -, -, h1, h2, h3, h4, h5⟩ := hr n hn
    exact ⟨_, h1, h2, h3, h4, h5⟩
  have hcond' : ∀ cd ∈ kb.conds, cd.Holds i.1 p ((altGeom c hc).borderSize i.1)
      (fun n => D.tS n * k - (D.bS j n * p + D.cS n)) := by
    intro cd hcd
    exact (KCond.holds_compile D.tS (D.bS j) D.cS cd _ _ _ k hle).1 (hcond _ (List.mem_map.2 ⟨cd, hcd, rfl⟩))
  obtain ⟨n, hn, hnb⟩ := hcat kb hkb i hi hr0 p hPb hN hqN _ hroots hcond'
  refine ⟨n, hn, ?_⟩
  rw [KBranch.evalN_compile]
  exact hnb

/-! ### The piece bound -/

/-- **The piece bound of a piece `x` of the template of the class `j`**: at every admissible member of scale `r`
and every prime `p ∈ (s r, t r]` that is large (`p > P_bad`, `p > N0`, `q (r + 2 m) < p²`), with the master root
`Q k = j p + oM`, some clearing exponent is at most `a r + b p + C`. -/
def PieceCov (D : KBankData) (c : ℚ) (hc : 0 < c) (const : ℝ) (depth : ℕ)
    (Q : NodeFamily.Index (altGeom c hc).geometry → ℚ[X]) (N0 j : ℕ) (x : QPiece) : Prop :=
  ∀ (i : (AltEvenFam c hc const depth Q).ι), (AltEvenFam c hc const depth Q).Adm i → 0 < i.1 →
    ∀ (p k : ℕ) [Fact p.Prime], D.Q * k = j * p + D.oM → N0 < p → D.Pbad < p →
      D.Q * (i.1 + 2 * (altGeom c hc).borderSize i.1) < p * p →
      Cond.Round D.Q i.1 p ((altGeom c hc).borderSize i.1) k D.α ((j : ℚ) / D.Q) →
      (∀ y ∈ D.shifts, y.s * j % y.q ≠ 0) →
      (x.s : ℝ) * i.1 < p → (p : ℝ) ≤ x.t * i.1 →
      ∃ n, GLE p n ((AltEvenFam c hc const depth Q).Q i) ∧ (n : ℝ) ≤ x.a * i.1 + x.b * p + x.C

/-- **A head piece** (`pieceOK`) has the piece bound (Theorem B). -/
theorem head_cov {D : KBankData} (hpar : KParams D) {c : ℚ} {hc : 0 < c} {const : ℝ} {depth : ℕ}
    {Q : NodeFamily.Index (altGeom c hc).geometry → ℚ[X]} {N0 : ℕ}
    (hdepth : depth ≤ D.depth) (hQ : AltQ c hc D.cF Q)
    (hcat : KCatValidFam c hc const depth Q D.shifts D.Q D.Pbad N0 D.kcat) {j : ℕ} {x : QPiece × Cert}
    (hok : pieceOK (D.cat j) D.Q D.α ((j : ℚ) / D.Q) D.depth D.cF D.Pbad x.1 x.2 = true) :
    PieceCov D c hc const depth Q N0 j x.1 := by
  intro i hi hr0 p k _ hk hN hPb hqN hrd hjs hs ht
  have hpar' := hpar
  obtain ⟨hq2, hqP, -, -, -, -, hα, -, -, -⟩ := hpar'
  have hr2 : i.1 % 2 = 0 := hi.2
  have hcr : GLE p (2 * i.1 * (3 * Nat.log p (14 * i.1) + D.cF)) ((AltEvenFam c hc const depth Q).Q i) := by
    exact hQ.crude i hr2 p
  have hodd : D.Pbad < p → p % 2 = 1 := by
    intro hPb'
    rcases (Fact.out : p.Prime).eq_two_or_odd with h | h
    · omega
    · exact h
  have hdel : delCount (altGeom c hc) i ≤ D.depth :=
    (show delCount (altGeom c hc) i ≤ depth from hi.1).trans hdepth
  exact piece_sound x.1 x.2 hok (by omega) hα
    (fun n => GLE p n ((AltEvenFam c hc const depth Q).Q i)) hrd hodd (Fact.out : p.Prime).two_le hdel hcr
    (branches_of_kcat' hpar hcat hjs i hi hr0 p k hk hN) hs ht


/-- **An expansion piece** has the piece bound (Lemma T): the prefix branch (or `D1x`) of its cell is valid,
and its price is below the line of the piece with slack `3`. -/
theorem exp_cov {D : KBankData} (hpar : KParams D) (hlen : 2 ≤ D.shifts.length)
    {c : ℚ} {hc : 0 < c} {const : ℝ} {depth : ℕ}
    {Q : NodeFamily.Index (altGeom c hc).geometry → ℚ[X]} {N0 : ℕ}
    (hpre : ∀ n j0 j1 j2, KCatValidFam c hc const depth Q D.shifts D.Q D.Pbad N0 [kbrPre n j0 [j1, j2]])
    (hd1x : KCatValidFam c hc const depth Q D.shifts D.Q D.Pbad N0 [⟨kD1xE, [], 0⟩])
    {j n' : ℕ} (hn : 1 ≤ n') {c₀ : PCell}
    (hcell : c₀.ok D.α (kappaOf D j 0) (kappaOf D j 1) = true) :
    PieceCov D c hc const depth Q N0 j (expPiece D.α D.α.den expC n' c₀) := by
  intro i hi hr0 p k _ hk hN hPb hqN hrd hjs hs ht
  have hpar' := hpar
  obtain ⟨hq2, hqP, -, -, -, -, hα, -, -, -⟩ := hpar'
  obtain ⟨hle, hr⟩ := kv_roots hpar hjs hk hPb
  set r := i.1 with hrdef
  set m := (altGeom c hc).borderSize r with hmdef
  obtain ⟨kv, hkv⟩ : ∃ kv : ℕ → ℕ, kv = fun n => D.tS n * k - (D.bS j n * p + D.cS n) := ⟨_, rfl⟩
  have hroots : ∀ n < D.shifts.length, ∃ jn,
      (shAt D.shifts n).q * kv n = jn * p + (shAt D.shifts n).o ∧ 0 < jn ∧ jn < (shAt D.shifts n).q ∧
      0 < kv n ∧ kv n < p := fun n hn => by
    obtain ⟨-, -, -, h1, h2, h3, h4, h5⟩ := hr n hn
    subst hkv
    exact ⟨_, h1, h2, h3, h4, h5⟩
  have hkap : ∀ t < 2, kappaOf D j t * p ≤ (kv t : ℚ) ∧ (kv t : ℚ) ≤ kappaOf D j t * p + 1 := by
    intro t ht2
    obtain ⟨hq0, ho0, hoq, hspec, hjj, hjq, hk0, hkp⟩ := hr t (lt_of_lt_of_le ht2 hlen)
    have hspec' : (shAt D.shifts t).q * kv t = (shAt D.shifts t).jj j * p + (shAt D.shifts t).o := by
      subst hkv; exact hspec
    have hq : (0 : ℚ) < (shAt D.shifts t).q := by exact_mod_cast hq0
    have hsp : ((shAt D.shifts t).q : ℚ) * kv t = (shAt D.shifts t).jj j * p + (shAt D.shifts t).o := by
      exact_mod_cast hspec'
    have hoq' : ((shAt D.shifts t).o : ℚ) < (shAt D.shifts t).q := by exact_mod_cast hoq
    have ho0' : (0 : ℚ) ≤ (shAt D.shifts t).o := Nat.cast_nonneg _
    have e : kappaOf D j t * p = (kv t : ℚ) - (shAt D.shifts t).o / (shAt D.shifts t).q := by
      unfold kappaOf
      field_simp
      linarith
    have hfrac : ((shAt D.shifts t).o : ℚ) / (shAt D.shifts t).q < 1 := (div_lt_one hq).2 hoq'
    have hfrac0 : (0 : ℚ) ≤ ((shAt D.shifts t).o : ℚ) / (shAt D.shifts t).q := div_nonneg ho0' hq.le
    constructor <;> linarith
  have hpQ : (0 : ℚ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  -- the cell context
  have hnum : (0 : ℤ) ≤ D.α.num := Rat.num_nonneg.2 hα
  have hnat : ((D.α.num.toNat : ℕ) : ℚ) = (D.α.num : ℚ) := by
    have : ((D.α.num.toNat : ℕ) : ℤ) = D.α.num := Int.toNat_of_nonneg hnum
    exact_mod_cast this
  have hab : D.α * (D.α.den : ℚ) = (D.α.num.toNat : ℚ) := by
    rw [hnat]; exact Rat.mul_den_eq_num D.α
  have hb1 : 1 ≤ D.α.den := D.α.den_pos
  have hmlo := hrd.m_lo
  have hmhi := hrd.m_hi
  have hm1 : -1 / 2 ≤ (m : ℚ) - D.α * r := by
    have : ((-1 / 2 : ℚ) : ℝ) ≤ (((m : ℚ) - D.α * r : ℚ) : ℝ) := by push_cast; linarith [hmlo]
    exact_mod_cast this
  have hm2 : (m : ℚ) - D.α * r ≤ 1 / 2 := by
    have : (((m : ℚ) - D.α * r : ℚ) : ℝ) < ((1 / 2 : ℚ) : ℝ) := by push_cast; linarith [hmhi]
    have := (Rat.cast_lt (K := ℝ)).1 this
    exact this.le
  obtain ⟨hlt, hk0', -, -, -, -⟩ := c₀.ok_spec hcell
  have hkc : (0 : ℚ) ≤ c₀.kc := Nat.cast_nonneg _
  have h1 : (1 : ℚ) ≤ D.α.den := by exact_mod_cast hb1
  have h2 : (1 : ℚ) ≤ n' := by exact_mod_cast hn
  have hbn : (0 : ℚ) < (D.α.den : ℚ) * n' + c₀.u1 := by nlinarith
  have hbn0 : (0 : ℚ) < (D.α.den : ℚ) * n' + c₀.u0 := by nlinarith
  have hs' : (1 / ((D.α.den : ℚ) * n' + c₀.u1)) * (r : ℚ) < p := by
    have h := hs
    simp only [expPiece] at h
    exact_mod_cast h
  have ht' : (p : ℚ) ≤ (1 / ((D.α.den : ℚ) * n' + c₀.u0)) * (r : ℚ) := by
    have h := ht
    simp only [expPiece] at h
    exact_mod_cast h
  have hr1 : (r : ℚ) < ((D.α.den : ℚ) * n' + c₀.u1) * p := by
    rw [one_div, inv_mul_eq_div, div_lt_iff₀ hbn] at hs'
    linarith
  have hr0' : ((D.α.den : ℚ) * n' + c₀.u0) * p ≤ r := by
    rw [one_div, inv_mul_eq_div, le_div_iff₀ hbn0] at ht'
    linarith
  have hctx : CellCtx D.α (kappaOf D j 0) (kappaOf D j 1) D.α.num.toNat D.α.den n' c₀ r p m kv :=
    { hα := hα, hab := hab, hb := hb1, hn := hn, hok := hcell, hp := (Fact.out : p.Prime).pos,
      hm1 := hm1, hm2 := hm2, hk0 := (hkap 0 (by norm_num)).1, hk0' := (hkap 0 (by norm_num)).2,
      hk1 := (hkap 1 (by norm_num)).1, hk1' := (hkap 1 (by norm_num)).2, hr0 := hr0', hr1 := hr1 }
  have hcond : ∀ cd ∈ ([] : List KCond), cd.Holds r p m kv := fun cd hcd => absurd hcd List.not_mem_nil
  rcases hbr : c₀.br with _ | ⟨j0, j1, j2⟩
  · -- `D1x`
    obtain ⟨nn, hnn, hb⟩ := hd1x ⟨kD1xE, [], 0⟩ (List.mem_singleton_self _) i hi hr0 p hPb hN hqN kv hroots
      hcond
    refine ⟨nn, hnn, ?_⟩
    have h1 : (nn : ℝ) ≤ ((kD1xE.evalN r p m kv : ℕ) : ℝ) := by
      have h0 : (⟨kD1xE, [], 0⟩ : KBranch).debit = 0 := rfl
      rw [h0, Nat.zero_mul, Nat.add_zero] at hb
      have : nn ≤ kD1xE.evalN r p m kv := hb
      exact_mod_cast this
    have h2 := (Rat.cast_le (K := ℝ)).2 (d1x_bound hctx hbr)
    push_cast at h2
    simp only [expPiece, expC]
    push_cast
    linarith
  · -- the prefix branch of the cell
    obtain ⟨nn, hnn, hb⟩ := hpre (D.α.num.toNat * n' + c₀.nu) j0 j1 j2 _ (List.mem_singleton_self _) i hi hr0
      p hPb hN hqN kv hroots hcond
    refine ⟨nn, hnn, ?_⟩
    have h1 : (nn : ℝ) ≤ (((kbrPre (D.α.num.toNat * n' + c₀.nu) j0 [j1, j2]).τ.evalN r p m kv : ℕ) : ℝ) := by
      have h0 : (kbrPre (D.α.num.toNat * n' + c₀.nu) j0 [j1, j2]).debit = 0 := rfl
      rw [h0, Nat.zero_mul, Nat.add_zero] at hb
      have : nn ≤ (kbrPre (D.α.num.toNat * n' + c₀.nu) j0 [j1, j2]).τ.evalN r p m kv := hb
      exact_mod_cast this
    have h2 := (Rat.cast_le (K := ℝ)).2 (pre_bound hctx hbr)
    push_cast at h2
    simp only [expPiece, expC]
    push_cast
    linarith

/-! ### Theorem C3 -/

set_option maxHeartbeats 4000000 in
/-- **Theorem D with `PieceBasic` and `PieceCov` in place of `pieceOK`** (the proof of
`hasScaledContent_of_kcheckFam`). -/
theorem hasScaledContent_of_facts (D : KBankData) (hpar : KParams D)
    (hcls : kclassOK D = true) (hheads : ∀ x ∈ D.tmpls, ktmplHead D x.1 x.2 = true)
    (c : ℚ) (hc : 0 < c) (hcα : c = 2 * D.α)
    (const : ℝ) (depth : ℕ) (Q : NodeFamily.Index (altGeom c hc).geometry → ℚ[X])
    (hQ : AltQ c hc D.cF Q) (B : SmallBudget)
    (N0 : ℕ) (hbas : ∀ x ∈ D.tmpls, ∀ y ∈ x.2.pieces, PieceBasic y.1)
    (hcov : ∀ x ∈ D.tmpls, ∀ y ∈ x.2.pieces, PieceCov D c hc const depth Q N0 x.1 y.1)
    (hcat : KCatValidFam c hc const depth Q D.shifts D.Q D.Pbad N0 D.kcat)
    (hpre : PreValidFam c hc const depth Q D.M B D.t0 D.α0b) :
    HasScaledContent (AltEvenFam c hc const depth Q) (altGeom c hc).scale (D.Λ : ℝ) := by
  classical
  have hpar' := hpar
  obtain ⟨hq2, hqP, hM0, hMq, ha0, haq, hα, hα0b, hα0, -⟩ := hpar'
  haveI : NeZero D.M := ⟨by omega⟩
  have hmem := hcls
  simp only [kclassOK, Bool.and_eq_true, decide_eq_true_eq] at hmem
  obtain ⟨hcls', hsum⟩ := hmem
  -- the template of a unit class
  have hclass : ∀ c' : ZMod D.M, IsUnit c' →
      ∃ j T, jOf D.Q D.a c'.val = some j ∧ findK j D.tmpls = some T := by
    intro c' hc'
    have hcop : D.M.Coprime c'.val := by
      have : IsUnit ((c'.val : ℕ) : ZMod D.M) := by rwa [ZMod.natCast_zmod_val]
      exact ((ZMod.isUnit_iff_coprime c'.val D.M).1 this).symm
    have := unitAll_spec D.M _ D.M hcls' c'.val (ZMod.val_lt c') hcop
    rcases hj : jOf D.Q D.a c'.val with _ | j <;> simp only [hj, Bool.false_eq_true] at this
    rcases hT : findK j D.tmpls with _ | T <;> simp only [hT, Option.isSome_none, Bool.false_eq_true] at this
    exact ⟨j, T, rfl, hT⟩
  have htmpl : ∀ c' : ZMod D.M, ∀ j T, jOf D.Q D.a c'.val = some j → findK j D.tmpls = some T →
      ktmplOf D c' = mkTemplate D.α0 T.toQ := by
    intro c' j T hj hT
    unfold ktmplOf; rw [hj]; simp only [hT]
  -- the master root datum of a prime in the class `c'`
  have hdatum : ∀ (c' : ZMod D.M) (j : ℕ) (p : ℕ), jOf D.Q D.a c'.val = some j → (p : ZMod D.M) = c' →
      j < D.Q ∧ 0 < j ∧ D.Q * ((j * p) / D.Q + 1) = j * p + (D.Q - D.a) := by
    intro c' j p hj hpc
    have hpc' : p % D.M = c'.val := by rw [← hpc, ZMod.val_natCast]
    exact root_datum hq2 hMq ha0 haq hj hpc'
  -- the facts of the template found for a class
  have hfind : ∀ j T, findK j D.tmpls = some T → (j, T) ∈ D.tmpls := fun j T h => findK_mem j D.tmpls h
  -- the scale `R0`
  obtain ⟨tlo, htlo0, htlo⟩ := ktlo_exists' hheads
  have htl : (0 : ℝ) < tlo := by exact_mod_cast htlo0
  obtain ⟨R0, hR0, hRt, hRP, hRq⟩ := exists_R0 N0 D.Rt ((D.Pbad : ℚ) / tlo)
    ((D.Q : ℚ) * (2 + 2 * D.α) / (tlo * tlo)) htlo0
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
  refine hasScaledContent_lift (AltEvenFam c hc const depth Q) (altGeom c hc).scale (D.Λ : ℝ) R0
    (fun i => hQ.deg i) ?_
  refine altContent_of_bounds c hc D.cF const depth R0 Q hQ D.M D.Λ B (fun _ => ktmplOf D) D.τ ?_ ?_ ?_ ?_ ?_
  · -- hmass (D6)
    intro ε hε
    have hcc : contentConstant D.M (ktmplOf D) = D.Λ := by
      unfold contentConstant
      have h1 : ∀ c' ∈ unitClasses D.M, (ktmplOf D c').mass = ((kclassMass D c'.val : ℚ) : ℝ) := by
        intro c' hc'
        obtain ⟨j, T, hj, hT⟩ := hclass c' (mem_unitClasses.1 hc')
        obtain ⟨ht1, -, hch, -⟩ := ktmplHead_facts (hheads _ (hfind j T hT))
        have hbT := hbas _ (hfind j T hT)
        rw [htmpl c' j T hj hT, mass_mkTemplate_of (T := T.toQ) hα0 ht1 (ktmpl_chain' hch hbT)]
        simp [kclassMass, hj, hT]
      rw [Finset.sum_congr rfl h1, sum_unitClasses D.M (fun x => ((kclassMass D x : ℚ) : ℝ)),
        ← unitSum_eq, hsum, Nat.totient_eq_card_coprime, ← unitCount_eq]
      have hpos : 0 < unitCount D.M D.M := by
        rw [unitCount_eq, ← Nat.totient_eq_card_coprime]; exact Nat.totient_pos.2 (by omega)
      push_cast
      field_simp
    rw [hcc]; linarith
  · -- tend_le
    intro ε hε c' hc'
    obtain ⟨j, T, hj, hT⟩ := hclass c' hc'
    obtain ⟨ht1, -, hch, -, -, hte⟩ := ktmplHead_facts (hheads _ (hfind j T hT))
    have hbT := hbas _ (hfind j T hT)
    rw [htmpl c' j T hj hT, tend_mkTemplate_of (T := T.toQ) hα0 ht1 (ktmpl_chain' hch hbT)]
    exact_mod_cast hte
  · -- tail: the tail branch of the class
    intro ε hε i hi c' hc' p hp hpc hlt _
    have hr2 : i.1 % 2 = 0 := hi.1.2
    rcases Nat.eq_zero_or_pos i.1 with h0 | hr0
    · have := hQ.crude i hr2 p
      have h00 : Ecrude D.cF i.1 p = 0 := by simp [Ecrude, h0]
      rw [h00] at this
      exact this
    obtain ⟨j, T, hj, hT⟩ := hclass c' hc'
    obtain ⟨hjq, hj0, hk⟩ := hdatum c' j p hj hpc
    set k := (j * p) / D.Q + 1 with hkdef
    rw [htmpl c' j T hj hT] at hlt
    obtain ⟨ht1, -, hch, hjs, htail, hte⟩ := ktmplHead_facts (hheads _ (hfind j T hT))
    have hbT := hbas _ (hfind j T hT)
    rw [tend_mkTemplate_of (T := T.toQ) hα0 ht1 (ktmpl_chain' hch hbT)] at hlt
    set te := tendQ T.t1 T.pieces with hte'
    unfold tailOK at htail
    rcases hbr : nth (D.cat j) T.tb with _ | br <;> simp only [hbr, reduceCtorEq, Bool.false_eq_true] at htail
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at htail
    obtain ⟨⟨⟨⟨⟨hz, hd0⟩, hcs⟩, hte0⟩, hRq'⟩, hRP'⟩ := htail
    have hbm := nth_mem (D.cat j) T.tb hbr
    have hteR : (0 : ℝ) < te := by exact_mod_cast hte0
    have hr0' : (0 : ℝ) ≤ i.1 := Nat.cast_nonneg _
    have hrR : (0 : ℝ) < i.1 := by exact_mod_cast hr0
    have hlt' : (te : ℝ) * i.1 < p := (Nat.floor_lt (mul_nonneg hteR.le hr0')).1 hlt
    have hRr : (D.Rt : ℝ) ≤ i.1 := by
      have : (R0 : ℝ) ≤ i.1 := by exact_mod_cast hi.2
      linarith
    have hPb : D.Pbad < p := by
      have h1 : (((D.Pbad : ℚ) / te : ℚ) : ℝ) ≤ i.1 := by
        have := (Rat.cast_le (K := ℝ)).2 hRP'; linarith
      push_cast at h1
      rw [div_le_iff₀ hteR] at h1
      have : (D.Pbad : ℝ) < p := by nlinarith
      exact_mod_cast this
    have hrd := round_of (D := D.toBank) c hc hcα hr2 hq2 ha0 haq hk (r := i.1)
    set m := (altGeom c hc).borderSize i.1 with hm
    have hqN : D.Q * (i.1 + 2 * m) < p * p := by
      have hm2 : (m : ℝ) < D.α * i.1 + 1 / 2 := by
        have h := hrd.m_hi
        change (m : ℝ) - ((D.α : ℚ) : ℝ) * (i.1 : ℝ) < 1 / 2 at h
        linarith
      have hRq2 : (D.Q : ℚ) * (2 + 2 * D.α) / (te * te) ≤ (i.1 : ℚ) := by
        have : D.Rt ≤ (i.1 : ℚ) := by exact_mod_cast hRr
        exact hRq'.trans this
      exact qN_of (by omega) hα hr0 (by exact_mod_cast hte0) hm2 hRq2 hlt'
    have hN0p : N0 < p := by
      have hge := (kchain_ge' T.pieces T.t1 hch hbT).2
      have : (te : ℚ) ≥ tlo := le_trans (htlo j T hT) hge
      exact hN0 i.1 p te hi.2 this hlt'
    have hcond : ∀ cd ∈ br.conds, cd.Holds i.1 p m k := by
      intro cd hcd
      obtain ⟨⟨hl1, hlv⟩, hR⟩ := hcs cd hcd
      apply Cond.holds_large cd hrd
      have hlvR : (0 : ℝ) < ((cd.lv D.α ((j : ℚ) / D.Q) te : ℚ) : ℝ) := by exact_mod_cast hlv
      have h5 : ((((1 - cd.etaLo D.Q) / cd.lv D.α ((j : ℚ) / D.Q) te : ℚ)) : ℝ) ≤ i.1 := by
        have := (Rat.cast_le (K := ℝ)).2 hR; linarith
      rw [Rat.cast_div, div_le_iff₀ hlvR, Rat.cast_sub, Rat.cast_one] at h5
      have e1 : (cd.ell0 D.α : ℝ) * i.1 + (cd.ell1 ((j : ℚ) / D.Q) : ℝ) * p =
          i.1 * ((cd.lv D.α ((j : ℚ) / D.Q) te : ℚ) : ℝ) + (cd.ell1 ((j : ℚ) / D.Q) : ℝ) * ((p : ℝ) - te * i.1) := by
        rw [lv_real]; ring
      have hl1R : (0 : ℝ) ≤ (cd.ell1 ((j : ℚ) / D.Q) : ℝ) := by exact_mod_cast hl1
      have h6 : 0 ≤ (cd.ell1 ((j : ℚ) / D.Q) : ℝ) * ((p : ℝ) - te * i.1) := mul_nonneg hl1R (by linarith)
      show 1 - ((cd.etaLo D.Q : ℚ) : ℝ) ≤ (cd.ell0 D.α : ℝ) * i.1 + (cd.ell1 ((j : ℚ) / D.Q) : ℝ) * p
      linarith
    obtain ⟨n, hn, hnb⟩ := branches_of_kcat' hpar hcat hjs i hi.1 hr0 p k hk hN0p br hbm hPb hqN hcond
    rw [evalN_of_isZero hz, hd0, Nat.zero_mul, Nat.add_zero] at hnb
    have : n = 0 := by omega
    rw [this] at hn
    exact hn
  · -- pre (D3)
    intro ε hε i hi c' hc' p h1 hp hpc _
    obtain ⟨j, T, hj, hT⟩ := hclass c' hc'
    obtain ⟨ht1, ht0, hch, -⟩ := ktmplHead_facts (hheads _ (hfind j T hT))
    have hbT := hbas _ (hfind j T hT)
    rw [htmpl c' j T hj hT, mkTemplate_eq_of (T := T.toQ) hα0 ht1 (ktmpl_chain' hch hbT)] at h1 ⊢
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
  · -- cov (D5)
    intro ε hε i hi c' hc' P hP p h1 h2 hp hpc _
    obtain ⟨j, T, hj, hT⟩ := hclass c' hc'
    obtain ⟨ht1, -, hch, hjs, -⟩ := ktmplHead_facts (hheads _ (hfind j T hT))
    have hbT := hbas _ (hfind j T hT)
    rw [htmpl c' j T hj hT, mkTemplate_eq_of (T := T.toQ) hα0 ht1 (ktmpl_chain' hch hbT)] at hP
    simp only [QTmpl.real, KTmpl.toQ, List.mem_map] at hP
    obtain ⟨x, hx, rfl⟩ := hP
    have hxb := hbT x hx
    obtain ⟨hk, hj0, hk'⟩ := hdatum c' j p hj hpc
    have hr2 : i.1 % 2 = 0 := hi.1.2
    have hs0 : (0 : ℝ) ≤ (x.1.s : ℝ) * i.1 := by
      have : (0 : ℝ) < x.1.s := by exact_mod_cast hxb.1
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
    have hrd := round_of (D := D.toBank) c hc hcα hr2 hq2 ha0 haq hk' (r := i.1)
    have hge := (kchain_ge' T.pieces T.t1 hch hbT).1 x hx
    have hsl : tlo ≤ x.1.s := le_trans (htlo j T hT) hge
    have hN : N0 < p := hN0 i.1 p x.1.s hi.2 hsl hs
    have htlr : (tlo : ℝ) * i.1 < p := by
      have : (tlo : ℝ) ≤ x.1.s := by exact_mod_cast hsl
      have := mul_le_mul_of_nonneg_right this (Nat.cast_nonneg i.1)
      linarith
    have hPb : D.Pbad < p := by
      have h1 : (((D.Pbad : ℚ) / tlo : ℚ) : ℝ) ≤ i.1 := by
        have : (R0 : ℝ) ≤ i.1 := by exact_mod_cast hi.2
        linarith
      push_cast at h1
      rw [div_le_iff₀ htl] at h1
      have : (D.Pbad : ℝ) < p := by nlinarith
      exact_mod_cast this
    have hqN : D.Q * (i.1 + 2 * (altGeom c hc).borderSize i.1) < p * p := by
      have hm2 : (((altGeom c hc).borderSize i.1 : ℕ) : ℝ) < D.α * i.1 + 1 / 2 := by
        have h := hrd.m_hi
        change (((altGeom c hc).borderSize i.1 : ℕ) : ℝ) - ((D.α : ℚ) : ℝ) * (i.1 : ℝ) < 1 / 2 at h
        linarith
      refine qN_of (by omega) hα hr0 htlo0 hm2 ?_ htlr
      have : (R0 : ℝ) ≤ i.1 := by exact_mod_cast hi.2
      have h3 : (D.Q : ℚ) * (2 + 2 * D.α) / (tlo * tlo) ≤ (i.1 : ℚ) := by exact_mod_cast (hRq.trans this)
      exact h3
    obtain ⟨n, hn, hb⟩ := hcov _ (hfind j T hT) x hx i hi.1 hr0 p _ hk' hN hPb hqN hrd hjs hs ht
    exact ⟨n, hn, hb⟩

/-- The facts of an accepted closed bank. -/
theorem kcheckC_facts {E : KBankDataC} (h : kcheckC E = true) :
    KParams E.toK ∧ 2 ≤ E.shifts.length ∧ 0 < E.α ∧ kclassOK E.toK = true ∧
    (∀ x ∈ E.toK.tmpls, ktmplHead E.toK x.1 x.2 = true) ∧
    (∀ y ∈ E.tmpls, ∀ c ∈ y.2.cells,
      c.ok E.α (kappaOf E.toK y.1 0) (kappaOf E.toK y.1 1) = true) ∧
    (∀ y ∈ E.tmpls, kpieceAll E.toK y.1 y.2.head = true) ∧ (∀ y ∈ E.tmpls, 1 ≤ y.2.N) := by
  simp only [kcheckC, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  simp only [kcParams, Bool.and_eq_true, decide_eq_true_eq] at h1
  obtain ⟨⟨hp, hlen⟩, hα⟩ := h1
  simp only [kcHeads, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h2
  simp only [kcCells, List.all_eq_true] at h3
  simp only [kcPieces, List.all_eq_true] at h4
  refine ⟨kparams_of hp, hlen, hα, h5, ?_, fun y hy => h3 y hy, fun y hy => h4 y hy, fun y hy => (h2 y hy).2⟩
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
  exact (h2 y hy).1

/-- **Theorem C3** (family form): a closed `k`-shift bank that passes `kcheckC`, with the valid catalogue, the
valid prefix branches of every strip and the valid branch `D1x`, has the scaled content `Λ`. -/
theorem hasScaledContent_of_kcheckC (E : KBankDataC) (hE : kcheckC E = true)
    (c : ℚ) (hc : 0 < c) (hcα : c = 2 * E.α) (const : ℝ) (depth : ℕ)
    (Q : NodeFamily.Index (altGeom c hc).geometry → ℚ[X]) (hdepth : depth ≤ E.depth)
    (hQ : AltQ c hc E.cF Q) (B : SmallBudget) (N0 : ℕ)
    (hcat : KCatValidFam c hc const depth Q E.shifts E.Q E.Pbad N0 E.kcat)
    (hpre : ∀ n j0 j1 j2, KCatValidFam c hc const depth Q E.shifts E.Q E.Pbad N0 [kbrPre n j0 [j1, j2]])
    (hd1x : KCatValidFam c hc const depth Q E.shifts E.Q E.Pbad N0 [⟨kD1xE, [], 0⟩])
    (hPre : PreValidFam c hc const depth Q E.M B E.t0 E.α0b) :
    HasScaledContent (AltEvenFam c hc const depth Q) (altGeom c hc).scale (E.Λ : ℝ) := by
  obtain ⟨hpar, hlen, hαpos, hcls, hheads, hcells, hpieces, hN1⟩ := kcheckC_facts hE
  have hα0 : 0 ≤ E.α := hαpos.le
  have hb1 : 1 ≤ E.α.den := E.α.den_pos
  refine hasScaledContent_of_facts E.toK hpar hcls hheads c hc hcα const depth Q hQ B N0 ?_ ?_ hcat hPre
  · intro x hx z hz
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    simp only [KTmplC.toK, List.mem_append, List.mem_map] at hz
    rcases hz with ⟨e, he, rfl⟩ | hz
    · obtain ⟨n', c₀, hn1, -, hc₀, rfl⟩ := mem_expList he
      exact expPiece_basic hα0 hb1 hn1 (hcells y hy c₀ hc₀) (by norm_num [expC])
    · have hall := hpieces y hy
      simp only [kpieceAll, List.all_eq_true] at hall
      exact pieceBasic_of_ok (hall z hz)
  · intro x hx z hz
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    simp only [KTmplC.toK, List.mem_append, List.mem_map] at hz
    rcases hz with ⟨e, he, rfl⟩ | hz
    · obtain ⟨n', c₀, hn1, -, hc₀, rfl⟩ := mem_expList he
      exact exp_cov hpar hlen hpre hd1x hn1 (hcells y hy c₀ hc₀)
    · have hall := hpieces y hy
      simp only [kpieceAll, List.all_eq_true] at hall
      exact head_cov hpar hdepth hQ hcat (hall z hz)

/-! ### Assembling a closed bank from shared facts about the expansion

The expansion of a class (the same for the two supports of a plane) is checked once.  The head conditions of
`ktmplHead` and the mass of the template are then assembled from the checked facts: `chainOK` and `tendQ` split
over `++`, and the mass is additive. -/

theorem chainOK_append : ∀ (l1 l2 : List (QPiece × Cert)) (s0 : ℚ),
    chainOK s0 (l1 ++ l2) = (chainOK s0 l1 && chainOK (tendQ s0 l1) l2)
  | [], l2, s0 => by simp [chainOK, tendQ]
  | x :: l1, l2, s0 => by
    simp only [List.cons_append, chainOK, tendQ, Bool.and_assoc]
    rw [chainOK_append l1 l2 x.1.t]

theorem tendQ_append : ∀ (l1 l2 : List (QPiece × Cert)) (s0 : ℚ),
    tendQ s0 (l1 ++ l2) = tendQ (tendQ s0 l1) l2
  | [], l2, s0 => by simp [tendQ]
  | x :: l1, l2, s0 => by
    simp only [List.cons_append, tendQ]
    exact tendQ_append l1 l2 x.1.t

/-- The expansion pieces of `N` strips of the cells, with their (inert) certificates. -/
def expPs (α : ℚ) (N : ℕ) (cells : List PCell) : List (QPiece × Cert) :=
  (expList α α.den expC N cells).map (fun q => (q, dummyCert))

/-- The expansion pieces of a closed template. -/
def KTmplC.expP (α : ℚ) (T : KTmplC) : List (QPiece × Cert) := expPs α T.N T.cells

theorem KTmplC.toK_pieces (α : ℚ) (T : KTmplC) : (T.toK α).pieces = T.expP α ++ T.head := rfl

/-- `ktmplHead` of a closed template from the facts about its expansion and head. -/
theorem ktmplHead_toK_of {D : KBankData} {α : ℚ} {T : KTmplC} {j : ℕ} {e0 : ℚ}
    (h1 : 0 < T.t1) (h2 : T.t1 ≤ D.t0) (hc1 : chainOK T.t1 (T.expP α) = true)
    (he : tendQ T.t1 (T.expP α) = e0) (hc2 : chainOK e0 T.head = true)
    (hs : D.shifts.all (fun x => decide (x.s * j % x.q ≠ 0)) = true)
    (ht : tailOK D j (tendQ e0 T.head) T.tb = true) (hτ : tendQ e0 T.head ≤ D.τ) :
    ktmplHead D j (T.toK α) = true := by
  have hp : (T.toK α).pieces = T.expP α ++ T.head := rfl
  have ht1 : (T.toK α).t1 = T.t1 := rfl
  have htb : (T.toK α).tb = T.tb := rfl
  simp only [ktmplHead, Bool.and_eq_true, decide_eq_true_eq, hp, ht1, htb, chainOK_append, tendQ_append, hc1,
    he, hc2, hs, ht, Bool.true_and, and_true]
  exact ⟨⟨h1, h2⟩, hτ⟩

/-- The mass of a closed template is additive. -/
theorem KTmplC.mass_toK (α α0 : ℚ) (T : KTmplC) :
    (T.toK α).toQ.mass α0 = α0 * T.t1 + ((T.expP α).map (fun x => x.1.mass)).sum +
      (T.head.map (fun x => x.1.mass)).sum := by
  simp only [KTmpl.toQ, QTmpl.mass, KTmplC.toK_pieces, List.map_append, List.sum_append, add_assoc]
  rfl

/-- `kclassOK` for a bank with `M = Q = 6` (unit classes `1`, `5`) and the member `a ∈ {1, 5}`: the two class masses
add up to `2 Λ`. -/
theorem kclassOK_six (D : KBankData) (hM : D.M = 6) (hQ : D.Q = 6) (ha : D.a = 1 ∨ D.a = 5)
    {T1 T5 : KTmpl} (h1 : findK 1 D.tmpls = some T1) (h5 : findK 5 D.tmpls = some T5)
    (hm : T1.toQ.mass D.α0 + T5.toQ.mass D.α0 = D.Λ * 2) : kclassOK D = true := by
  have hu : ∀ f : ℕ → ℚ, unitSum 6 f 6 = f 1 + f 5 := fun f => by simp [unitSum]
  have hall : ∀ P : ℕ → Bool, unitAll 6 P 6 = (P 1 && P 5) := fun P => by simp [unitAll]
  have hc : unitCount 6 6 = 2 := by decide
  unfold kclassOK
  rw [hM, hQ]
  rcases ha with ha | ha
  · have j1 : jOf 6 1 1 = some 1 := by decide
    have j5 : jOf 6 1 5 = some 5 := by decide
    simp only [hall, hu, hc, ha, j1, j5, h1, h5, kclassMass, hQ, Option.isSome_some, Bool.and_self,
      Bool.and_true, Bool.true_and, decide_eq_true_eq]
    exact hm
  · have j1 : jOf 6 5 1 = some 5 := by decide
    have j5 : jOf 6 5 5 = some 1 := by decide
    simp only [hall, hu, hc, ha, j1, j5, h1, h5, kclassMass, hQ, Option.isSome_some, Bool.and_self,
      Bool.and_true, Bool.true_and, decide_eq_true_eq]
    exact (add_comm _ _).trans hm

theorem kcheckC_of {E : KBankDataC} (h1 : kcParams E = true) (h2 : kcHeads E = true) (h3 : kcCells E = true)
    (h4 : kcPieces E = true) (h5 : kcClass E = true) : kcheckC E = true := by
  simp only [kcheckC, Bool.and_eq_true]
  exact ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩

end CatalanCore.Uniform.Content.BankShared.KTerm
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.exp_cov
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.head_cov
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.hasScaledContent_of_facts
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.hasScaledContent_of_kcheckC
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.ktmplHead_toK_of
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.KTmplC.mass_toK
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.kcheckC_of
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.kclassOK_six
