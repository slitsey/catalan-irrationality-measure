module

public import CatalanCore.Uniform.Content.BankShared.KTerm.Bank
public import CatalanCore.Uniform.Content.BankShared.Check.Content

@[expose] public section
set_option Elab.async false

/-! # Theorem D for k-shift banks (lane K)

* `KCatValid`: the branch theorems of a k-shift catalogue, stated with the bank's own pole indices: for every
  admissible member, every prime `p > P_bad` with `Q(r+2m) < p²`, and every vector `kv` with
  `q_i kv_i = j_i p + o_i`, `0 < j_i < q_i`, `0 < kv_i < p` for each shift `i`;
* `branches_of_kcat`: at a master root `Q k = j p + (Q - a)` the compiled catalogue `cat D j` satisfies the
  one-lattice branch hypothesis `Check.BranchesValid` of Theorem B (root transport `Shift.kOf_spec`,
  `evalN_compile`, `holds_compile`);
* **Theorem D** `hasScaledContent_of_kcheck`: `kcheck D = true`, `KCatValid` and the prefix statement give
  `HasScaledContent (AltEven c Fr depth) scale Λ_fin` (`c = 2α`).  The tail is the class's tail branch (price `0`),
  valid beyond `tend` at scales `≥ R_t` by Lemma 2 (iii); there is no built-in table T. -/

namespace CatalanCore.Uniform.Content.BankShared.KTerm
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.BankShared
  CatalanCore.Uniform.Content.SmallPrimes CatalanCore.Uniform.Content.Member CatalanCore.Arith.Hybrid
  CatalanCore.Basic Filter Finset CatalanCore.Uniform.Content.BankShared.Check

/-- **The k-shift catalogue is valid** for the frame `Fr` with shifts `sh` (`N0` is never evaluated). -/
def KCatValid (c : ℚ) (hc : 0 < c) (Fr : Frame) (depth : ℕ) (sh : List Shift) (Q Pbad N0 : ℕ)
    (cat : List KBranch) : Prop :=
  ∀ b ∈ cat, ∀ i : (AltEven c hc Fr depth).ι, (AltEven c hc Fr depth).Adm i → 0 < i.1 →
    ∀ (p : ℕ) [Fact p.Prime], Pbad < p → N0 < p →
    Q * (i.1 + 2 * (altGeom c hc).borderSize i.1) < p * p →
    ∀ kv : ℕ → ℕ, (∀ n < sh.length, ∃ jn, (shAt sh n).q * kv n = jn * p + (shAt sh n).o ∧ 0 < jn ∧
      jn < (shAt sh n).q ∧ 0 < kv n ∧ kv n < p) →
    (∀ cd ∈ b.conds, cd.Holds i.1 p ((altGeom c hc).borderSize i.1) kv) →
    ∃ n, GLE p n ((AltEven c hc Fr depth).Q i) ∧
      n ≤ b.τ.evalN i.1 p ((altGeom c hc).borderSize i.1) kv + b.debit * delCount (altGeom c hc) i

/-- The two-term bank data carrying `Q` and `α` (to reuse `Check.round_of`). -/
def KBankData.toBank (D : KBankData) : BankData :=
  ⟨D.Q, D.M, D.α, [], D.depth, D.cF, D.Pbad, D.α0, D.τ, D.Λ, D.α0b, D.t0, [], []⟩

theorem kchain_ge {cat : List Branch} {q : ℕ} {α κ : ℚ} {depth cF Pbad : ℕ} :
    ∀ (l : List (QPiece × Cert)) (s0 : ℚ), chainOK s0 l = true →
      (∀ x ∈ l, pieceOK cat q α κ depth cF Pbad x.1 x.2 = true) →
      (∀ x ∈ l, s0 ≤ x.1.s) ∧ s0 ≤ tendQ s0 l
  | [], _, _, _ => ⟨fun _ h => absurd h List.not_mem_nil, le_refl _⟩
  | x :: l, s0, h, hp => by
    simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq] at h
    have hx := pieceOK_lt (hp x List.mem_cons_self)
    obtain ⟨ih1, ih2⟩ := kchain_ge l x.1.t h.2 (fun y hy => hp y (List.mem_cons_of_mem _ hy))
    refine ⟨fun y hy => ?_, ?_⟩
    · rcases List.mem_cons.1 hy with rfl | hy
      · exact h.1.ge
      · have := ih1 y hy; linarith [h.1, hx.2]
    · show s0 ≤ tendQ x.1.t l
      linarith [h.1, hx.2]

theorem ktlo_list : ∀ l : List (ℕ × KTmpl), (∀ x ∈ l, 0 < x.2.t1) →
    ∃ tlo : ℚ, 0 < tlo ∧ ∀ x ∈ l, tlo ≤ x.2.t1
  | [], _ => ⟨1, one_pos, fun _ h => absurd h List.not_mem_nil⟩
  | x :: l, h => by
    obtain ⟨t, ht0, ht⟩ := ktlo_list l (fun y hy => h y (List.mem_cons_of_mem _ hy))
    refine ⟨min x.2.t1 t, lt_min (h x List.mem_cons_self) ht0, fun y hy => ?_⟩
    rcases List.mem_cons.1 hy with rfl | hy
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (ht y hy)

theorem ktlo_exists {D : KBankData} (hD : kcheck D = true) :
    ∃ tlo : ℚ, 0 < tlo ∧ ∀ j T, findK j D.tmpls = some T → tlo ≤ T.t1 := by
  obtain ⟨t, ht0, ht⟩ := ktlo_list D.tmpls (fun x hx => by
    have h := hD
    simp only [kcheck, Bool.and_eq_true, List.all_eq_true] at h
    have := h.1.2 x hx
    simp only [ktmplOK, ktmplHead, Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1.1.1.1.1.1)
  exact ⟨t, ht0, fun j T h => ht (j, T) (findK_mem j D.tmpls h)⟩

/-- **The compiled catalogue satisfies the branch hypothesis of Theorem B** at a master root. -/
theorem branches_of_kcat {D : KBankData} (hD : kcheck D = true) {c : ℚ} {hc : 0 < c} {Fr : Frame}
    {depth N0 : ℕ} (hcat : KCatValid c hc Fr depth D.shifts D.Q D.Pbad N0 D.kcat)
    {j : ℕ} (hjs : ∀ x ∈ D.shifts, x.s * j % x.q ≠ 0)
    (i : (AltEven c hc Fr depth).ι) (hi : (AltEven c hc Fr depth).Adm i) (hr0 : 0 < i.1)
    (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : D.Q * k = j * p + D.oM) (hN : N0 < p) :
    BranchesValid (D.cat j) D.Pbad D.Q i.1 p ((altGeom c hc).borderSize i.1) k (delCount (altGeom c hc) i)
      (fun n => GLE p n ((AltEven c hc Fr depth).Q i)) := by
  intro b hb hPb hqN hcond
  obtain ⟨hq2, hqP, -, -, -, -, -, -, -, hsh⟩ := kcheck_params hD
  obtain ⟨kb, hkb, rfl⟩ := List.mem_map.1 hb
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
  have hroots : ∀ n < D.shifts.length, ∃ jn,
      (shAt D.shifts n).q * (D.tS n * k - (D.bS j n * p + D.cS n)) = jn * p + (shAt D.shifts n).o ∧
      0 < jn ∧ jn < (shAt D.shifts n).q ∧ 0 < D.tS n * k - (D.bS j n * p + D.cS n) ∧
      D.tS n * k - (D.bS j n * p + D.cS n) < p := by
    intro n hn
    have hmem := shAt_mem D.shifts n hn
    have hx := hsh _ hmem
    simp only [shiftOK, Bool.and_eq_true, decide_eq_true_eq] at hx
    obtain ⟨⟨⟨⟨⟨hq0, hQ⟩, ho0⟩, hoq⟩, ho⟩, hc'⟩ := hx
    have hspec : (shAt D.shifts n).q * (D.tS n * k - (D.bS j n * p + D.cS n)) =
        (shAt D.shifts n).jj j * p + (shAt D.shifts n).o := (Shift.kOf_spec hq0 hQ ho hc' hk).2
    have hjj : 0 < (shAt D.shifts n).jj j := Nat.pos_of_ne_zero (hjs _ hmem)
    have hjq : (shAt D.shifts n).jj j < (shAt D.shifts n).q := Nat.mod_lt _ hq0
    refine ⟨(shAt D.shifts n).jj j, hspec, hjj, hjq, ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos (D.tS n * k - (D.bS j n * p + D.cS n)) with h0 | h0
      · rw [h0, Nat.mul_zero] at hspec
        have : 0 < (shAt D.shifts n).jj j * p + (shAt D.shifts n).o :=
          Nat.lt_of_lt_of_le ho0 (Nat.le_add_left _ _)
        rw [← hspec] at this
        exact absurd this (lt_irrefl 0)
      · exact h0
    · have hqQ : (shAt D.shifts n).q ≤ D.Q :=
        Nat.le_of_dvd (by omega) (Nat.dvd_of_mod_eq_zero hQ)
      have hop : (shAt D.shifts n).o < p := by omega
      have h1 : (shAt D.shifts n).q * (D.tS n * k - (D.bS j n * p + D.cS n)) < (shAt D.shifts n).q * p :=
        calc _ = (shAt D.shifts n).jj j * p + (shAt D.shifts n).o := hspec
          _ < (shAt D.shifts n).jj j * p + p := Nat.add_lt_add_left hop _
          _ = ((shAt D.shifts n).jj j + 1) * p := by ring
          _ ≤ (shAt D.shifts n).q * p := Nat.mul_le_mul_right p hjq
      exact Nat.lt_of_mul_lt_mul_left h1
  have hcond' : ∀ cd ∈ kb.conds, cd.Holds i.1 p ((altGeom c hc).borderSize i.1)
      (fun n => D.tS n * k - (D.bS j n * p + D.cS n)) := by
    intro cd hcd
    exact (KCond.holds_compile D.tS (D.bS j) D.cS cd _ _ _ k hle).1 (hcond _ (List.mem_map.2 ⟨cd, hcd, rfl⟩))
  obtain ⟨n, hn, hnb⟩ := hcat kb hkb i hi hr0 p hPb hN hqN _ hroots hcond'
  refine ⟨n, hn, ?_⟩
  rw [KBranch.evalN_compile]
  exact hnb

set_option maxHeartbeats 1000000 in
/-- **Theorem D for k-shift banks** (finite form). -/
theorem hasScaledContent_of_kcheck (D : KBankData) (hD : kcheck D = true)
    (c : ℚ) (hc : 0 < c) (hc1 : c ≤ 1) (hcα : c = 2 * D.α)
    (Fr : Frame) (depth : ℕ) (hdepth : depth ≤ D.depth) (hcF : cFr Fr ≤ D.cF) (B : SmallBudget)
    (N0 : ℕ) (hcat : KCatValid c hc Fr depth D.shifts D.Q D.Pbad N0 D.kcat)
    (hpre : PreValid c hc Fr depth D.M B D.t0 D.α0b) :
    HasScaledContent (AltEven c hc Fr depth) (altGeom c hc).scale (D.Λ : ℝ) := by
  classical
  obtain ⟨hq2, hqP, hM0, hMq, ha0, haq, hα, hα0b, hα0, -⟩ := kcheck_params hD
  haveI : NeZero D.M := ⟨by omega⟩
  have hmem := kcheck_class hD
  simp only [kclassOK, Bool.and_eq_true, decide_eq_true_eq] at hmem
  obtain ⟨hcls, hsum⟩ := hmem
  -- the template of a unit class
  have hclass : ∀ c' : ZMod D.M, IsUnit c' →
      ∃ j T, jOf D.Q D.a c'.val = some j ∧ findK j D.tmpls = some T := by
    intro c' hc'
    have hcop : D.M.Coprime c'.val := by
      have : IsUnit ((c'.val : ℕ) : ZMod D.M) := by rwa [ZMod.natCast_zmod_val]
      exact ((ZMod.isUnit_iff_coprime c'.val D.M).1 this).symm
    have := unitAll_spec D.M _ D.M hcls c'.val (ZMod.val_lt c') hcop
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
  -- the scale `R0`: every prime of every piece exceeds `N0`, and `R0 ≥ R_t`
  obtain ⟨tlo, htlo0, htlo⟩ := ktlo_exists hD
  have htl : (0 : ℝ) < tlo := by exact_mod_cast htlo0
  obtain ⟨R0, hR0, hRt⟩ : ∃ R0 : ℕ, (N0 : ℝ) < tlo * R0 ∧ (D.Rt : ℝ) ≤ R0 := by
    obtain ⟨R1, hR⟩ := exists_nat_gt ((N0 : ℝ) / tlo)
    refine ⟨max R1 ⌈(D.Rt : ℝ)⌉₊, ?_, ?_⟩
    · have h1 : (N0 : ℝ) < tlo * R1 := by rwa [div_lt_iff₀ htl, mul_comm] at hR
      have h2 : (R1 : ℝ) ≤ (max R1 ⌈(D.Rt : ℝ)⌉₊ : ℕ) := by exact_mod_cast le_max_left _ _
      have := mul_le_mul_of_nonneg_left h2 htl.le
      linarith
    · have h2 : (⌈(D.Rt : ℝ)⌉₊ : ℝ) ≤ (max R1 ⌈(D.Rt : ℝ)⌉₊ : ℕ) := by exact_mod_cast le_max_right _ _
      exact (Nat.le_ceil _).trans h2
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
  refine hasScaledContent_lift (AltEven c hc Fr depth) (altGeom c hc).scale (D.Λ : ℝ) R0
    (fun i => NodeFamily.family_degree Fr (altGeom c hc).geometry depth i) ?_
  refine altContent_of_bounds c hc hc1 Fr depth R0 D.M D.Λ B (fun _ => ktmplOf D) D.τ ?_ ?_ ?_ ?_ ?_
  · -- hmass (D6)
    intro ε hε
    have hcc : contentConstant D.M (ktmplOf D) = D.Λ := by
      unfold contentConstant
      have h1 : ∀ c' ∈ unitClasses D.M, (ktmplOf D c').mass = ((kclassMass D c'.val : ℚ) : ℝ) := by
        intro c' hc'
        obtain ⟨j, T, hj, hT⟩ := hclass c' (mem_unitClasses.1 hc')
        rw [htmpl c' j T hj hT, kmass hD hT]
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
    rw [htmpl c' j T hj hT, ktend hD hT]
    exact_mod_cast (ktmpl_facts hD hT).2.2.2.2.2.1
  · -- tail: the tail branch of the class
    intro ε hε i hi c' hc' p hp hpc hlt _
    have hr2 : i.1 % 2 = 0 := hi.1.2
    rcases Nat.eq_zero_or_pos i.1 with h0 | hr0
    · have := altGeom_gle_Ecrude c hc hc1 Fr depth i hr2 p
      have h00 : Ecrude (cFr Fr) i.1 p = 0 := by simp [Ecrude, h0]
      rw [h00] at this
      exact this
    obtain ⟨j, T, hj, hT⟩ := hclass c' hc'
    obtain ⟨hjq, hj0, hk⟩ := hdatum c' j p hj hpc
    set k := (j * p) / D.Q + 1 with hkdef
    rw [htmpl c' j T hj hT, ktend hD hT] at hlt
    obtain ⟨ht1, -, hch, hjs, htail, -, hpcs⟩ := ktmpl_facts hD hT
    set te := tendQ T.t1 T.pieces with hte
    unfold tailOK at htail
    rcases hbr : nth (D.cat j) T.tb with _ | br <;> simp only [hbr, reduceCtorEq, Bool.false_eq_true] at htail
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at htail
    obtain ⟨⟨⟨⟨⟨hz, hd0⟩, hcs⟩, hte0⟩, hRq⟩, hRP⟩ := htail
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
        have := (Rat.cast_le (K := ℝ)).2 hRP; linarith
      push_cast at h1
      rw [div_le_iff₀ hteR] at h1
      have : (D.Pbad : ℝ) < p := by nlinarith
      exact_mod_cast this
    have hrd := round_of (D := D.toBank) c hc hcα hr2 hq2 ha0 haq hk (r := i.1)
    set m := (altGeom c hc).borderSize i.1 with hm
    have hqN : D.Q * (i.1 + 2 * m) < p * p := by
      have h1 : (((D.Q : ℚ) * (2 + 2 * D.α) / (te * te) : ℚ) : ℝ) ≤ i.1 := by
        have := (Rat.cast_le (K := ℝ)).2 hRq; linarith
      push_cast at h1
      rw [div_le_iff₀ (mul_pos hteR hteR)] at h1
      have hq0 : (0 : ℝ) < D.Q := by exact_mod_cast (show 0 < D.Q by omega)
      have hr1 : (1 : ℝ) ≤ i.1 := by exact_mod_cast hr0
      have hα' : (0 : ℝ) ≤ D.α := by exact_mod_cast hα
      have hm2 : (m : ℝ) < D.α * i.1 + 1 / 2 := by
        have h := hrd.m_hi
        change (m : ℝ) - ((D.α : ℚ) : ℝ) * (i.1 : ℝ) < 1 / 2 at h
        linarith
      have e1 : (D.Q : ℝ) * (i.1 + 2 * m) < D.Q * ((1 + 2 * D.α) * i.1 + 1) :=
        mul_lt_mul_of_pos_left (by linarith) hq0
      have e2 : (D.Q : ℝ) * ((1 + 2 * D.α) * i.1 + 1) ≤ D.Q * (2 + 2 * D.α) * i.1 := by
        have := mul_le_mul_of_nonneg_left hr1 hq0.le
        linarith
      have e3 : (D.Q : ℝ) * (2 + 2 * D.α) * i.1 ≤ (te * i.1) * (te * i.1) := by
        have := mul_le_mul_of_nonneg_right h1 hrR.le
        linarith
      have hsr : (0 : ℝ) ≤ te * i.1 := mul_nonneg hteR.le hrR.le
      have e4 : ((te : ℝ) * i.1) * (te * i.1) < p * p := mul_self_lt_mul_self hsr hlt'
      have : ((D.Q * (i.1 + 2 * m) : ℕ) : ℝ) < ((p * p : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    have hN0p : N0 < p := by
      have hge := (kchain_ge T.pieces T.t1 hch hpcs).2
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
    obtain ⟨n, hn, hnb⟩ := branches_of_kcat hD hcat hjs i hi.1 hr0 p k hk hN0p br hbm hPb hqN hcond
    rw [evalN_of_isZero hz, hd0, Nat.zero_mul, Nat.add_zero] at hnb
    have : n = 0 := by omega
    rw [this] at hn
    exact hn
  · -- pre (D3)
    intro ε hε i hi c' hc' p h1 hp hpc _
    obtain ⟨j, T, hj, hT⟩ := hclass c' hc'
    obtain ⟨ht1, ht0, -⟩ := ktmpl_facts hD hT
    rw [htmpl c' j T hj hT, mkTemplate_eq_of (T := T.toQ) hα0 ht1 (ktmpl_chain hD hT)] at h1 ⊢
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
    obtain ⟨ht1, -, hch, hjs, -, -, hpcs⟩ := ktmpl_facts hD hT
    rw [htmpl c' j T hj hT, mkTemplate_eq_of (T := T.toQ) hα0 ht1 (ktmpl_chain hD hT)] at hP
    simp only [QTmpl.real, KTmpl.toQ, List.mem_map] at hP
    obtain ⟨x, hx, rfl⟩ := hP
    have hok := hpcs x hx
    obtain ⟨hjq, hj0, hk⟩ := hdatum c' j p hj hpc
    have hr2 : i.1 % 2 = 0 := hi.1.2
    have hs0 : (0 : ℝ) ≤ (x.1.s : ℝ) * i.1 := by
      have : (0 : ℝ) < x.1.s := by exact_mod_cast (pieceOK_lt hok).1
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
    have hrd := round_of (D := D.toBank) c hc hcα hr2 hq2 ha0 haq hk (r := i.1)
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
    have hN : N0 < p := by
      have hge := (kchain_ge T.pieces T.t1 hch hpcs).1 x hx
      exact hN0 i.1 p x.1.s hi.2 (le_trans (htlo j T hT) hge) hs
    obtain ⟨n, hn, hb⟩ := piece_sound x.1 x.2 hok (by omega) hα
      (fun n => GLE p n ((AltEven c hc Fr depth).Q i)) hrd hodd (Fact.out : p.Prime).two_le hdel hcr
      (branches_of_kcat hD hcat hjs i hi.1 hr0 p _ hk hN) hs ht
    exact ⟨n, hn, hb⟩

end CatalanCore.Uniform.Content.BankShared.KTerm
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.branches_of_kcat
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.hasScaledContent_of_kcheck
