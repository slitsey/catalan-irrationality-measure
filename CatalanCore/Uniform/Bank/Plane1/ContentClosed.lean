module

public import CatalanCore.Uniform.Bank.Plane1.Bound
public import CatalanCore.Uniform.Content.BankShared.KTerm.PeriodContent
public import CatalanCore.Uniform.Content.BankShared.KTerm.PeriodTranslation

@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 1600000

/-! ### The prefix layer as an instance of Theorem PC (wave P1F; ledger P115, P116)

The closed bank of a plane (`KBankDataC`) is the instance of `hasScaledContent_of_periodic` with `b = den α`,
`a = num α`, `K_c = 2 b + 2 a` (the prefix constant `2 + 2 α` times `b`):

* **(T1), the index move**: the translation of the prefix branch `PRE(ν, j₀, j₁, j₂)` along the lattice shift of order
  `t` is `PRE(ν + a t, j₀, j₁, j₂)` and `D1x` is fixed; the price is covariant, `τ(σ_t x) = τ(x) + t K_c p`
  (`pre_cov`, `d1x_cov`; no side condition, truncated subtractions included).  The conditions are empty (T2 is
  `KBundle.prefix_valid` and the valid branch `D1x`, for every index).
* **The base cell** of a period cell `c` (in `u = s - b n'`) is the strip `n' = 1` piece `expPiece α b 3 1 c` with
  threshold `R = 0`; its soundness (`baseSound_cell`) is Lemma T (`pre_bound`, `d1x_bound`) at the strip `n' = 1` with
  the branch `PRE(a + ν, j₀, j₁, j₂)` of the base catalogue `kbOf`.  The translate of order `t` is the cell in the
  strip `t + 1` (`trPiece_exp`), so the expansion of a closed template (strips `N, …, 1`) is `expPer` of the base cells
  with no partial strip (`tmplP_toK`). -/

namespace CatalanCore.Uniform.Content.BankShared.KTerm
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.BankShared
  CatalanCore.Uniform.Content.SmallPrimes CatalanCore.Uniform.Content.Member CatalanCore.Arith.Hybrid
  CatalanCore.Basic Filter Finset Polynomial CatalanCore.Uniform.Content.BankShared.Check

/-! #### Base cells -/

/-- The base branch of a period cell: `D1x`, or `PRE(a + ν, j₀, j₁, j₂)` (the strip `n' = 1`). -/
def cellBr (a : ℕ) (c : PCell) : KBranch :=
  match c.br with
  | .d1x => kbD1xB
  | .pre j0 j1 j2 => kbrPre (a * 1 + c.nu) j0 [j1, j2]

theorem cellBr_kind (a : ℕ) (c : PCell) : cellBr a c = kbD1xB ∨ IsPre (cellBr a c) := by
  unfold cellBr
  rcases hb : c.br with _ | ⟨j0, j1, j2⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨(a * 1 + c.nu, j0, j1, j2), rfl⟩

/-- The base catalogue of a closed bank: the base branches of all its cells. -/
def kbOf (E : KBankDataC) : List KBranch :=
  E.tmpls.flatMap (fun x => x.2.cells.map (cellBr E.α.num.toNat))

theorem kbOf_kind (E : KBankDataC) : ∀ br ∈ kbOf E, br = kbD1xB ∨ IsPre br := by
  intro br hbr
  simp only [kbOf, List.mem_flatMap, List.mem_map] at hbr
  obtain ⟨x, -, c, -, rfl⟩ := hbr
  exact cellBr_kind _ c

/-- The base piece of a period cell: the cell in the strip `n' = 1`. -/
def basePieceOf (α : ℚ) (c : PCell) : QPiece × Cert := (expPiece α α.den expC 1 c, ⟨0, [], [], 0⟩)

/-- The periodic template of a closed template. -/
def tmplP (α : ℚ) (T : KTmplC) : KTmplP := ⟨T.t1, T.N, 0, T.cells.map (basePieceOf α), T.head, T.tb⟩

/-- **The translate of the base cell of order `t` is the cell in the strip `t + 1`.** -/
theorem trPiece_exp {α : ℚ} {a b : ℕ} (hab : α * b = a) (hb : 1 ≤ b) {κ0 κ1 : ℚ} {c : PCell}
    (hc : c.ok α κ0 κ1 = true) (cF t : ℕ) :
    trPiece b (2 * b + 2 * a) cF 0 t (expPiece α b expC 1 c) = expPiece α b expC (t + 1) c := by
  obtain ⟨hlt, hk, -, -, -, -⟩ := c.ok_spec hc
  have hkc : (0 : ℚ) ≤ c.kc := Nat.cast_nonneg _
  have hb' : (1 : ℚ) ≤ b := by exact_mod_cast hb
  have ht0 : (0 : ℚ) ≤ t := Nat.cast_nonneg _
  have hcr : crudeBd cF ⌈(0 : ℚ) * (1 + (t : ℚ) * b * (1 / ((b : ℚ) * (1 : ℕ) + c.u0)))⌉₊ = 0 := by
    simp [crudeBd]
  simp only [trPiece, expPiece, hcr, Nat.cast_zero, add_zero]
  push_cast
  simp only [mul_one]
  have hu0'' : (0 : ℚ) < (b : ℚ) + c.u0 := by nlinarith
  have hu1'' : (0 : ℚ) < (b : ℚ) + c.u1 := by nlinarith
  have hu0''' : (0 : ℚ) < (b : ℚ) * ((t : ℚ) + 1) + c.u0 := by nlinarith
  have hu1''' : (0 : ℚ) < (b : ℚ) * ((t : ℚ) + 1) + c.u1 := by nlinarith
  have ha : (2 * b + 2 * a : ℚ) = (2 + 2 * α) * b := by rw [← hab]; ring
  have key : ∀ u : ℚ, 0 < (b : ℚ) + u → 0 < (b : ℚ) * ((t : ℚ) + 1) + u →
      (1 / ((b : ℚ) + u)) / (1 + (t : ℚ) * b * (1 / ((b : ℚ) + u))) =
        1 / ((b : ℚ) * ((t : ℚ) + 1) + u) := by
    intro u h1 h2
    have h3 : (1 : ℚ) + (t : ℚ) * b * (1 / ((b : ℚ) + u)) =
        ((b : ℚ) * ((t : ℚ) + 1) + u) / ((b : ℚ) + u) := by
      field_simp
      ring
    rw [h3]
    field_simp
  refine (QPiece.mk.injEq ..).mpr ⟨key c.u1 hu1'' hu1''', key c.u0 hu0'' hu0''', rfl, ?_, rfl⟩
  rw [ha]; ring

/-- **Soundness of a prefix cell** at the strip `n' ≥ 1` against a base catalogue containing its branch: Lemma T
(`pre_bound`, `d1x_bound`) at a master root. -/
theorem baseSound_cell {D : KBankData} (hlen : 2 ≤ D.shifts.length) {kb : List KBranch} {j n' : ℕ}
    (hn : 1 ≤ n') {c₀ : PCell} (hcell : c₀.ok D.α (kappaOf D j 0) (kappaOf D j 1) = true)
    (hd : c₀.br = .d1x → kbD1xB ∈ kb)
    (hp : ∀ j0 j1 j2, c₀.br = .pre j0 j1 j2 → kbrPre (D.α.num.toNat * n' + c₀.nu) j0 [j1, j2] ∈ kb) :
    BaseSound D (kb.map (KBranch.compile D.tS (D.bS j) D.cS)) j (expPiece D.α D.α.den expC n' c₀) 0 := by
  intro hpar hjs r p m k del Good hk hqN hrd hPb hodd hp2 hdel hr0 _ hs ht hBV
  have hpar' := hpar
  obtain ⟨hq2, hqP, -, -, -, -, hα, -, -, -⟩ := hpar'
  obtain ⟨hle, hr⟩ := kv_roots hpar hjs hk hPb
  obtain ⟨kv, hkv⟩ : ∃ kv : ℕ → ℕ, kv = fun n => D.tS n * k - (D.bS j n * p + D.cS n) := ⟨_, rfl⟩
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
  have hpQ : (0 : ℚ) < p := by exact_mod_cast (show 0 < p by omega)
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
    { hα := hα, hab := hab, hb := hb1, hn := hn, hok := hcell, hp := by omega,
      hm1 := hm1, hm2 := hm2, hk0 := (hkap 0 (by norm_num)).1, hk0' := (hkap 0 (by norm_num)).2,
      hk1 := (hkap 1 (by norm_num)).1, hk1' := (hkap 1 (by norm_num)).2, hr0 := hr0', hr1 := hr1 }
  rcases hbr : c₀.br with _ | ⟨j0, j1, j2⟩
  · -- `D1x`
    have hmem : kbD1xB.compile D.tS (D.bS j) D.cS ∈ kb.map (KBranch.compile D.tS (D.bS j) D.cS) :=
      List.mem_map.2 ⟨kbD1xB, hd hbr, rfl⟩
    obtain ⟨nn, hnn, hb⟩ := hBV _ hmem hPb hqN (by intro cd hcd; simp [KBranch.compile, kbD1xB] at hcd)
    refine ⟨nn, hnn, ?_⟩
    have e1 : (kbD1xB.compile D.tS (D.bS j) D.cS).τ.evalN r p m k = kD1xE.evalN r p m kv := by
      rw [KBranch.evalN_compile, hkv]; rfl
    have h1 : nn ≤ kD1xE.evalN r p m kv := by
      have h0 : (kbD1xB.compile D.tS (D.bS j) D.cS).debit = 0 := rfl
      rw [h0, Nat.zero_mul, Nat.add_zero, e1] at hb
      exact hb
    have h1' : (nn : ℝ) ≤ ((kD1xE.evalN r p m kv : ℕ) : ℝ) := by exact_mod_cast h1
    have h2 := (Rat.cast_le (K := ℝ)).2 (d1x_bound hctx hbr)
    push_cast at h2
    simp only [expPiece, expC]
    push_cast
    linarith
  · -- the prefix branch of the cell
    have hmem : (kbrPre (D.α.num.toNat * n' + c₀.nu) j0 [j1, j2]).compile D.tS (D.bS j) D.cS ∈
        kb.map (KBranch.compile D.tS (D.bS j) D.cS) :=
      List.mem_map.2 ⟨_, hp j0 j1 j2 hbr, rfl⟩
    obtain ⟨nn, hnn, hb⟩ := hBV _ hmem hPb hqN (by intro cd hcd; simp [KBranch.compile, kbrPre] at hcd)
    refine ⟨nn, hnn, ?_⟩
    have e1 : ((kbrPre (D.α.num.toNat * n' + c₀.nu) j0 [j1, j2]).compile D.tS (D.bS j) D.cS).τ.evalN r p m k =
        (kbrPre (D.α.num.toNat * n' + c₀.nu) j0 [j1, j2]).τ.evalN r p m kv := by
      rw [KBranch.evalN_compile, hkv]
    have h1 : nn ≤ (kbrPre (D.α.num.toNat * n' + c₀.nu) j0 [j1, j2]).τ.evalN r p m kv := by
      have h0 : ((kbrPre (D.α.num.toNat * n' + c₀.nu) j0 [j1, j2]).compile D.tS (D.bS j) D.cS).debit = 0 := rfl
      rw [h0, Nat.zero_mul, Nat.add_zero, e1] at hb
      exact hb
    have h1' : (nn : ℝ) ≤
        (((kbrPre (D.α.num.toNat * n' + c₀.nu) j0 [j1, j2]).τ.evalN r p m kv : ℕ) : ℝ) := by exact_mod_cast h1
    have h2 := (Rat.cast_le (K := ℝ)).2 (pre_bound hctx hbr)
    push_cast at h2
    simp only [expPiece, expC]
    push_cast
    linarith

/-! #### The expansion of a closed template -/

/-- The expansion of the periodic template of a closed template is the expansion of the closed template. -/
theorem tmplP_toK {α : ℚ} {a b : ℕ} (hab : α * b = a) (hb : b = α.den) (cF : ℕ) {κ0 κ1 : ℚ} (T : KTmplC)
    (hc : ∀ c ∈ T.cells, c.ok α κ0 κ1 = true) :
    (tmplP α T).toK b (2 * b + 2 * a) cF = T.toK α := by
  subst hb
  have hb1 : 1 ≤ α.den := α.den_pos
  unfold KTmplP.toK KTmplC.toK
  congr 1
  congr 1
  simp only [tmplP, expPer, expList, List.drop_length, Nat.sub_zero, List.map_nil, List.nil_append]
  rw [List.map_flatMap]
  refine List.flatMap_congr (fun i _ => ?_)
  rw [List.map_map, List.map_map]
  refine List.map_congr_left (fun c hcmem => ?_)
  simp only [Function.comp, basePieceOf]
  rw [trPiece_exp hab hb1 (hc c hcmem) cF i]

theorem exists_nat_bound : ∀ (L : List ℚ), ∃ Ω : ℕ, ∀ q ∈ L, q ≤ Ω
  | [] => ⟨0, fun q hq => absurd hq (by simp)⟩
  | q :: L => by
    obtain ⟨Ω, hΩ⟩ := exists_nat_bound L
    obtain ⟨n, hn⟩ := exists_nat_ge q
    refine ⟨max Ω n, fun x hx => ?_⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hn.trans (by exact_mod_cast le_max_right _ _)
    · exact (hΩ x hx).trans (by exact_mod_cast le_max_left _ _)

/-- **Theorem C3** (family form): a closed `k`-shift bank that passes `kcheckC`, with the valid catalogue, the
valid prefix branches of every strip and the valid branch `D1x`, has the scaled content `Λ`.  It is the instance of
Theorem PC (`hasScaledContent_of_periodic`) with `b = den α`, `a = num α`, `K_c = 2 b + 2 a`, the translation
`preTransl` and the base cells `tmplP`. -/
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
  have hnum : (0 : ℤ) ≤ E.α.num := Rat.num_nonneg.2 hα0
  have hnat : ((E.α.num.toNat : ℕ) : ℚ) = (E.α.num : ℚ) := by
    have : ((E.α.num.toNat : ℕ) : ℤ) = E.α.num := Int.toNat_of_nonneg hnum
    exact_mod_cast this
  have hab : E.α * (E.α.den : ℚ) = (E.α.num.toNat : ℚ) := by
    rw [hnat]; exact Rat.mul_den_eq_num E.α
  -- the ambient range (not used by the conditions: they are empty)
  obtain ⟨Ω, hΩ⟩ := exists_nat_bound (E.tmpls.flatMap (fun x => x.2.cells.map
    (fun y => y.u1 + (E.α.den : ℚ) + (x.2.N : ℚ) * E.α.den)))
  have hkb := kbOf_kind E
  let tr := preTransl E.α.den E.α.num.toNat Ω (kbOf E) hkb
  let Tm : List (ℕ × KTmplP) := E.tmpls.map (fun x => (x.1, tmplP E.α x.2))
  have hTm : E.toK.tmpls =
      Tm.map (fun x => (x.1, x.2.toK E.α.den (2 * E.α.den + 2 * E.α.num.toNat) E.toK.cF)) := by
    show E.tmpls.map (fun x => (x.1, x.2.toK E.α)) = _
    simp only [Tm, List.map_map]
    refine List.map_congr_left (fun x hx => ?_)
    simp only [Function.comp]
    exact Prod.ext rfl (tmplP_toK hab rfl E.cF x.2 (hcells x hx)).symm
  refine hasScaledContent_of_periodic E.toK hpar hcls hheads c hc hcα const depth Q hdepth hQ B N0 hab tr Tm hTm
    ?_ ?_ ?_ hcat ?_ hPre
  · -- (K0), the threshold and the ambient range of the base cells
    intro x hx y hy
    obtain ⟨x0, hx0, rfl⟩ := List.mem_map.1 hx
    obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 hy
    refine ⟨expPiece_basic hα0 hb1 le_rfl (hcells x0 hx0 c0 hc0) (by norm_num [expC]), le_rfl, ?_⟩
    have hmem := hΩ (c0.u1 + (E.α.den : ℚ) + (x0.2.N : ℚ) * E.α.den)
      (List.mem_flatMap.2 ⟨x0, hx0, List.mem_map.2 ⟨c0, hc0, rfl⟩⟩)
    have hN : (tmplP E.α x0.2).N = x0.2.N := rfl
    simp only [basePieceOf, expPiece, one_div_one_div, hN]
    push_cast
    linarith
  · -- the base cells are sound
    intro x hx y hy
    obtain ⟨x0, hx0, rfl⟩ := List.mem_map.1 hx
    obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 hy
    refine baseSound_cell (D := E.toK) hlen (j := x0.1) (n' := 1) le_rfl (hcells x0 hx0 c0 hc0) ?_ ?_
    · intro hbr
      refine List.mem_flatMap.2 ⟨x0, hx0, List.mem_map.2 ⟨c0, hc0, ?_⟩⟩
      simp only [cellBr, hbr]
    · intro j0 j1 j2 hbr
      refine List.mem_flatMap.2 ⟨x0, hx0, List.mem_map.2 ⟨c0, hc0, ?_⟩⟩
      simp only [cellBr, hbr]
      rfl
  · -- the heads
    intro x hx y hy
    obtain ⟨x0, hx0, rfl⟩ := List.mem_map.1 hx
    have hall := hpieces x0 hx0
    simp only [kpieceAll, List.all_eq_true] at hall
    exact hall y hy
  · -- (T2): the translates of the base catalogue are valid
    intro n b' hb'
    obtain ⟨br, hbr, rfl⟩ := List.mem_map.1 hb'
    rcases hkb br hbr with rfl | h
    · have : tr.ρ n kbD1xB = kbD1xB := preRho_d1x _ _
      rw [this]
      exact hd1x _ (List.mem_singleton_self _)
    · obtain ⟨x, hx, hρ⟩ := preRho_pre (a := E.α.num.toNat) (t := n) h
      have : tr.ρ n br = kbrPre (x.1 + E.α.num.toNat * n) x.2.1 [x.2.2.1, x.2.2.2] := hρ
      rw [this]
      exact hpre _ _ _ _ _ (List.mem_singleton_self _)

end CatalanCore.Uniform.Content.BankShared.KTerm

/-! # The content of the plane frames from the closed form (wave H5a-closed; ledger P109, P115)

`plane_content_closed` is `plane_content` for a bank `kd : KBankDataC` whose periodic layer is the expansion of a
period table (`kcheckC`, Theorem C3 of `THREE-TERM-CONTENT-2026-11-07.md`): the same hypotheses on the shifts, the
catalogue and the small primes (with `α₀ᵇ ≥ 13/6`), the same conclusion `HasScaledContent … Λ` for every plane
frame at once.  `PlaneBankOKC` and `planeContent_of_banksC` are `PlaneBankOK` and `planeContent_of_banks`: two
closed banks (one per support, the same `Λ`) give `PlaneContent Λ`. -/

namespace CatalanCore.Uniform.Bank.Plane1
open Finset CatalanCore CatalanCore.Basic CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanCore.Uniform
  CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.BankShared
  CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check
  CatalanCore.Uniform.Content.BankShared.TwoTerm CatalanCore.Uniform.Content.SmallPrimes
  CatalanFrames.HybCommon CatalanFrames.HybGen CatalanCore.Rect

/-- **The scaled content of the plane family from a closed bank** (P109 with P115 in closed form). -/
theorem plane_content_closed (σ : Support) (a b c : ℤ) (h0 : a + b + c = 0) (kd : KBankDataC)
    (hkd : kcheckC kd = true)
    (hshifts : kd.shifts = (planeBundle σ a b c h0).shifts) (hα : planeC = 2 * kd.α)
    (hcat : ∀ br ∈ kd.kcat, PlaneBranch br) (hQ : 3 ≤ kd.Q) (hP : 6 ≤ kd.Pbad) (hM : 6 ∣ kd.M)
    (ht0 : kd.t0 ≤ 1 / 68) (hα0 : 13 / 6 ≤ kd.α0b) (hcF : 23 ≤ kd.cF) (depth : ℕ)
    (hdepth : depth ≤ kd.depth) :
    HasScaledContent (AltEven planeC planeC_pos (planeFrame σ a b c h0) depth)
      (altGeom planeC planeC_pos).scale (kd.Λ : ℝ) := by
  refine hasScaledContent_of_kcheckC kd hkd planeC planeC_pos hα (planeFrame σ a b c h0).const depth _ hdepth
    (AltQ.ofFrame planeC planeC_pos planeC_le_one (planeFrame σ a b c h0) ((cFr_plane σ a b c h0).trans hcF))
    (SmallBudget.add (SmallBudget.sqrtLog 5 10) SmallBudget.unit) 0 ?_ ?_ ?_ ?_
  · rw [hshifts]
    exact plane_cat_valid σ a b c h0 planeC planeC_pos planeC_le_one depth kd.Q kd.Pbad 0 hQ hP kd.kcat hcat
  · intro n j0 j1 j2
    rw [hshifts]
    exact (planeBundle σ a b c h0).prefix_valid planeC planeC_pos depth kd.Q kd.Pbad 0 n j0 j1 j2 hQ hP
  · rw [hshifts]
    exact plane_cat_valid σ a b c h0 planeC planeC_pos planeC_le_one depth kd.Q kd.Pbad 0 hQ hP [kbD1x]
      (fun br hbr => by
        rw [List.mem_singleton] at hbr
        subst hbr
        exact Or.inl (by simp [planeTrop]))
  · exact PreValid_mono hM ht0 hα0 (plane_preValid σ a b c h0 depth)

/-- The data of a closed bank for the support `σ` (see `plane_content_closed`). -/
structure PlaneBankOKC (σ : Support) (kd : KBankDataC) : Prop where
  check : kcheckC kd = true
  shifts : kd.shifts = [⟨3, σ.rho, 1⟩, ⟨2, 1, 1⟩]
  alpha : planeC = 2 * kd.α
  cat : ∀ br ∈ kd.kcat, PlaneBranch br
  hQ : 3 ≤ kd.Q
  hP : 6 ≤ kd.Pbad
  hM : 6 ∣ kd.M
  ht0 : kd.t0 ≤ 1 / 68
  hα0 : 13 / 6 ≤ kd.α0b
  hcF : 23 ≤ kd.cF
  hdepth : planeDepth ≤ kd.depth

/-- Content of the plane from a closed bank on each support, both with the same `Λ`. -/
theorem planeContent_of_banksC {kP kM : KBankDataC} (hP : PlaneBankOKC .plus kP)
    (hM : PlaneBankOKC .minus kM) (hΛ : kP.Λ = kM.Λ) : PlaneContent (kP.Λ : ℝ) := by
  intro σ a b c h0
  cases σ
  · exact plane_content_closed .plus a b c h0 kP hP.check hP.shifts hP.alpha hP.cat hP.hQ hP.hP hP.hM hP.ht0
      hP.hα0 hP.hcF planeDepth hP.hdepth
  · have := plane_content_closed .minus a b c h0 kM hM.check hM.shifts hM.alpha hM.cat hM.hQ hM.hP hM.hM hM.ht0
      hM.hα0 hM.hcF planeDepth hM.hdepth
    rwa [← hΛ] at this

end CatalanCore.Uniform.Bank.Plane1

#print axioms CatalanCore.Uniform.Bank.Plane1.plane_content_closed
#print axioms CatalanCore.Uniform.Bank.Plane1.planeContent_of_banksC

#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.pre_cov
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.d1x_cov
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.trPiece_exp
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.baseSound_cell
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.tmplP_toK
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.hasScaledContent_of_kcheckC
