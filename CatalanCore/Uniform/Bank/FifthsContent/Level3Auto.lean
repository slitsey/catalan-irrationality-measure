module
public import CatalanCore.Uniform.Bank.FifthsContent.Level3Data
public import CatalanCore.Uniform.Content.BankShared.TwoTerm.Trop
public import CatalanFrames.Fifths.ContentHyb
public import CatalanCore.Uniform.Bank.Fifths.Geom
public import CatalanCore.Uniform.Bank.Fifths.Frame
public import CatalanCore.Arith.Hybrid.PieceTools
public import CatalanFrames.Fifths.Instance
public import CatalanCore.Uniform.Content.BankShared.KTerm.CatalogueOrbit.Sound
public import CatalanCore.Uniform.Content.UFSimple.WrapPrefixCheck
public import CatalanCore.Uniform.Content.BankShared.Check.Prefix
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 3200000
namespace CatalanCore.Uniform.Bank.FifthsContent.Level3Auto
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.BankShared
  CatalanCore.Uniform.Content.BankShared.Check CatalanCore.Uniform.Content.BankShared.TwoTerm
  CatalanCore.Uniform.Content.SmallPrimes CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanFrames.HybCommon
  CatalanFrames.HybGen CatalanCore.Uniform.Bank.Fifths CatalanCore.Uniform.Content.RankProducer
  CatalanCore.Uniform.Content.Smith
open CatalanFrames.Fifths hiding fifths1 fifths2 fifths3 fifths4

/-! ### Instance hypotheses of the fifths frames -/

theorem fifths1_shift : ShiftData fifths1 5 4 := CatalanFrames.Fifths.fifths1_data
theorem fifths2_shift : ShiftData fifths2 5 3 := CatalanFrames.Fifths.fifths2_data
theorem fifths3_shift : ShiftData fifths3 5 2 := CatalanFrames.Fifths.fifths3_data
theorem fifths4_shift : ShiftData fifths4 5 1 := CatalanFrames.Fifths.fifths4_data


open CatalanCore.Uniform.Content.BankShared.KTerm
open CatalanCore.Uniform.Content.UFSimple

/-- The two-term data of a fifths frame (`q = 5`, `o = u`). -/
theorem shift_twoTerm {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) : TwoTermData Fr 5 u where
  o_pos := T.hu0
  o_lt := T.hu1
  delta_eq t ht := by
    rw [T.delta t (by omega), cast_linear (k := t) T.hu1 (by omega)]
  dsq_eq t ht := by
    rw [T.dsq t (by omega), cast_linear (k := t) T.hu1 (by omega)]

theorem cFr_fifths1 : cFr fifths1 ≤ 49 := by decide +kernel
theorem cFr_fifths2 : cFr fifths2 ≤ 49 := by decide +kernel
theorem cFr_fifths3 : cFr fifths3 ≤ 49 := by decide +kernel
theorem cFr_fifths4 : cFr fifths4 ≤ 49 := by decide +kernel

/-- The branch catalogue of `bankData` is valid on every fifths frame (`ShiftData Fr 5 u`, `o = u`). -/
theorem fifths_catValid {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) :
    CatValid (2 / 9) two_ninths_pos Fr depth 5 u 9 (max (NFr (1 / Fr.norm) (-1 / Fr.norm) 5 9) 50)
      bankData.cat := by
  have hu0 := T.hu0
  have hu1 := T.hu1
  rw [bankData_cat]
  apply catValid_append
  · apply catValid_append
    · exact catValid_bankUFwP (fifthsInst T) (fifths_arithmetic T).L_eq (fifths_levels T) (2 / 9) two_ninths_pos
        (by norm_num) (shift_twoTerm T) (nm := 5 * 5) (by rw [T.norm_eq]; norm_num) depth 9 9 50
        (by norm_num) (by norm_num) (by norm_num) le_rfl
        (fun p hp h => ⟨not_dvd_sq_of_lt hp (by norm_num) (by omega), by omega, by omega,
          not_bad_of_levels (fifths_levels T) hp (show 7 ≤ p by omega), (show 7 ≤ p by omega), by omega⟩)
        (fun p hp h j k hk hj0 hjq _ _ => by
          have h7 : 7 ≤ p := by omega
          have hb := (fifths_good T hp h7).2
          obtain ⟨h1, -⟩ := kq_eq_poleIndex (fifthsCD T) (fun _ => rfl) (by omega) (by omega) hp (by omega) hb
            (fifths_kq_att T p hp.isPrimePow hb)
          have hk' : 5 * k = j * p + (5 - (5 - u)) := by rw [show 5 - (5 - u) = u by omega]; exact hk
          have h2 := (rootClass_unique hp (by omega) (by omega) (by omega) hjq hk').2
          show (fifthsCD T).kq p = k
          rw [h1, h2])
        bankWins bankPres
    · exact CatalanCore.Uniform.Content.UFSimple.WrapCheck.catValid_wrap (2 / 9) two_ninths_pos (shift_twoTerm T) (nm := 5 * 5) (by rw [T.norm_eq]; norm_num) depth 9 _ (fun p hp h => ⟨not_dvd_sq_of_lt hp (by norm_num) (by omega), by omega⟩)
  · exact CatalanCore.Uniform.Content.UFSimple.catValid_prefixBranches (2 / 9) two_ninths_pos (shift_twoTerm T) (nm := 5 * 5) (by rw [T.norm_eq]; norm_num) depth 9 _ 24 (fun p hp h => ⟨not_dvd_sq_of_lt hp (by norm_num) (by omega), by omega⟩)

/-- The prefix bound of every fifths frame (`pre_gle_any`), for `p ≤ r/900`, `α0 = 20/9`. -/
theorem fifths_preValid {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49) :
    PreValid (2 / 9) two_ninths_pos Fr depth 10 (SmallBudget.add (SmallBudget.sqrtLog 7 122) SmallBudget.unit)
      (qq 1 900) (qq 20 9) := by
  intro i hi p _ _ h
  have hp : p.Prime := Fact.out
  have e1 : ((qq 1 900 : ℚ) : ℝ) = ((1 : ℕ) : ℝ) / ((900 : ℕ) : ℝ) := by norm_num [qq]
  rw [e1, floor_frac 1 900 i.1] at h
  have h900 : 900 * p ≤ i.1 := by omega
  have hp2 := hp.two_le
  have hr2 : i.1 % 2 = 0 := hi.2
  obtain ⟨hb1, hb2⟩ := altGeom_border_nat (2 / 9) two_ninths_pos 2 9 (by norm_num) (by norm_num) hr2
  have hR : (9 : ℝ) * (2 * ((altGeom (2 / 9) two_ninths_pos).borderSize i.1 : ℝ)) < 2 * i.1 + 9 := by
    exact_mod_cast hb2
  have hbad : p ∈ (fifthsInst T).cd.bad → p * p ≤ 7 * i.1 := by
    intro hpb
    have hp5 : p ≤ 5 := by
      simp [fifthsInst, HybInst.ofSing, fifthsCD, badPrimes] at hpb
      omega
    have : p * p ≤ 5 * 5 := Nat.mul_le_mul hp5 hp5
    omega
  obtain ⟨n, hn, hle⟩ := pre_gle_any (fifthsInst T) (fifths_arithmetic T).L_eq (2 / 9) two_ninths_pos
    (by norm_num) depth i hr2 (by omega) p 7 122 3 49 (20 / 9) (by norm_num) hcF (by norm_num) hbad
    (by omega) (by norm_num; omega) (by omega) (by omega) (by linarith) (by omega)
  refine ⟨n, hn, ?_⟩
  have e2 : ((qq 20 9 : ℚ) : ℝ) = 20 / 9 := by norm_num [qq]
  rw [e2]
  exact hle

/-! ### The content of the four fifths frames -/


/-- Compiler fields agree at all indices, including shAt's zero-multiplier default. -/
theorem pcCompiler (o j : ℕ) :
    (pcBank o).tS=(pcHead 1).tS ∧ (pcBank o).bS j=(pcHead 1).bS j ∧
      (pcBank o).cS=(pcHead 1).cS := by
  have h0 : bankHead.q-(bankHead.q-o)-o=0 := by omega
  have h1 : bankHead.q-(bankHead.q-1)-1=0 := by omega
  constructor
  · funext i
    cases i with
    | zero => rfl
    | succ i => cases i <;> rfl
  constructor
  · funext i
    cases i with
    | zero => rfl
    | succ i => cases i <;> rfl
  · funext i
    cases i with
    | zero => simp [KBankData.cS,KBankData.oM,pcBank,pcHead,legacyShifts,shAt,Shift.c,h0,h1]
    | succ i => cases i <;> simp [KBankData.cS,KBankData.oM,pcBank,pcHead,legacyShifts,shAt,Shift.c,h0,h1]

theorem pcSeedTransport (o : ℕ) (kb : List KBranch) (j L : ℕ) (S : OrbitSeed) :
    seedOK (pcBank o) kb j L S=seedOK (pcHead 1) kb j L S := by
  obtain ⟨ht,hb,hc⟩ := pcCompiler o j
  unfold seedOK cellOKb
  rw [ht,hb,hc]
  rfl
theorem pcCellTransport (o : ℕ) (kb : List KBranch) (j N b Ω : ℕ) (y : QPiece×Cert) :
    cellOKb (pcBank o) kb j N b Ω y=cellOKb (pcHead 1) kb j N b Ω y := by
  obtain ⟨ht,hb,hc⟩ := pcCompiler o j
  unfold cellOKb
  rw [ht,hb,hc]
  rfl
theorem pc_content_o {Fr : Frame} (o depth Nold : ℕ) (B : SmallBudget)
    (hd : depth≤64) (hcF : cFr Fr≤bankHead.cF)
    (hOld : CatValid (2/9) two_ninths_pos Fr depth 5 o bankHead.Pbad Nold bankData.cat)
    (hPre : PreValid (2/9) two_ninths_pos Fr depth bankHead.M B bankHead.t0 bankHead.α0b)
    (hAllPre : ∀ ν j0 j1,CatValid (2/9) two_ninths_pos Fr depth 5 o bankHead.Pbad Nold [brPre ν j0 j1])
    (hAllWrap : ∀ ν,1≤ν → CatValid (2/9) two_ninths_pos Fr depth 5 o bankHead.Pbad Nold [WrapPrefixCheck.brPrefix ν])
    (hParams : kcheckParams (pcBank o)=true) (hClasses : kclassOK (pcBank o)=true)
    (hHeads : ∀ x∈(pcBank o).tmpls,ktmplHead (pcBank o) x.1 x.2=true) :
    HasScaledContent (AltEven (2/9) two_ninths_pos Fr depth) (altGeom (2/9) two_ninths_pos).scale (bankData.Λ:ℝ) := by
  let D := pcBank o
  let N := max Nold pcSeedLimit
  have hNold : Nold≤N := le_max_left _ _
  have hL : pcSeedLimit≤N := le_max_right _ _
  have hpar : KParams D := kparams_of hParams
  have hd' : depth≤D.depth := hd
  have hD6 : brD6∈bankHead.cat := by
    change brD6∈bankData.cat
    rw [bankData_cat]
    simp [tableT]
  have hD1x : brD1x∈bankHead.cat := by
    change brD1x∈bankData.cat
    rw [bankData_cat]
    simp [tableT]
  have hcat : KCatValid (2/9) two_ninths_pos Fr depth D.shifts D.Q D.Pbad N D.kcat :=
    (legacy_kcat_valid (2/9) two_ninths_pos Fr.const depth
      (NodeFamily.polynomial Fr (altGeom (2/9) two_ninths_pos).geometry) 5 o bankHead.Pbad Nold bankHead.cat hOld hD6).mono_threshold hNold
  have hlegacy : KCatValid (2/9) two_ninths_pos Fr depth D.shifts D.Q D.Pbad N pcLegacyCatalogue := by
    intro br hb
    exact hcat br (List.mem_append.mpr (Or.inl hb))
  have hd1x : KCatValid (2/9) two_ninths_pos Fr depth D.shifts D.Q D.Pbad N [kbD1xB] :=
    (legacy_d1x_valid (2/9) two_ninths_pos Fr.const depth
      (NodeFamily.polynomial Fr (altGeom (2/9) two_ninths_pos).geometry) 5 o bankHead.Pbad Nold bankHead.cat hOld hD1x).mono_threshold hNold
  have hpre (ν j0 j1 : ℕ) : KCatValid (2/9) two_ninths_pos Fr depth D.shifts D.Q D.Pbad N [(brPre ν j0 j1).liftK 0] := by
    have h := (hAllPre ν j0 j1).liftK (2/9) two_ninths_pos Fr.const depth
      (NodeFamily.polynomial Fr (altGeom (2/9) two_ninths_pos).geometry) 5 o bankHead.Pbad Nold [brPre ν j0 j1]
      (legacyShifts 5 o) 0 5 (by decide) rfl rfl le_rfl
    exact (show KCatValid (2/9) two_ninths_pos Fr depth D.shifts D.Q D.Pbad Nold [(brPre ν j0 j1).liftK 0] by
      simpa only [List.map_cons,List.map_nil] using h).mono_threshold hNold
  have hwrap (ν : ℕ) (hν : 1≤ν) : KCatValid (2/9) two_ninths_pos Fr depth D.shifts D.Q D.Pbad N [(WrapPrefixCheck.brPrefix ν).liftK 0] := by
    have h := (hAllWrap ν hν).liftK (2/9) two_ninths_pos Fr.const depth
      (NodeFamily.polynomial Fr (altGeom (2/9) two_ninths_pos).geometry) 5 o bankHead.Pbad Nold [WrapPrefixCheck.brPrefix ν]
      (legacyShifts 5 o) 0 5 (by decide) rfl rfl le_rfl
    exact (show KCatValid (2/9) two_ninths_pos Fr depth D.shifts D.Q D.Pbad Nold [(WrapPrefixCheck.brPrefix ν).liftK 0] by
      simpa only [List.map_cons,List.map_nil] using h).mono_threshold hNold
  have hallowed (S : CatalogueSeed pcLegacyCatalogue) :
      S.law.Allowed (KCatValidFam (2/9) two_ninths_pos Fr.const depth
        (NodeFamily.polynomial Fr (altGeom (2/9) two_ninths_pos).geometry) D.shifts D.Q D.Pbad N) 0 := by
    cases h:S.law with
    | constant indices => simpa only [h,CatalogueOrbitLaw.Allowed] using hlegacy
    | d1x => simpa only [h,CatalogueOrbitLaw.Allowed] using hd1x
    | pre ν j0 j1 => simpa only [h,CatalogueOrbitLaw.Allowed] using (fun ν' => hpre ν' j0 j1)
    | wrap ν hν => simpa only [h,CatalogueOrbitLaw.Allowed] using hwrap
  have hab (S : CatalogueSeed pcLegacyCatalogue) : D.α*S.law.shiftB 9=S.law.shiftA 1 := by
    cases S.law <;> norm_num [CatalogueOrbitLaw.shiftB,CatalogueOrbitLaw.shiftA,D,pcBank,pcHead,bankHead,qq]
  have hhead1 : ∀ z∈pcHead1,PieceBasic z.1 ∧
      PieceCov D (2/9) two_ninths_pos Fr.const depth (NodeFamily.polynomial Fr (altGeom (2/9) two_ninths_pos).geometry) N 1 z.1 := by
    rw [pcHead1_eq]
    apply catalogueHead_facts hpar hd' hL pcRawSeeds1 9 1 10000 0
    · intro S hS;exact hab S
    · intro S hS;exact hallowed S
    · intro S hS
      rw [show seedOK D (S.law.palette 0) 1 pcSeedLimit (S.toSeed 9 1 10000)=
        seedOK (pcHead 1) (S.law.palette 0) 1 pcSeedLimit (S.toSeed 9 1 10000) from pcSeedTransport o _ _ _ _]
      exact pcRawSeeds1_ok S hS
  have hcells1 : ∀ y∈pcCells1,
      (PieceBasic y.1 ∧ 0≤y.2.R ∧ 1/y.1.s+(125:ℚ)*9≤10000) ∧
      BaseSound D (pcBase.map (KBranch.compile D.tS (D.bS 1) D.cS)) 1 y.1 y.2.R ∧ y.2.R*y.1.t≤(N:ℚ) := by
    intro y hy
    simp only [pcCells1,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · have hk : cellOKb D pcBase 1 125 9 10000 pcCellBase1_0=true := by
        rw [show cellOKb D pcBase 1 125 9 10000 pcCellBase1_0=
          cellOKb (pcHead 1) pcBase 1 125 9 10000 pcCellBase1_0 from pcCellTransport o _ _ _ _ _ _]
        exact pcCell1_0
      have hf := cellOKb_facts (by decide : 1≤D.Q) (by norm_num [D,pcBank,pcHead,bankHead,qq] : 0≤D.α) hk
      exact ⟨hf.1,hf.2,(pcCellLimit1_0).trans (by exact_mod_cast hL)⟩
    · have hk : cellOKb D pcBase 1 125 9 10000 pcCellBase1_1=true := by
        rw [show cellOKb D pcBase 1 125 9 10000 pcCellBase1_1=
          cellOKb (pcHead 1) pcBase 1 125 9 10000 pcCellBase1_1 from pcCellTransport o _ _ _ _ _ _]
        exact pcCell1_1
      have hf := cellOKb_facts (by decide : 1≤D.Q) (by norm_num [D,pcBank,pcHead,bankHead,qq] : 0≤D.α) hk
      exact ⟨hf.1,hf.2,(pcCellLimit1_1).trans (by exact_mod_cast hL)⟩
  have hf1 : ∀ z∈(pcTmpl1.toK 9 20 bankHead.cF).pieces,PieceBasic z.1 ∧
      PieceCov D (2/9) two_ninths_pos Fr.const depth (NodeFamily.polynomial Fr (altGeom (2/9) two_ninths_pos).geometry) N 1 z.1 := by
    intro z hz
    change z∈expPer 9 20 bankHead.cF 125 0 pcCells1++pcHead1 at hz
    rcases List.mem_append.mp hz with hz | hz
    · obtain ⟨n,hn,y,hy,rfl⟩ := mem_expPer hz
      obtain ⟨⟨hbasic,hR,hΩ⟩,hbase,hRlim⟩ := hcells1 y hy
      have hn' : (n:ℚ)≤125 := by exact_mod_cast hn
      exact ⟨trPiece_basic hbasic 9 20 D.cF y.2.R n,
        exp_cov_per_large hpar hd' (by norm_num [D,pcBank,pcHead,bankHead,qq])
          (d1xTranslation 9 1 10000) (by intro n;simpa only [pcBase,d1xTranslation,List.map_cons,List.map_nil] using hd1x)
          hbasic hbase hRlim n (by linarith)⟩
    · exact hhead1 z hz
  have hhead2 : ∀ z∈pcHead2,PieceBasic z.1 ∧
      PieceCov D (2/9) two_ninths_pos Fr.const depth (NodeFamily.polynomial Fr (altGeom (2/9) two_ninths_pos).geometry) N 2 z.1 := by
    rw [pcHead2_eq]
    apply catalogueHead_facts hpar hd' hL pcRawSeeds2 9 1 10000 0
    · intro S hS;exact hab S
    · intro S hS;exact hallowed S
    · intro S hS
      rw [show seedOK D (S.law.palette 0) 2 pcSeedLimit (S.toSeed 9 1 10000)=
        seedOK (pcHead 1) (S.law.palette 0) 2 pcSeedLimit (S.toSeed 9 1 10000) from pcSeedTransport o _ _ _ _]
      exact pcRawSeeds2_ok S hS
  have hcells2 : ∀ y∈pcCells2,
      (PieceBasic y.1 ∧ 0≤y.2.R ∧ 1/y.1.s+(125:ℚ)*9≤10000) ∧
      BaseSound D (pcBase.map (KBranch.compile D.tS (D.bS 2) D.cS)) 2 y.1 y.2.R ∧ y.2.R*y.1.t≤(N:ℚ) := by
    intro y hy
    simp only [pcCells2,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · have hk : cellOKb D pcBase 2 125 9 10000 pcCellBase2_0=true := by
        rw [show cellOKb D pcBase 2 125 9 10000 pcCellBase2_0=
          cellOKb (pcHead 1) pcBase 2 125 9 10000 pcCellBase2_0 from pcCellTransport o _ _ _ _ _ _]
        exact pcCell2_0
      have hf := cellOKb_facts (by decide : 1≤D.Q) (by norm_num [D,pcBank,pcHead,bankHead,qq] : 0≤D.α) hk
      exact ⟨hf.1,hf.2,(pcCellLimit2_0).trans (by exact_mod_cast hL)⟩
    · have hk : cellOKb D pcBase 2 125 9 10000 pcCellBase2_1=true := by
        rw [show cellOKb D pcBase 2 125 9 10000 pcCellBase2_1=
          cellOKb (pcHead 1) pcBase 2 125 9 10000 pcCellBase2_1 from pcCellTransport o _ _ _ _ _ _]
        exact pcCell2_1
      have hf := cellOKb_facts (by decide : 1≤D.Q) (by norm_num [D,pcBank,pcHead,bankHead,qq] : 0≤D.α) hk
      exact ⟨hf.1,hf.2,(pcCellLimit2_1).trans (by exact_mod_cast hL)⟩
  have hf2 : ∀ z∈(pcTmpl2.toK 9 20 bankHead.cF).pieces,PieceBasic z.1 ∧
      PieceCov D (2/9) two_ninths_pos Fr.const depth (NodeFamily.polynomial Fr (altGeom (2/9) two_ninths_pos).geometry) N 2 z.1 := by
    intro z hz
    change z∈expPer 9 20 bankHead.cF 125 0 pcCells2++pcHead2 at hz
    rcases List.mem_append.mp hz with hz | hz
    · obtain ⟨n,hn,y,hy,rfl⟩ := mem_expPer hz
      obtain ⟨⟨hbasic,hR,hΩ⟩,hbase,hRlim⟩ := hcells2 y hy
      have hn' : (n:ℚ)≤125 := by exact_mod_cast hn
      exact ⟨trPiece_basic hbasic 9 20 D.cF y.2.R n,
        exp_cov_per_large hpar hd' (by norm_num [D,pcBank,pcHead,bankHead,qq])
          (d1xTranslation 9 1 10000) (by intro n;simpa only [pcBase,d1xTranslation,List.map_cons,List.map_nil] using hd1x)
          hbasic hbase hRlim n (by linarith)⟩
    · exact hhead2 z hz
  have hhead3 : ∀ z∈pcHead3,PieceBasic z.1 ∧
      PieceCov D (2/9) two_ninths_pos Fr.const depth (NodeFamily.polynomial Fr (altGeom (2/9) two_ninths_pos).geometry) N 3 z.1 := by
    rw [pcHead3_eq]
    apply catalogueHead_facts hpar hd' hL pcRawSeeds3 9 1 10000 0
    · intro S hS;exact hab S
    · intro S hS;exact hallowed S
    · intro S hS
      rw [show seedOK D (S.law.palette 0) 3 pcSeedLimit (S.toSeed 9 1 10000)=
        seedOK (pcHead 1) (S.law.palette 0) 3 pcSeedLimit (S.toSeed 9 1 10000) from pcSeedTransport o _ _ _ _]
      exact pcRawSeeds3_ok S hS
  have hcells3 : ∀ y∈pcCells3,
      (PieceBasic y.1 ∧ 0≤y.2.R ∧ 1/y.1.s+(125:ℚ)*9≤10000) ∧
      BaseSound D (pcBase.map (KBranch.compile D.tS (D.bS 3) D.cS)) 3 y.1 y.2.R ∧ y.2.R*y.1.t≤(N:ℚ) := by
    intro y hy
    simp only [pcCells3,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · have hk : cellOKb D pcBase 3 125 9 10000 pcCellBase3_0=true := by
        rw [show cellOKb D pcBase 3 125 9 10000 pcCellBase3_0=
          cellOKb (pcHead 1) pcBase 3 125 9 10000 pcCellBase3_0 from pcCellTransport o _ _ _ _ _ _]
        exact pcCell3_0
      have hf := cellOKb_facts (by decide : 1≤D.Q) (by norm_num [D,pcBank,pcHead,bankHead,qq] : 0≤D.α) hk
      exact ⟨hf.1,hf.2,(pcCellLimit3_0).trans (by exact_mod_cast hL)⟩
    · have hk : cellOKb D pcBase 3 125 9 10000 pcCellBase3_1=true := by
        rw [show cellOKb D pcBase 3 125 9 10000 pcCellBase3_1=
          cellOKb (pcHead 1) pcBase 3 125 9 10000 pcCellBase3_1 from pcCellTransport o _ _ _ _ _ _]
        exact pcCell3_1
      have hf := cellOKb_facts (by decide : 1≤D.Q) (by norm_num [D,pcBank,pcHead,bankHead,qq] : 0≤D.α) hk
      exact ⟨hf.1,hf.2,(pcCellLimit3_1).trans (by exact_mod_cast hL)⟩
  have hf3 : ∀ z∈(pcTmpl3.toK 9 20 bankHead.cF).pieces,PieceBasic z.1 ∧
      PieceCov D (2/9) two_ninths_pos Fr.const depth (NodeFamily.polynomial Fr (altGeom (2/9) two_ninths_pos).geometry) N 3 z.1 := by
    intro z hz
    change z∈expPer 9 20 bankHead.cF 125 0 pcCells3++pcHead3 at hz
    rcases List.mem_append.mp hz with hz | hz
    · obtain ⟨n,hn,y,hy,rfl⟩ := mem_expPer hz
      obtain ⟨⟨hbasic,hR,hΩ⟩,hbase,hRlim⟩ := hcells3 y hy
      have hn' : (n:ℚ)≤125 := by exact_mod_cast hn
      exact ⟨trPiece_basic hbasic 9 20 D.cF y.2.R n,
        exp_cov_per_large hpar hd' (by norm_num [D,pcBank,pcHead,bankHead,qq])
          (d1xTranslation 9 1 10000) (by intro n;simpa only [pcBase,d1xTranslation,List.map_cons,List.map_nil] using hd1x)
          hbasic hbase hRlim n (by linarith)⟩
    · exact hhead3 z hz
  have hhead4 : ∀ z∈pcHead4,PieceBasic z.1 ∧
      PieceCov D (2/9) two_ninths_pos Fr.const depth (NodeFamily.polynomial Fr (altGeom (2/9) two_ninths_pos).geometry) N 4 z.1 := by
    rw [pcHead4_eq]
    apply catalogueHead_facts hpar hd' hL pcRawSeeds4 9 1 10000 0
    · intro S hS;exact hab S
    · intro S hS;exact hallowed S
    · intro S hS
      rw [show seedOK D (S.law.palette 0) 4 pcSeedLimit (S.toSeed 9 1 10000)=
        seedOK (pcHead 1) (S.law.palette 0) 4 pcSeedLimit (S.toSeed 9 1 10000) from pcSeedTransport o _ _ _ _]
      exact pcRawSeeds4_ok S hS
  have hcells4 : ∀ y∈pcCells4,
      (PieceBasic y.1 ∧ 0≤y.2.R ∧ 1/y.1.s+(125:ℚ)*9≤10000) ∧
      BaseSound D (pcBase.map (KBranch.compile D.tS (D.bS 4) D.cS)) 4 y.1 y.2.R ∧ y.2.R*y.1.t≤(N:ℚ) := by
    intro y hy
    simp only [pcCells4,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · have hk : cellOKb D pcBase 4 125 9 10000 pcCellBase4_0=true := by
        rw [show cellOKb D pcBase 4 125 9 10000 pcCellBase4_0=
          cellOKb (pcHead 1) pcBase 4 125 9 10000 pcCellBase4_0 from pcCellTransport o _ _ _ _ _ _]
        exact pcCell4_0
      have hf := cellOKb_facts (by decide : 1≤D.Q) (by norm_num [D,pcBank,pcHead,bankHead,qq] : 0≤D.α) hk
      exact ⟨hf.1,hf.2,(pcCellLimit4_0).trans (by exact_mod_cast hL)⟩
    · have hk : cellOKb D pcBase 4 125 9 10000 pcCellBase4_1=true := by
        rw [show cellOKb D pcBase 4 125 9 10000 pcCellBase4_1=
          cellOKb (pcHead 1) pcBase 4 125 9 10000 pcCellBase4_1 from pcCellTransport o _ _ _ _ _ _]
        exact pcCell4_1
      have hf := cellOKb_facts (by decide : 1≤D.Q) (by norm_num [D,pcBank,pcHead,bankHead,qq] : 0≤D.α) hk
      exact ⟨hf.1,hf.2,(pcCellLimit4_1).trans (by exact_mod_cast hL)⟩
  have hf4 : ∀ z∈(pcTmpl4.toK 9 20 bankHead.cF).pieces,PieceBasic z.1 ∧
      PieceCov D (2/9) two_ninths_pos Fr.const depth (NodeFamily.polynomial Fr (altGeom (2/9) two_ninths_pos).geometry) N 4 z.1 := by
    intro z hz
    change z∈expPer 9 20 bankHead.cF 125 0 pcCells4++pcHead4 at hz
    rcases List.mem_append.mp hz with hz | hz
    · obtain ⟨n,hn,y,hy,rfl⟩ := mem_expPer hz
      obtain ⟨⟨hbasic,hR,hΩ⟩,hbase,hRlim⟩ := hcells4 y hy
      have hn' : (n:ℚ)≤125 := by exact_mod_cast hn
      exact ⟨trPiece_basic hbasic 9 20 D.cF y.2.R n,
        exp_cov_per_large hpar hd' (by norm_num [D,pcBank,pcHead,bankHead,qq])
          (d1xTranslation 9 1 10000) (by intro n;simpa only [pcBase,d1xTranslation,List.map_cons,List.map_nil] using hd1x)
          hbasic hbase hRlim n (by linarith)⟩
    · exact hhead4 z hz
  have hall : ∀ x∈D.tmpls,∀ z∈x.2.pieces,PieceBasic z.1 ∧
      PieceCov D (2/9) two_ninths_pos Fr.const depth (NodeFamily.polynomial Fr (altGeom (2/9) two_ninths_pos).geometry) N x.1 z.1 := by
    intro x hx
    change x∈[(1,pcTmpl1.toK 9 20 bankHead.cF), (2,pcTmpl2.toK 9 20 bankHead.cF), (3,pcTmpl3.toK 9 20 bankHead.cF), (4,pcTmpl4.toK 9 20 bankHead.cF)] at hx
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact hf1
    · exact hf2
    · exact hf3
    · exact hf4
  exact hasScaledContent_of_facts D hpar hClasses hHeads (2/9) two_ninths_pos
    (by norm_num [D,pcBank,pcHead,bankHead,qq]) Fr.const depth
    (NodeFamily.polynomial Fr (altGeom (2/9) two_ninths_pos).geometry)
    (AltQ.ofFrame (2/9) two_ninths_pos (by norm_num) Fr hcF) B N
    (fun x hx z hz => (hall x hx z hz).1) (fun x hx z hz => (hall x hx z hz).2) hcat hPre

theorem fifths1_content_auto (depth : ℕ) (hd : depth≤64) :
    HasScaledContent (AltEven (2/9) two_ninths_pos fifths1 depth) (altGeom (2/9) two_ninths_pos).scale (bankData.Λ:ℝ) := by
  apply pc_content_o 4 depth (max (NFr (1/fifths1.norm) (-1/fifths1.norm) 5 9) 50) (SmallBudget.add (SmallBudget.sqrtLog 7 122) SmallBudget.unit) hd cFr_fifths1 (fifths_catValid fifths1_shift depth) (fifths_preValid fifths1_shift depth cFr_fifths1)
  · intro ν j0 j1
    exact catValid_pre (2/9) two_ninths_pos (shift_twoTerm fifths1_shift) (nm:=25) (by rw [fifths1_shift.norm_eq];norm_num) depth 9 (max (NFr (1/fifths1.norm) (-1/fifths1.norm) 5 9) 50) (by norm_num) (fun p hp h => ⟨not_dvd_sq_of_lt hp (by norm_num) (by omega),by omega,by omega⟩) ν j0 j1
  · intro ν hν
    exact WrapPrefixCheck.catValid_prefix_full (2/9) two_ninths_pos (shift_twoTerm fifths1_shift) (nm:=25) (by rw [fifths1_shift.norm_eq];norm_num) depth 9 (max (NFr (1/fifths1.norm) (-1/fifths1.norm) 5 9) 50) ν hν (fun p hp h => ⟨not_dvd_sq_of_lt hp (by norm_num) (by omega),by omega⟩)
  · exact pcParams4
  · exact pcClasses4
  · intro x hx
    change x∈[(1,pcTmpl1.toK 9 20 bankHead.cF), (2,pcTmpl2.toK 9 20 bankHead.cF), (3,pcTmpl3.toK 9 20 bankHead.cF), (4,pcTmpl4.toK 9 20 bankHead.cF)] at hx
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact pcTemplate1Head4
    · exact pcTemplate2Head4
    · exact pcTemplate3Head4
    · exact pcTemplate4Head4
#print axioms fifths1_content_auto
theorem fifths2_content_auto (depth : ℕ) (hd : depth≤64) :
    HasScaledContent (AltEven (2/9) two_ninths_pos fifths2 depth) (altGeom (2/9) two_ninths_pos).scale (bankData.Λ:ℝ) := by
  apply pc_content_o 3 depth (max (NFr (1/fifths2.norm) (-1/fifths2.norm) 5 9) 50) (SmallBudget.add (SmallBudget.sqrtLog 7 122) SmallBudget.unit) hd cFr_fifths2 (fifths_catValid fifths2_shift depth) (fifths_preValid fifths2_shift depth cFr_fifths2)
  · intro ν j0 j1
    exact catValid_pre (2/9) two_ninths_pos (shift_twoTerm fifths2_shift) (nm:=25) (by rw [fifths2_shift.norm_eq];norm_num) depth 9 (max (NFr (1/fifths2.norm) (-1/fifths2.norm) 5 9) 50) (by norm_num) (fun p hp h => ⟨not_dvd_sq_of_lt hp (by norm_num) (by omega),by omega,by omega⟩) ν j0 j1
  · intro ν hν
    exact WrapPrefixCheck.catValid_prefix_full (2/9) two_ninths_pos (shift_twoTerm fifths2_shift) (nm:=25) (by rw [fifths2_shift.norm_eq];norm_num) depth 9 (max (NFr (1/fifths2.norm) (-1/fifths2.norm) 5 9) 50) ν hν (fun p hp h => ⟨not_dvd_sq_of_lt hp (by norm_num) (by omega),by omega⟩)
  · exact pcParams3
  · exact pcClasses3
  · intro x hx
    change x∈[(1,pcTmpl1.toK 9 20 bankHead.cF), (2,pcTmpl2.toK 9 20 bankHead.cF), (3,pcTmpl3.toK 9 20 bankHead.cF), (4,pcTmpl4.toK 9 20 bankHead.cF)] at hx
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact pcTemplate1Head3
    · exact pcTemplate2Head3
    · exact pcTemplate3Head3
    · exact pcTemplate4Head3
#print axioms fifths2_content_auto
theorem fifths3_content_auto (depth : ℕ) (hd : depth≤64) :
    HasScaledContent (AltEven (2/9) two_ninths_pos fifths3 depth) (altGeom (2/9) two_ninths_pos).scale (bankData.Λ:ℝ) := by
  apply pc_content_o 2 depth (max (NFr (1/fifths3.norm) (-1/fifths3.norm) 5 9) 50) (SmallBudget.add (SmallBudget.sqrtLog 7 122) SmallBudget.unit) hd cFr_fifths3 (fifths_catValid fifths3_shift depth) (fifths_preValid fifths3_shift depth cFr_fifths3)
  · intro ν j0 j1
    exact catValid_pre (2/9) two_ninths_pos (shift_twoTerm fifths3_shift) (nm:=25) (by rw [fifths3_shift.norm_eq];norm_num) depth 9 (max (NFr (1/fifths3.norm) (-1/fifths3.norm) 5 9) 50) (by norm_num) (fun p hp h => ⟨not_dvd_sq_of_lt hp (by norm_num) (by omega),by omega,by omega⟩) ν j0 j1
  · intro ν hν
    exact WrapPrefixCheck.catValid_prefix_full (2/9) two_ninths_pos (shift_twoTerm fifths3_shift) (nm:=25) (by rw [fifths3_shift.norm_eq];norm_num) depth 9 (max (NFr (1/fifths3.norm) (-1/fifths3.norm) 5 9) 50) ν hν (fun p hp h => ⟨not_dvd_sq_of_lt hp (by norm_num) (by omega),by omega⟩)
  · exact pcParams2
  · exact pcClasses2
  · intro x hx
    change x∈[(1,pcTmpl1.toK 9 20 bankHead.cF), (2,pcTmpl2.toK 9 20 bankHead.cF), (3,pcTmpl3.toK 9 20 bankHead.cF), (4,pcTmpl4.toK 9 20 bankHead.cF)] at hx
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact pcTemplate1Head2
    · exact pcTemplate2Head2
    · exact pcTemplate3Head2
    · exact pcTemplate4Head2
#print axioms fifths3_content_auto
theorem fifths4_content_auto (depth : ℕ) (hd : depth≤64) :
    HasScaledContent (AltEven (2/9) two_ninths_pos fifths4 depth) (altGeom (2/9) two_ninths_pos).scale (bankData.Λ:ℝ) := by
  apply pc_content_o 1 depth (max (NFr (1/fifths4.norm) (-1/fifths4.norm) 5 9) 50) (SmallBudget.add (SmallBudget.sqrtLog 7 122) SmallBudget.unit) hd cFr_fifths4 (fifths_catValid fifths4_shift depth) (fifths_preValid fifths4_shift depth cFr_fifths4)
  · intro ν j0 j1
    exact catValid_pre (2/9) two_ninths_pos (shift_twoTerm fifths4_shift) (nm:=25) (by rw [fifths4_shift.norm_eq];norm_num) depth 9 (max (NFr (1/fifths4.norm) (-1/fifths4.norm) 5 9) 50) (by norm_num) (fun p hp h => ⟨not_dvd_sq_of_lt hp (by norm_num) (by omega),by omega,by omega⟩) ν j0 j1
  · intro ν hν
    exact WrapPrefixCheck.catValid_prefix_full (2/9) two_ninths_pos (shift_twoTerm fifths4_shift) (nm:=25) (by rw [fifths4_shift.norm_eq];norm_num) depth 9 (max (NFr (1/fifths4.norm) (-1/fifths4.norm) 5 9) 50) ν hν (fun p hp h => ⟨not_dvd_sq_of_lt hp (by norm_num) (by omega),by omega⟩)
  · exact pcParams1
  · exact pcClasses1
  · intro x hx
    change x∈[(1,pcTmpl1.toK 9 20 bankHead.cF), (2,pcTmpl2.toK 9 20 bankHead.cF), (3,pcTmpl3.toK 9 20 bankHead.cF), (4,pcTmpl4.toK 9 20 bankHead.cF)] at hx
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact pcTemplate1Head1
    · exact pcTemplate2Head1
    · exact pcTemplate3Head1
    · exact pcTemplate4Head1
#print axioms fifths4_content_auto
end CatalanCore.Uniform.Bank.FifthsContent.Level3Auto
#print axioms CatalanCore.Uniform.Bank.FifthsContent.Level3Auto.pc_content_o
