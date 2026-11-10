module
public import CatalanCore.Uniform.Bank.ThirdsContent.Level3Data
public import CatalanCore.Uniform.Bank.ThirdsContent.Edge
public import CatalanCore.Uniform.Bank.Thirds.Geom
public import CatalanFrames.Thirds.TargetConstants
public import CatalanCore.Uniform.Content.BankShared.KTerm.CatalogueOrbit.Sound
public import CatalanCore.Uniform.Content.UFSimple.WrapPrefixCheck
public import CatalanCore.Uniform.Content.BankShared.Check.Prefix
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 3200000
namespace CatalanCore.Uniform.Bank.ThirdsContent.Level3Auto
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.BankShared
  CatalanCore.Uniform.Content.BankShared.Check CatalanCore.Uniform.Content.BankShared.TwoTerm
  CatalanCore.Uniform.Content.SmallPrimes CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanFrames.HybCommon
  CatalanFrames.HybGen CatalanFrames.Thirds CatalanCore.Uniform.Bank.ThirdsContent
  CatalanCore.Uniform.Bank.Thirds CatalanCore.Uniform.Content.RankProducer


open CatalanCore.Uniform.Content.BankShared.KTerm
open CatalanCore.Uniform.Content.UFSimple
theorem thirds_catValidUF {Fr : Frame} {e : ℕ} (T : ThirdsData Fr e) (depth : ℕ) :
    CatValid (3 / 10) c310_pos Fr depth 3 e 5 (max (NFr (1 / Fr.norm) (-1 / Fr.norm) 3 7) 23) bankData.cat := by
  have he := T.he
  rw [bankData_cat]
  apply catValid_append
  · apply catValid_append
    · exact catValid_bankUFwP (thirdsInst T) (arith_of_bad (thirds_badInfo T)).L_eq (thirds_levels T) (3 / 10)
        c310_pos (by norm_num) (ThirdsData.twoTerm T) (nm := 3 * 3) (by rw [T.norm_eq]; norm_num) depth 5 7 23
        (by norm_num) (by norm_num) (by norm_num) le_rfl
        (fun p hp h => ⟨not_dvd_sq_of_lt (q:=3) hp (by norm_num) (by omega), by omega, by omega,
          not_bad_of_levels (thirds_levels T) hp (show 5 ≤ p by omega), (show 5 ≤ p by omega), by omega⟩)
        (fun p hp h j k hk hj0 hjq _ _ => by
          have h5 : 5 ≤ p := by omega
          have hb := (thirds_good T hp h5).2
          obtain ⟨h1, -⟩ := kq_eq_poleIndex (thirdsCD T) (fun _ => rfl) (by omega) (by omega) hp (by omega) hb
            (thirds_kq_att T p hp.isPrimePow hb)
          have hk' : 3 * k = j * p + (3 - (3 - e)) := by rw [show 3 - (3 - e) = e by omega]; exact hk
          have h2 := (rootClass_unique hp (by omega) (by omega) (by omega) hjq hk').2
          show (thirdsCD T).kq p = k
          rw [h1, h2])
        bankWins bankPres
    · exact CatalanCore.Uniform.Content.UFSimple.WrapCheck.catValid_wrap (3 / 10) c310_pos (ThirdsData.twoTerm T) (nm := 3 * 3) (by rw [T.norm_eq]; norm_num) depth 5 _ (fun p hp h => ⟨not_dvd_sq_of_lt (q:=3) hp (by norm_num) (by omega), by omega⟩)
  · exact CatalanCore.Uniform.Content.UFSimple.catValid_prefixBranches (3 / 10) c310_pos (ThirdsData.twoTerm T) (nm := 3 * 3) (by rw [T.norm_eq]; norm_num) depth 5 _ 24 (fun p hp h => ⟨not_dvd_sq_of_lt (q:=3) hp (by norm_num) (by omega), by omega⟩)

theorem thirds_preValid {Fr : Frame} {e : ℕ} (T : ThirdsData Fr e) (depth : ℕ) :
    PreValid (3 / 10) c310_pos Fr depth 6 thirdsBudget (qq 3 1000) (qq 23 10) := by
  intro i hi p _ hpM h
  have hp : p.Prime := Fact.out
  have h5 : 5 ≤ p := by
    have h2 : p ≠ 2 := fun h => hpM (by rw [h]; norm_num)
    have h3 : p ≠ 3 := fun h => hpM (by rw [h]; norm_num)
    have h4 : p ≠ 4 := fun h => by rw [h] at hp; norm_num at hp
    have := hp.two_le
    omega
  have e1 : ((qq 3 1000 : ℚ) : ℝ) = ((3 : ℕ) : ℝ) / ((1000 : ℕ) : ℝ) := by norm_num [qq]
  rw [e1, floor_frac 3 1000 i.1] at h
  obtain ⟨n, hn, hb⟩ := thirds_pre_gle T depth i hi p h5 h
  refine ⟨n, hn, ?_⟩
  have e2 : ((qq 23 10 : ℚ) : ℝ) = 23 / 10 := by norm_num [qq]
  rw [e2]
  exact hb

theorem cFr_thirdsAc_le : CatalanCore.Uniform.Content.BankShared.cFr thirdsAc ≤ 25 := by
  have : CatalanCore.Uniform.Content.BankShared.cFr thirdsAc =
      CatalanCore.Uniform.Bank.ThirdsContent.cFr thirdsAc := rfl
  rw [this, cFr_thirdsAc]; norm_num

theorem cFr_thirdsBc_le : CatalanCore.Uniform.Content.BankShared.cFr thirdsBc ≤ 25 := by
  have : CatalanCore.Uniform.Content.BankShared.cFr thirdsBc =
      CatalanCore.Uniform.Bank.ThirdsContent.cFr thirdsBc := rfl
  rw [this, cFr_thirdsBc]


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
    (hOld : CatValid (3/10) c310_pos Fr depth 3 o bankHead.Pbad Nold bankData.cat)
    (hPre : PreValid (3/10) c310_pos Fr depth bankHead.M B bankHead.t0 bankHead.α0b)
    (hAllPre : ∀ ν j0 j1,CatValid (3/10) c310_pos Fr depth 3 o bankHead.Pbad Nold [brPre ν j0 j1])
    (hAllWrap : ∀ ν,1≤ν → CatValid (3/10) c310_pos Fr depth 3 o bankHead.Pbad Nold [WrapPrefixCheck.brPrefix ν])
    (hParams : kcheckParams (pcBank o)=true) (hClasses : kclassOK (pcBank o)=true)
    (hHeads : ∀ x∈(pcBank o).tmpls,ktmplHead (pcBank o) x.1 x.2=true) :
    HasScaledContent (AltEven (3/10) c310_pos Fr depth) (altGeom (3/10) c310_pos).scale (bankData.Λ:ℝ) := by
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
  have hcat : KCatValid (3/10) c310_pos Fr depth D.shifts D.Q D.Pbad N D.kcat :=
    (legacy_kcat_valid (3/10) c310_pos Fr.const depth
      (NodeFamily.polynomial Fr (altGeom (3/10) c310_pos).geometry) 3 o bankHead.Pbad Nold bankHead.cat hOld hD6).mono_threshold hNold
  have hlegacy : KCatValid (3/10) c310_pos Fr depth D.shifts D.Q D.Pbad N pcLegacyCatalogue := by
    intro br hb
    exact hcat br (List.mem_append.mpr (Or.inl hb))
  have hd1x : KCatValid (3/10) c310_pos Fr depth D.shifts D.Q D.Pbad N [kbD1xB] :=
    (legacy_d1x_valid (3/10) c310_pos Fr.const depth
      (NodeFamily.polynomial Fr (altGeom (3/10) c310_pos).geometry) 3 o bankHead.Pbad Nold bankHead.cat hOld hD1x).mono_threshold hNold
  have hpre (ν j0 j1 : ℕ) : KCatValid (3/10) c310_pos Fr depth D.shifts D.Q D.Pbad N [(brPre ν j0 j1).liftK 0] := by
    have h := (hAllPre ν j0 j1).liftK (3/10) c310_pos Fr.const depth
      (NodeFamily.polynomial Fr (altGeom (3/10) c310_pos).geometry) 3 o bankHead.Pbad Nold [brPre ν j0 j1]
      (legacyShifts 3 o) 0 3 (by simp [legacyShifts]) rfl rfl le_rfl
    exact (show KCatValid (3/10) c310_pos Fr depth D.shifts D.Q D.Pbad Nold [(brPre ν j0 j1).liftK 0] by
      simpa only [KCatValid,D,pcBank,pcHead,bankHead,List.map_cons,List.map_nil] using h).mono_threshold hNold
  have hwrap (ν : ℕ) (hν : 1≤ν) : KCatValid (3/10) c310_pos Fr depth D.shifts D.Q D.Pbad N [(WrapPrefixCheck.brPrefix ν).liftK 0] := by
    have h := (hAllWrap ν hν).liftK (3/10) c310_pos Fr.const depth
      (NodeFamily.polynomial Fr (altGeom (3/10) c310_pos).geometry) 3 o bankHead.Pbad Nold [WrapPrefixCheck.brPrefix ν]
      (legacyShifts 3 o) 0 3 (by simp [legacyShifts]) rfl rfl le_rfl
    exact (show KCatValid (3/10) c310_pos Fr depth D.shifts D.Q D.Pbad Nold [(WrapPrefixCheck.brPrefix ν).liftK 0] by
      simpa only [KCatValid,D,pcBank,pcHead,bankHead,List.map_cons,List.map_nil] using h).mono_threshold hNold
  have hallowed (S : CatalogueSeed pcLegacyCatalogue) :
      S.law.Allowed (KCatValidFam (3/10) c310_pos Fr.const depth
        (NodeFamily.polynomial Fr (altGeom (3/10) c310_pos).geometry) D.shifts D.Q D.Pbad N) 0 := by
    cases h:S.law with
    | constant indices => simpa only [h,CatalogueOrbitLaw.Allowed,KCatValid] using hlegacy
    | d1x => simpa only [h,CatalogueOrbitLaw.Allowed,KCatValid] using hd1x
    | pre ν j0 j1 => simpa only [h,CatalogueOrbitLaw.Allowed,KCatValid] using (fun ν' => hpre ν' j0 j1)
    | wrap ν hν => simpa only [h,CatalogueOrbitLaw.Allowed,KCatValid] using hwrap
  have hab (S : CatalogueSeed pcLegacyCatalogue) : D.α*S.law.shiftB 20=S.law.shiftA 3 := by
    cases S.law <;> norm_num [CatalogueOrbitLaw.shiftB,CatalogueOrbitLaw.shiftA,D,pcBank,pcHead,bankHead,qq]
  have hhead1 : ∀ z∈pcHead1,PieceBasic z.1 ∧
      CatalanCore.Uniform.Content.BankShared.KTerm.PieceCov D (3/10) c310_pos Fr.const depth (NodeFamily.polynomial Fr (altGeom (3/10) c310_pos).geometry) N 1 z.1 := by
    rw [pcHead1_eq]
    apply catalogueHead_facts hpar hd' hL pcRawSeeds1 20 3 10000 0
    · intro S hS;exact hab S
    · intro S hS;exact hallowed S
    · intro S hS
      rw [show seedOK D (S.law.palette 0) 1 pcSeedLimit (S.toSeed 20 3 10000)=
        seedOK (pcHead 1) (S.law.palette 0) 1 pcSeedLimit (S.toSeed 20 3 10000) from pcSeedTransport o _ _ _ _]
      exact pcRawSeeds1_ok S hS
  have hcells1 : ∀ y∈pcCells1,
      (PieceBasic y.1 ∧ 0≤y.2.R ∧ 1/y.1.s+(41:ℚ)*20≤10000) ∧
      BaseSound D (pcBase.map (KBranch.compile D.tS (D.bS 1) D.cS)) 1 y.1 y.2.R ∧ y.2.R*y.1.t≤(N:ℚ) := by
    intro y hy
    simp only [pcCells1,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
    · have hk : cellOKb D pcBase 1 41 20 10000 pcCellBase1_0=true := by
        rw [show cellOKb D pcBase 1 41 20 10000 pcCellBase1_0=
          cellOKb (pcHead 1) pcBase 1 41 20 10000 pcCellBase1_0 from pcCellTransport o _ _ _ _ _ _]
        exact pcCell1_0
      have hf := cellOKb_facts (by norm_num [D,pcBank,pcHead,bankHead] : 1≤D.Q) (by norm_num [D,pcBank,pcHead,bankHead,qq] : 0≤D.α) hk
      exact ⟨hf.1,hf.2,(pcCellLimit1_0).trans (by exact_mod_cast hL)⟩
    · have hk : cellOKb D pcBase 1 41 20 10000 pcCellBase1_1=true := by
        rw [show cellOKb D pcBase 1 41 20 10000 pcCellBase1_1=
          cellOKb (pcHead 1) pcBase 1 41 20 10000 pcCellBase1_1 from pcCellTransport o _ _ _ _ _ _]
        exact pcCell1_1
      have hf := cellOKb_facts (by norm_num [D,pcBank,pcHead,bankHead] : 1≤D.Q) (by norm_num [D,pcBank,pcHead,bankHead,qq] : 0≤D.α) hk
      exact ⟨hf.1,hf.2,(pcCellLimit1_1).trans (by exact_mod_cast hL)⟩
    · have hk : cellOKb D pcBase 1 41 20 10000 pcCellBase1_2=true := by
        rw [show cellOKb D pcBase 1 41 20 10000 pcCellBase1_2=
          cellOKb (pcHead 1) pcBase 1 41 20 10000 pcCellBase1_2 from pcCellTransport o _ _ _ _ _ _]
        exact pcCell1_2
      have hf := cellOKb_facts (by norm_num [D,pcBank,pcHead,bankHead] : 1≤D.Q) (by norm_num [D,pcBank,pcHead,bankHead,qq] : 0≤D.α) hk
      exact ⟨hf.1,hf.2,(pcCellLimit1_2).trans (by exact_mod_cast hL)⟩
    · have hk : cellOKb D pcBase 1 41 20 10000 pcCellBase1_3=true := by
        rw [show cellOKb D pcBase 1 41 20 10000 pcCellBase1_3=
          cellOKb (pcHead 1) pcBase 1 41 20 10000 pcCellBase1_3 from pcCellTransport o _ _ _ _ _ _]
        exact pcCell1_3
      have hf := cellOKb_facts (by norm_num [D,pcBank,pcHead,bankHead] : 1≤D.Q) (by norm_num [D,pcBank,pcHead,bankHead,qq] : 0≤D.α) hk
      exact ⟨hf.1,hf.2,(pcCellLimit1_3).trans (by exact_mod_cast hL)⟩
    · have hk : cellOKb D pcBase 1 41 20 10000 pcCellBase1_4=true := by
        rw [show cellOKb D pcBase 1 41 20 10000 pcCellBase1_4=
          cellOKb (pcHead 1) pcBase 1 41 20 10000 pcCellBase1_4 from pcCellTransport o _ _ _ _ _ _]
        exact pcCell1_4
      have hf := cellOKb_facts (by norm_num [D,pcBank,pcHead,bankHead] : 1≤D.Q) (by norm_num [D,pcBank,pcHead,bankHead,qq] : 0≤D.α) hk
      exact ⟨hf.1,hf.2,(pcCellLimit1_4).trans (by exact_mod_cast hL)⟩
    · have hk : cellOKb D pcBase 1 41 20 10000 pcCellBase1_5=true := by
        rw [show cellOKb D pcBase 1 41 20 10000 pcCellBase1_5=
          cellOKb (pcHead 1) pcBase 1 41 20 10000 pcCellBase1_5 from pcCellTransport o _ _ _ _ _ _]
        exact pcCell1_5
      have hf := cellOKb_facts (by norm_num [D,pcBank,pcHead,bankHead] : 1≤D.Q) (by norm_num [D,pcBank,pcHead,bankHead,qq] : 0≤D.α) hk
      exact ⟨hf.1,hf.2,(pcCellLimit1_5).trans (by exact_mod_cast hL)⟩
  have hf1 : ∀ z∈(pcTmpl1.toK 20 46 bankHead.cF).pieces,PieceBasic z.1 ∧
      CatalanCore.Uniform.Content.BankShared.KTerm.PieceCov D (3/10) c310_pos Fr.const depth (NodeFamily.polynomial Fr (altGeom (3/10) c310_pos).geometry) N 1 z.1 := by
    intro z hz
    change z∈expPer 20 46 bankHead.cF 41 0 pcCells1++pcHead1 at hz
    rcases List.mem_append.mp hz with hz | hz
    · obtain ⟨n,hn,y,hy,rfl⟩ := mem_expPer hz
      obtain ⟨⟨hbasic,hR,hΩ⟩,hbase,hRlim⟩ := hcells1 y hy
      have hn' : (n:ℚ)≤41 := by exact_mod_cast hn
      exact ⟨trPiece_basic hbasic 20 46 D.cF y.2.R n,
        exp_cov_per_large hpar hd' (by norm_num [D,pcBank,pcHead,bankHead,qq])
          (d1xTranslation 20 3 10000) (by intro n;simpa only [pcBase,d1xTranslation,List.map_cons,List.map_nil,KCatValid] using hd1x)
          hbasic hbase hRlim n (by linarith)⟩
    · exact hhead1 z hz
  have hhead2 : ∀ z∈pcHead2,PieceBasic z.1 ∧
      CatalanCore.Uniform.Content.BankShared.KTerm.PieceCov D (3/10) c310_pos Fr.const depth (NodeFamily.polynomial Fr (altGeom (3/10) c310_pos).geometry) N 2 z.1 := by
    rw [pcHead2_eq]
    apply catalogueHead_facts hpar hd' hL pcRawSeeds2 20 3 10000 0
    · intro S hS;exact hab S
    · intro S hS;exact hallowed S
    · intro S hS
      rw [show seedOK D (S.law.palette 0) 2 pcSeedLimit (S.toSeed 20 3 10000)=
        seedOK (pcHead 1) (S.law.palette 0) 2 pcSeedLimit (S.toSeed 20 3 10000) from pcSeedTransport o _ _ _ _]
      exact pcRawSeeds2_ok S hS
  have hcells2 : ∀ y∈pcCells2,
      (PieceBasic y.1 ∧ 0≤y.2.R ∧ 1/y.1.s+(41:ℚ)*20≤10000) ∧
      BaseSound D (pcBase.map (KBranch.compile D.tS (D.bS 2) D.cS)) 2 y.1 y.2.R ∧ y.2.R*y.1.t≤(N:ℚ) := by
    intro y hy
    simp only [pcCells2,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
    · have hk : cellOKb D pcBase 2 41 20 10000 pcCellBase2_0=true := by
        rw [show cellOKb D pcBase 2 41 20 10000 pcCellBase2_0=
          cellOKb (pcHead 1) pcBase 2 41 20 10000 pcCellBase2_0 from pcCellTransport o _ _ _ _ _ _]
        exact pcCell2_0
      have hf := cellOKb_facts (by norm_num [D,pcBank,pcHead,bankHead] : 1≤D.Q) (by norm_num [D,pcBank,pcHead,bankHead,qq] : 0≤D.α) hk
      exact ⟨hf.1,hf.2,(pcCellLimit2_0).trans (by exact_mod_cast hL)⟩
    · have hk : cellOKb D pcBase 2 41 20 10000 pcCellBase2_1=true := by
        rw [show cellOKb D pcBase 2 41 20 10000 pcCellBase2_1=
          cellOKb (pcHead 1) pcBase 2 41 20 10000 pcCellBase2_1 from pcCellTransport o _ _ _ _ _ _]
        exact pcCell2_1
      have hf := cellOKb_facts (by norm_num [D,pcBank,pcHead,bankHead] : 1≤D.Q) (by norm_num [D,pcBank,pcHead,bankHead,qq] : 0≤D.α) hk
      exact ⟨hf.1,hf.2,(pcCellLimit2_1).trans (by exact_mod_cast hL)⟩
    · have hk : cellOKb D pcBase 2 41 20 10000 pcCellBase2_2=true := by
        rw [show cellOKb D pcBase 2 41 20 10000 pcCellBase2_2=
          cellOKb (pcHead 1) pcBase 2 41 20 10000 pcCellBase2_2 from pcCellTransport o _ _ _ _ _ _]
        exact pcCell2_2
      have hf := cellOKb_facts (by norm_num [D,pcBank,pcHead,bankHead] : 1≤D.Q) (by norm_num [D,pcBank,pcHead,bankHead,qq] : 0≤D.α) hk
      exact ⟨hf.1,hf.2,(pcCellLimit2_2).trans (by exact_mod_cast hL)⟩
    · have hk : cellOKb D pcBase 2 41 20 10000 pcCellBase2_3=true := by
        rw [show cellOKb D pcBase 2 41 20 10000 pcCellBase2_3=
          cellOKb (pcHead 1) pcBase 2 41 20 10000 pcCellBase2_3 from pcCellTransport o _ _ _ _ _ _]
        exact pcCell2_3
      have hf := cellOKb_facts (by norm_num [D,pcBank,pcHead,bankHead] : 1≤D.Q) (by norm_num [D,pcBank,pcHead,bankHead,qq] : 0≤D.α) hk
      exact ⟨hf.1,hf.2,(pcCellLimit2_3).trans (by exact_mod_cast hL)⟩
    · have hk : cellOKb D pcBase 2 41 20 10000 pcCellBase2_4=true := by
        rw [show cellOKb D pcBase 2 41 20 10000 pcCellBase2_4=
          cellOKb (pcHead 1) pcBase 2 41 20 10000 pcCellBase2_4 from pcCellTransport o _ _ _ _ _ _]
        exact pcCell2_4
      have hf := cellOKb_facts (by norm_num [D,pcBank,pcHead,bankHead] : 1≤D.Q) (by norm_num [D,pcBank,pcHead,bankHead,qq] : 0≤D.α) hk
      exact ⟨hf.1,hf.2,(pcCellLimit2_4).trans (by exact_mod_cast hL)⟩
    · have hk : cellOKb D pcBase 2 41 20 10000 pcCellBase2_5=true := by
        rw [show cellOKb D pcBase 2 41 20 10000 pcCellBase2_5=
          cellOKb (pcHead 1) pcBase 2 41 20 10000 pcCellBase2_5 from pcCellTransport o _ _ _ _ _ _]
        exact pcCell2_5
      have hf := cellOKb_facts (by norm_num [D,pcBank,pcHead,bankHead] : 1≤D.Q) (by norm_num [D,pcBank,pcHead,bankHead,qq] : 0≤D.α) hk
      exact ⟨hf.1,hf.2,(pcCellLimit2_5).trans (by exact_mod_cast hL)⟩
  have hf2 : ∀ z∈(pcTmpl2.toK 20 46 bankHead.cF).pieces,PieceBasic z.1 ∧
      CatalanCore.Uniform.Content.BankShared.KTerm.PieceCov D (3/10) c310_pos Fr.const depth (NodeFamily.polynomial Fr (altGeom (3/10) c310_pos).geometry) N 2 z.1 := by
    intro z hz
    change z∈expPer 20 46 bankHead.cF 41 0 pcCells2++pcHead2 at hz
    rcases List.mem_append.mp hz with hz | hz
    · obtain ⟨n,hn,y,hy,rfl⟩ := mem_expPer hz
      obtain ⟨⟨hbasic,hR,hΩ⟩,hbase,hRlim⟩ := hcells2 y hy
      have hn' : (n:ℚ)≤41 := by exact_mod_cast hn
      exact ⟨trPiece_basic hbasic 20 46 D.cF y.2.R n,
        exp_cov_per_large hpar hd' (by norm_num [D,pcBank,pcHead,bankHead,qq])
          (d1xTranslation 20 3 10000) (by intro n;simpa only [pcBase,d1xTranslation,List.map_cons,List.map_nil,KCatValid] using hd1x)
          hbasic hbase hRlim n (by linarith)⟩
    · exact hhead2 z hz
  have hall : ∀ x∈D.tmpls,∀ z∈x.2.pieces,PieceBasic z.1 ∧
      CatalanCore.Uniform.Content.BankShared.KTerm.PieceCov D (3/10) c310_pos Fr.const depth (NodeFamily.polynomial Fr (altGeom (3/10) c310_pos).geometry) N x.1 z.1 := by
    intro x hx
    change x∈[(1,pcTmpl1.toK 20 46 bankHead.cF), (2,pcTmpl2.toK 20 46 bankHead.cF)] at hx
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl
    · exact hf1
    · exact hf2
  exact hasScaledContent_of_facts D hpar hClasses hHeads (3/10) c310_pos
    (by norm_num [D,pcBank,pcHead,bankHead,qq]) Fr.const depth
    (NodeFamily.polynomial Fr (altGeom (3/10) c310_pos).geometry)
    (AltQ.ofFrame (3/10) c310_pos (by norm_num) Fr hcF) B N
    (fun x hx z hz => (hall x hx z hz).1) (fun x hx z hz => (hall x hx z hz).2) hcat hPre

theorem thirdsAc_content_autoUF (depth : ℕ) (hd : depth≤64) :
    HasScaledContent (AltEven (3/10) c310_pos thirdsAc depth) (altGeom (3/10) c310_pos).scale (bankData.Λ:ℝ) := by
  apply pc_content_o 2 depth (max (NFr (1/thirdsAc.norm) (-1/thirdsAc.norm) 3 7) 23) thirdsBudget hd cFr_thirdsAc_le (thirds_catValidUF thirdsAc_data depth) (thirds_preValid thirdsAc_data depth)
  · intro ν j0 j1
    exact catValid_pre (3/10) c310_pos (ThirdsData.twoTerm thirdsAc_data) (nm:=9) (by rw [thirdsAc_data.norm_eq];norm_num) depth 5 (max (NFr (1/thirdsAc.norm) (-1/thirdsAc.norm) 3 7) 23) (by norm_num) (fun p hp h => ⟨not_dvd_sq_of_lt (q:=3) hp (by norm_num) (by omega),by omega,by omega⟩) ν j0 j1
  · intro ν hν
    exact WrapPrefixCheck.catValid_prefix_full (3/10) c310_pos (ThirdsData.twoTerm thirdsAc_data) (nm:=9) (by rw [thirdsAc_data.norm_eq];norm_num) depth 5 (max (NFr (1/thirdsAc.norm) (-1/thirdsAc.norm) 3 7) 23) ν hν (fun p hp h => ⟨not_dvd_sq_of_lt (q:=3) hp (by norm_num) (by omega),by omega⟩)
  · exact pcParams2
  · exact pcClasses2
  · intro x hx
    change x∈[(1,pcTmpl1.toK 20 46 bankHead.cF), (2,pcTmpl2.toK 20 46 bankHead.cF)] at hx
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl
    · exact pcTemplate1Head2
    · exact pcTemplate2Head2
#print axioms thirdsAc_content_autoUF
theorem thirdsBc_content_autoUF (depth : ℕ) (hd : depth≤64) :
    HasScaledContent (AltEven (3/10) c310_pos thirdsBc depth) (altGeom (3/10) c310_pos).scale (bankData.Λ:ℝ) := by
  apply pc_content_o 1 depth (max (NFr (1/thirdsBc.norm) (-1/thirdsBc.norm) 3 7) 23) thirdsBudget hd cFr_thirdsBc_le (thirds_catValidUF thirdsBc_data depth) (thirds_preValid thirdsBc_data depth)
  · intro ν j0 j1
    exact catValid_pre (3/10) c310_pos (ThirdsData.twoTerm thirdsBc_data) (nm:=9) (by rw [thirdsBc_data.norm_eq];norm_num) depth 5 (max (NFr (1/thirdsBc.norm) (-1/thirdsBc.norm) 3 7) 23) (by norm_num) (fun p hp h => ⟨not_dvd_sq_of_lt (q:=3) hp (by norm_num) (by omega),by omega,by omega⟩) ν j0 j1
  · intro ν hν
    exact WrapPrefixCheck.catValid_prefix_full (3/10) c310_pos (ThirdsData.twoTerm thirdsBc_data) (nm:=9) (by rw [thirdsBc_data.norm_eq];norm_num) depth 5 (max (NFr (1/thirdsBc.norm) (-1/thirdsBc.norm) 3 7) 23) ν hν (fun p hp h => ⟨not_dvd_sq_of_lt (q:=3) hp (by norm_num) (by omega),by omega⟩)
  · exact pcParams1
  · exact pcClasses1
  · intro x hx
    change x∈[(1,pcTmpl1.toK 20 46 bankHead.cF), (2,pcTmpl2.toK 20 46 bankHead.cF)] at hx
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl
    · exact pcTemplate1Head1
    · exact pcTemplate2Head1
#print axioms thirdsBc_content_autoUF
end CatalanCore.Uniform.Bank.ThirdsContent.Level3Auto
#print axioms CatalanCore.Uniform.Bank.ThirdsContent.Level3Auto.pc_content_o
