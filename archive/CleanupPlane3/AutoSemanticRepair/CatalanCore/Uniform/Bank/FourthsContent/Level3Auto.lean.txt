module
public import CatalanCore.Uniform.Content.BankShared.Check.Normalise
public import CatalanCore.Uniform.Content.BankShared.TwoTerm.Trop
public import CatalanFrames.Lambda.HybInst
public import CatalanFrames.LambdaMirrorHybrid.MirFinal
public import CatalanFrames.LambdaMirrorHybrid.MirTrop
public import CatalanCore.Uniform.Bank.Fourths.Geom
public import CatalanCore.Uniform.Bank.Fourths.TwoTerm
public import CatalanCore.Uniform.Bank.Fourths.Frame
public import CatalanCore.Arith.Hybrid.PieceTools
public import CatalanCore.Uniform.Bank.FourthsContent.Level3Data
public import CatalanCore.Uniform.Bank.FourthsContent.Level3Data.Head
public import CatalanCore.Uniform.Content.BankShared.Check.Prefix
public import CatalanCore.Uniform.Content.UFSimple.PrefixBranches
public import CatalanCore.Uniform.Content.UFSimple.WrapCheck
public import CatalanCore.Uniform.Content.BankShared.KTerm.CatalogueOrbit.Sound
public import CatalanCore.Uniform.Content.UFSimple.WrapPrefixCheck
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 3200000
namespace CatalanCore.Uniform.Bank.FourthsContent.Level3Auto
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.BankShared
  CatalanCore.Uniform.Content.BankShared.Check CatalanCore.Uniform.Content.BankShared.TwoTerm
  CatalanCore.Uniform.Content.SmallPrimes CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanFrames.HybCommon
  CatalanFrames.HybGen CatalanCore.Uniform.Bank.Fourths CatalanCore.Uniform.Content.RankProducer
  CatalanCore.Uniform.Content.Smith
open CatalanFrames.Lambda (lamFrame lamCD lamInst lam_badInfo lam_tropFacts lam_kq_att lam_odd_good)
open CatalanFrames.LambdaMirrorHybrid (mirNFrame mirNInst mirBad mirN_tropFacts mir_kq_att mir_Mn_neg)

/-! ### Frame facts -/


open CatalanCore.Uniform.Content.BankShared.KTerm
open CatalanCore.Uniform.Content.UFSimple
theorem lam_twoTerm : TwoTermData lamFrame 4 1 := by
  have T := pipeline_twoTerm 3 (Or.inr rfl)
  exact ⟨T.o_pos, T.o_lt, fun t ht => T.delta_eq t ht, fun t ht => T.dsq_eq t ht⟩

/-- `mirNFrame` has the two-term data of `pipeline true`: `q = 4`, `o = 3`. -/
theorem mirN_twoTerm : TwoTermData mirNFrame 4 3 := by
  have T := pipeline_twoTerm 1 (Or.inl rfl)
  exact ⟨T.o_pos, T.o_lt, fun t ht => T.delta_eq t ht, fun t ht => T.dsq_eq t ht⟩

theorem cFr_lamMinus : cFr (lambdaFrame false) ≤ 36 := by decide +kernel
theorem cFr_lamPlus : cFr (lambdaFrame true) ≤ 36 := by decide +kernel
theorem cFr_mirN : cFr mirNFrame ≤ 36 := by decide +kernel

/-! ### λ− : `lamFrame` -/

/-- The branch catalogue of `bankData` is valid on `lamFrame` (`o = 1`). -/
theorem lamMinus_catValid (depth : ℕ) :
    CatValid (1 / 5) one_fifth_pos lamFrame depth 4 1 28
      (max (NFr (1 / lamFrame.norm) (-1 / lamFrame.norm) 4 10) 44) bankData.cat := by
  rw [bankData_cat]
  apply catValid_append
  · apply catValid_append
    · exact catValid_bankUFwP lamInst (arith_of_bad lam_badInfo).L_eq lam_tropFacts.toLevelFacts (1 / 5) one_fifth_pos
        (by norm_num) lam_twoTerm (nm := 4 * 4) (by show (16 : ℚ) = ((4 * 4 : ℕ) : ℚ); norm_num) depth 28 10 44
        (by norm_num) (by norm_num) (by norm_num) le_rfl
        (fun p hp h => ⟨not_dvd_sq_of_lt hp (by norm_num) (by omega), by omega, by omega,
          not_bad_of_levels lam_tropFacts.toLevelFacts hp (show 5 ≤ p by omega), (show 5 ≤ p by omega),
          by omega⟩)
        (fun p hp h j k hk hj0 hjq _ _ => by
          have hb := (lam_odd_good hp (by omega)).2
          obtain ⟨h1, -⟩ := kq_eq_poleIndex lamCD (fun _ => rfl) (by norm_num) (by norm_num) hp (by omega) hb
            (lam_kq_att p hp.isPrimePow hb)
          have hk' : 4 * k = j * p + (4 - (4 - 1)) := hk
          have h2 := (rootClass_unique hp (by norm_num) (by norm_num) (by omega) hjq hk').2
          show lamCD.kq p = k
          rw [h1, h2])
        bankWins bankPres
    · exact CatalanCore.Uniform.Content.UFSimple.WrapCheck.catValid_wrap (1 / 5) one_fifth_pos lam_twoTerm (nm := 4 * 4) (by show (16 : ℚ) = ((4 * 4 : ℕ) : ℚ); norm_num) depth 28 _ (fun p hp h => ⟨not_dvd_sq_of_lt hp (by norm_num) (by omega), by omega⟩)
  · exact CatalanCore.Uniform.Content.UFSimple.catValid_prefixBranches (1 / 5) one_fifth_pos lam_twoTerm (nm := 4 * 4) (by show (16 : ℚ) = ((4 * 4 : ℕ) : ℚ); norm_num) depth 28 _ 24 (fun p hp h => ⟨not_dvd_sq_of_lt hp (by norm_num) (by omega), by omega⟩)

/-- The prefix bound of `lamFrame` (`pre_gle_any`), for `p ≤ r/1000`, `α0 = 11/5`. -/
theorem lamMinus_preValid (depth : ℕ) :
    PreValid (1 / 5) one_fifth_pos lamFrame depth 4 (SmallBudget.add (SmallBudget.sqrtLog 5 96) SmallBudget.unit)
      (qq 1 1000) (qq 11 5) := by
  intro i hi p _ _ h
  have hp : p.Prime := Fact.out
  have e1 : ((qq 1 1000 : ℚ) : ℝ) = ((1 : ℕ) : ℝ) / ((1000 : ℕ) : ℝ) := by norm_num [qq]
  rw [e1, floor_frac 1 1000 i.1] at h
  have h1000 : 1000 * p ≤ i.1 := by omega
  have hp2 := hp.two_le
  have hr2 : i.1 % 2 = 0 := hi.2
  obtain ⟨hb1, hb2⟩ := altGeom_border_nat (1 / 5) one_fifth_pos 1 5 (by norm_num) (by norm_num) hr2
  have hR : (5 : ℝ) * (2 * ((altGeom (1 / 5) one_fifth_pos).borderSize i.1 : ℝ)) < 1 * i.1 + 5 := by
    exact_mod_cast hb2
  have hbad : p ∈ lamInst.cd.bad → p * p ≤ 5 * i.1 := by
    intro hpb
    have hp3 : p ≤ 3 := lam_badInfo.bad_le p hpb
    have : p * p ≤ 3 * 3 := Nat.mul_le_mul hp3 hp3
    omega
  obtain ⟨n, hn, hle⟩ := pre_gle_any lamInst (arith_of_bad lam_badInfo).L_eq (1 / 5) one_fifth_pos
    (by norm_num) depth i hr2 (by omega) p 5 96 3 36 (11 / 5) (by norm_num) cFr_lamMinus (by norm_num) hbad
    (by omega) (by norm_num; omega) (by omega) (by omega) (by linarith) (by omega)
  refine ⟨n, hn, ?_⟩
  have e2 : ((qq 11 5 : ℚ) : ℝ) = 11 / 5 := by norm_num [qq]
  rw [e2]
  exact hle

theorem mirN_catValid (depth : ℕ) :
    CatValid (1 / 5) one_fifth_pos mirNFrame depth 4 3 28
      (max (NFr (1 / mirNFrame.norm) (-1 / mirNFrame.norm) 4 10) 44) bankData.cat := by
  rw [bankData_cat]
  apply catValid_append
  · apply catValid_append
    · exact catValid_bankUFwP mirNInst (arith_of_bad mirBad).L_eq mirN_tropFacts.toLevelFacts (1 / 5) one_fifth_pos
        (by norm_num) mirN_twoTerm (nm := 4 * 4) (by show (16 : ℚ) = ((4 * 4 : ℕ) : ℚ); norm_num) depth 28 10 44
        (by norm_num) (by norm_num) (by norm_num) le_rfl
        (fun p hp h => ⟨not_dvd_sq_of_lt hp (by norm_num) (by omega), by omega, by omega,
          not_bad_of_levels mirN_tropFacts.toLevelFacts hp (show 5 ≤ p by omega), (show 5 ≤ p by omega),
          by omega⟩)
        (fun p hp h j k hk hj0 hjq _ _ => by
          have hb := (mirN_tropFacts.good p hp (show 5 ≤ p by omega)).2
          obtain ⟨h1, -⟩ := kq_eq_poleIndex mirNInst.cd (fun _ => rfl) (by norm_num) (by norm_num) hp (by omega)
            hb (mir_kq_att p hp.isPrimePow hb)
          have hk' : 4 * k = j * p + (4 - (4 - 3)) := hk
          have h2 := (rootClass_unique hp (by norm_num) (by norm_num) (by omega) hjq hk').2
          rw [h1, h2])
        bankWins bankPres
    · exact CatalanCore.Uniform.Content.UFSimple.WrapCheck.catValid_wrap (1 / 5) one_fifth_pos mirN_twoTerm (nm := 4 * 4) (by show (16 : ℚ) = ((4 * 4 : ℕ) : ℚ); norm_num) depth 28 _ (fun p hp h => ⟨not_dvd_sq_of_lt hp (by norm_num) (by omega), by omega⟩)
  · exact CatalanCore.Uniform.Content.UFSimple.catValid_prefixBranches (1 / 5) one_fifth_pos mirN_twoTerm (nm := 4 * 4) (by show (16 : ℚ) = ((4 * 4 : ℕ) : ℚ); norm_num) depth 28 _ 24 (fun p hp h => ⟨not_dvd_sq_of_lt hp (by norm_num) (by omega), by omega⟩)

/-- The prefix bound of `mirNFrame` (`pre_gle_any`), for `p ≤ r/1000`, `α0 = 11/5`. -/
theorem mirN_preValid (depth : ℕ) :
    PreValid (1 / 5) one_fifth_pos mirNFrame depth 4 (SmallBudget.add (SmallBudget.sqrtLog 5 96) SmallBudget.unit)
      (qq 1 1000) (qq 11 5) := by
  intro i hi p _ _ h
  have hp : p.Prime := Fact.out
  have e1 : ((qq 1 1000 : ℚ) : ℝ) = ((1 : ℕ) : ℝ) / ((1000 : ℕ) : ℝ) := by norm_num [qq]
  rw [e1, floor_frac 1 1000 i.1] at h
  have h1000 : 1000 * p ≤ i.1 := by omega
  have hp2 := hp.two_le
  have hr2 : i.1 % 2 = 0 := hi.2
  obtain ⟨hb1, hb2⟩ := altGeom_border_nat (1 / 5) one_fifth_pos 1 5 (by norm_num) (by norm_num) hr2
  have hR : (5 : ℝ) * (2 * ((altGeom (1 / 5) one_fifth_pos).borderSize i.1 : ℝ)) < 1 * i.1 + 5 := by
    exact_mod_cast hb2
  have hbad : p ∈ mirNInst.cd.bad → p * p ≤ 5 * i.1 := by
    intro hpb
    have hp3 : p ≤ 3 := mirBad.bad_le p hpb
    have : p * p ≤ 3 * 3 := Nat.mul_le_mul hp3 hp3
    omega
  obtain ⟨n, hn, hle⟩ := pre_gle_any mirNInst (arith_of_bad mirBad).L_eq (1 / 5) one_fifth_pos
    (by norm_num) depth i hr2 (by omega) p 5 96 3 36 (11 / 5) (by norm_num) cFr_mirN (by norm_num) hbad
    (by omega) (by norm_num; omega) (by omega) (by omega) (by linarith) (by omega)
  refine ⟨n, hn, ?_⟩
  have e2 : ((qq 11 5 : ℚ) : ℝ) = 11 / 5 := by norm_num [qq]
  rw [e2]
  exact hle


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
    (hOld : CatValid (1/5) one_fifth_pos Fr depth 4 o bankHead.Pbad Nold bankData.cat)
    (hPre : PreValid (1/5) one_fifth_pos Fr depth bankHead.M B bankHead.t0 bankHead.α0b)
    (hAllPre : ∀ ν j0 j1,CatValid (1/5) one_fifth_pos Fr depth 4 o bankHead.Pbad Nold [brPre ν j0 j1])
    (hAllWrap : ∀ ν,1≤ν → CatValid (1/5) one_fifth_pos Fr depth 4 o bankHead.Pbad Nold [WrapPrefixCheck.brPrefix ν])
    (hParams : kcheckParams (pcBank o)=true) (hClasses : kclassOK (pcBank o)=true)
    (hHeads : ∀ x∈(pcBank o).tmpls,ktmplHead (pcBank o) x.1 x.2=true) :
    HasScaledContent (AltEven (1/5) one_fifth_pos Fr depth) (altGeom (1/5) one_fifth_pos).scale (bankData.Λ:ℝ) := by
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
  have hcat : KCatValid (1/5) one_fifth_pos Fr depth D.shifts D.Q D.Pbad N D.kcat :=
    (legacy_kcat_valid (1/5) one_fifth_pos Fr.const depth
      (NodeFamily.polynomial Fr (altGeom (1/5) one_fifth_pos).geometry) 4 o bankHead.Pbad Nold bankHead.cat hOld hD6).mono_threshold hNold
  have hlegacy : KCatValid (1/5) one_fifth_pos Fr depth D.shifts D.Q D.Pbad N pcLegacyCatalogue := by
    intro br hb
    exact hcat br (List.mem_append.mpr (Or.inl hb))
  have hd1x : KCatValid (1/5) one_fifth_pos Fr depth D.shifts D.Q D.Pbad N [kbD1xB] :=
    (legacy_d1x_valid (1/5) one_fifth_pos Fr.const depth
      (NodeFamily.polynomial Fr (altGeom (1/5) one_fifth_pos).geometry) 4 o bankHead.Pbad Nold bankHead.cat hOld hD1x).mono_threshold hNold
  have hpre (ν j0 j1 : ℕ) : KCatValid (1/5) one_fifth_pos Fr depth D.shifts D.Q D.Pbad N [(brPre ν j0 j1).liftK 0] := by
    have h := (hAllPre ν j0 j1).liftK (1/5) one_fifth_pos Fr.const depth
      (NodeFamily.polynomial Fr (altGeom (1/5) one_fifth_pos).geometry) 4 o bankHead.Pbad Nold [brPre ν j0 j1]
      (legacyShifts 4 o) 0 4 (by decide) rfl rfl le_rfl
    exact (show KCatValid (1/5) one_fifth_pos Fr depth D.shifts D.Q D.Pbad Nold [(brPre ν j0 j1).liftK 0] by
      simpa only [List.map_cons,List.map_nil] using h).mono_threshold hNold
  have hwrap (ν : ℕ) (hν : 1≤ν) : KCatValid (1/5) one_fifth_pos Fr depth D.shifts D.Q D.Pbad N [(WrapPrefixCheck.brPrefix ν).liftK 0] := by
    have h := (hAllWrap ν hν).liftK (1/5) one_fifth_pos Fr.const depth
      (NodeFamily.polynomial Fr (altGeom (1/5) one_fifth_pos).geometry) 4 o bankHead.Pbad Nold [WrapPrefixCheck.brPrefix ν]
      (legacyShifts 4 o) 0 4 (by decide) rfl rfl le_rfl
    exact (show KCatValid (1/5) one_fifth_pos Fr depth D.shifts D.Q D.Pbad Nold [(WrapPrefixCheck.brPrefix ν).liftK 0] by
      simpa only [List.map_cons,List.map_nil] using h).mono_threshold hNold
  have hallowed (S : CatalogueSeed pcLegacyCatalogue) :
      S.law.Allowed (KCatValidFam (1/5) one_fifth_pos Fr.const depth
        (NodeFamily.polynomial Fr (altGeom (1/5) one_fifth_pos).geometry) D.shifts D.Q D.Pbad N) 0 := by
    cases h:S.law with
    | constant indices => simpa only [h,CatalogueOrbitLaw.Allowed] using hlegacy
    | d1x => simpa only [h,CatalogueOrbitLaw.Allowed] using hd1x
    | pre ν j0 j1 => simpa only [h,CatalogueOrbitLaw.Allowed] using (fun ν' => hpre ν' j0 j1)
    | wrap ν hν => simpa only [h,CatalogueOrbitLaw.Allowed] using hwrap
  have hab (S : CatalogueSeed pcLegacyCatalogue) : D.α*S.law.shiftB 10=S.law.shiftA 1 := by
    cases S.law <;> norm_num [CatalogueOrbitLaw.shiftB,CatalogueOrbitLaw.shiftA,D,pcBank,pcHead,bankHead,qq]
  have hhead1 : ∀ z∈pcHead1,PieceBasic z.1 ∧
      PieceCov D (1/5) one_fifth_pos Fr.const depth (NodeFamily.polynomial Fr (altGeom (1/5) one_fifth_pos).geometry) N 1 z.1 := by
    rw [pcHead1_eq]
    apply catalogueHead_facts hpar hd' hL pcRawSeeds1 10 1 10000 0
    · intro S hS;exact hab S
    · intro S hS;exact hallowed S
    · intro S hS
      rw [show seedOK D (S.law.palette 0) 1 pcSeedLimit (S.toSeed 10 1 10000)=
        seedOK (pcHead 1) (S.law.palette 0) 1 pcSeedLimit (S.toSeed 10 1 10000) from pcSeedTransport o _ _ _ _]
      exact pcRawSeeds1_ok S hS
  have hcells1 : ∀ y∈pcCells1,
      (PieceBasic y.1 ∧ 0≤y.2.R ∧ 1/y.1.s+(125:ℚ)*10≤10000) ∧
      BaseSound D (pcBase.map (KBranch.compile D.tS (D.bS 1) D.cS)) 1 y.1 y.2.R ∧ y.2.R*y.1.t≤(N:ℚ) := by
    intro y hy
    simp only [pcCells1,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · have hk : cellOKb D pcBase 1 125 10 10000 pcCellBase1_0=true := by
        rw [show cellOKb D pcBase 1 125 10 10000 pcCellBase1_0=
          cellOKb (pcHead 1) pcBase 1 125 10 10000 pcCellBase1_0 from pcCellTransport o _ _ _ _ _ _]
        exact pcCell1_0
      have hf := cellOKb_facts (by decide : 1≤D.Q) (by norm_num [D,pcBank,pcHead,bankHead,qq] : 0≤D.α) hk
      exact ⟨hf.1,hf.2,(pcCellLimit1_0).trans (by exact_mod_cast hL)⟩
    · have hk : cellOKb D pcBase 1 125 10 10000 pcCellBase1_1=true := by
        rw [show cellOKb D pcBase 1 125 10 10000 pcCellBase1_1=
          cellOKb (pcHead 1) pcBase 1 125 10 10000 pcCellBase1_1 from pcCellTransport o _ _ _ _ _ _]
        exact pcCell1_1
      have hf := cellOKb_facts (by decide : 1≤D.Q) (by norm_num [D,pcBank,pcHead,bankHead,qq] : 0≤D.α) hk
      exact ⟨hf.1,hf.2,(pcCellLimit1_1).trans (by exact_mod_cast hL)⟩
  have hf1 : ∀ z∈(pcTmpl1.toK 10 22 bankHead.cF).pieces,PieceBasic z.1 ∧
      PieceCov D (1/5) one_fifth_pos Fr.const depth (NodeFamily.polynomial Fr (altGeom (1/5) one_fifth_pos).geometry) N 1 z.1 := by
    intro z hz
    change z∈expPer 10 22 bankHead.cF 125 0 pcCells1++pcHead1 at hz
    rcases List.mem_append.mp hz with hz | hz
    · obtain ⟨n,hn,y,hy,rfl⟩ := mem_expPer hz
      obtain ⟨⟨hbasic,hR,hΩ⟩,hbase,hRlim⟩ := hcells1 y hy
      have hn' : (n:ℚ)≤125 := by exact_mod_cast hn
      exact ⟨trPiece_basic hbasic 10 22 D.cF y.2.R n,
        exp_cov_per_large hpar hd' (by norm_num [D,pcBank,pcHead,bankHead,qq])
          (d1xTranslation 10 1 10000) (by intro n;simpa only [pcBase,d1xTranslation,List.map_cons,List.map_nil] using hd1x)
          hbasic hbase hRlim n (by linarith)⟩
    · exact hhead1 z hz
  have hhead3 : ∀ z∈pcHead3,PieceBasic z.1 ∧
      PieceCov D (1/5) one_fifth_pos Fr.const depth (NodeFamily.polynomial Fr (altGeom (1/5) one_fifth_pos).geometry) N 3 z.1 := by
    rw [pcHead3_eq]
    apply catalogueHead_facts hpar hd' hL pcRawSeeds3 10 1 10000 0
    · intro S hS;exact hab S
    · intro S hS;exact hallowed S
    · intro S hS
      rw [show seedOK D (S.law.palette 0) 3 pcSeedLimit (S.toSeed 10 1 10000)=
        seedOK (pcHead 1) (S.law.palette 0) 3 pcSeedLimit (S.toSeed 10 1 10000) from pcSeedTransport o _ _ _ _]
      exact pcRawSeeds3_ok S hS
  have hcells3 : ∀ y∈pcCells3,
      (PieceBasic y.1 ∧ 0≤y.2.R ∧ 1/y.1.s+(125:ℚ)*10≤10000) ∧
      BaseSound D (pcBase.map (KBranch.compile D.tS (D.bS 3) D.cS)) 3 y.1 y.2.R ∧ y.2.R*y.1.t≤(N:ℚ) := by
    intro y hy
    simp only [pcCells3,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · have hk : cellOKb D pcBase 3 125 10 10000 pcCellBase3_0=true := by
        rw [show cellOKb D pcBase 3 125 10 10000 pcCellBase3_0=
          cellOKb (pcHead 1) pcBase 3 125 10 10000 pcCellBase3_0 from pcCellTransport o _ _ _ _ _ _]
        exact pcCell3_0
      have hf := cellOKb_facts (by decide : 1≤D.Q) (by norm_num [D,pcBank,pcHead,bankHead,qq] : 0≤D.α) hk
      exact ⟨hf.1,hf.2,(pcCellLimit3_0).trans (by exact_mod_cast hL)⟩
    · have hk : cellOKb D pcBase 3 125 10 10000 pcCellBase3_1=true := by
        rw [show cellOKb D pcBase 3 125 10 10000 pcCellBase3_1=
          cellOKb (pcHead 1) pcBase 3 125 10 10000 pcCellBase3_1 from pcCellTransport o _ _ _ _ _ _]
        exact pcCell3_1
      have hf := cellOKb_facts (by decide : 1≤D.Q) (by norm_num [D,pcBank,pcHead,bankHead,qq] : 0≤D.α) hk
      exact ⟨hf.1,hf.2,(pcCellLimit3_1).trans (by exact_mod_cast hL)⟩
  have hf3 : ∀ z∈(pcTmpl3.toK 10 22 bankHead.cF).pieces,PieceBasic z.1 ∧
      PieceCov D (1/5) one_fifth_pos Fr.const depth (NodeFamily.polynomial Fr (altGeom (1/5) one_fifth_pos).geometry) N 3 z.1 := by
    intro z hz
    change z∈expPer 10 22 bankHead.cF 125 0 pcCells3++pcHead3 at hz
    rcases List.mem_append.mp hz with hz | hz
    · obtain ⟨n,hn,y,hy,rfl⟩ := mem_expPer hz
      obtain ⟨⟨hbasic,hR,hΩ⟩,hbase,hRlim⟩ := hcells3 y hy
      have hn' : (n:ℚ)≤125 := by exact_mod_cast hn
      exact ⟨trPiece_basic hbasic 10 22 D.cF y.2.R n,
        exp_cov_per_large hpar hd' (by norm_num [D,pcBank,pcHead,bankHead,qq])
          (d1xTranslation 10 1 10000) (by intro n;simpa only [pcBase,d1xTranslation,List.map_cons,List.map_nil] using hd1x)
          hbasic hbase hRlim n (by linarith)⟩
    · exact hhead3 z hz
  have hall : ∀ x∈D.tmpls,∀ z∈x.2.pieces,PieceBasic z.1 ∧
      PieceCov D (1/5) one_fifth_pos Fr.const depth (NodeFamily.polynomial Fr (altGeom (1/5) one_fifth_pos).geometry) N x.1 z.1 := by
    intro x hx
    change x∈[(1,pcTmpl1.toK 10 22 bankHead.cF), (3,pcTmpl3.toK 10 22 bankHead.cF)] at hx
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl
    · exact hf1
    · exact hf3
  exact hasScaledContent_of_facts D hpar hClasses hHeads (1/5) one_fifth_pos
    (by norm_num [D,pcBank,pcHead,bankHead,qq]) Fr.const depth
    (NodeFamily.polynomial Fr (altGeom (1/5) one_fifth_pos).geometry)
    (AltQ.ofFrame (1/5) one_fifth_pos (by norm_num) Fr hcF) B N
    (fun x hx z hz => (hall x hx z hz).1) (fun x hx z hz => (hall x hx z hz).2) hcat hPre

theorem lamMinus_content_auto (depth : ℕ) (hd : depth≤64) :
    HasScaledContent (AltEven (1/5) one_fifth_pos (lambdaFrame false) depth) (altGeom (1/5) one_fifth_pos).scale (bankData.Λ:ℝ) := by
  apply pc_content_o 1 depth (max (NFr (1/lamFrame.norm) (-1/lamFrame.norm) 4 10) 44) (SmallBudget.add (SmallBudget.sqrtLog 5 96) SmallBudget.unit) hd cFr_lamMinus (lamMinus_catValid depth) (lamMinus_preValid depth)
  · intro ν j0 j1
    exact catValid_pre (1/5) one_fifth_pos lam_twoTerm (nm:=16) (by rfl) depth 28 (max (NFr (1/lamFrame.norm) (-1/lamFrame.norm) 4 10) 44) (by norm_num) (fun p hp h => ⟨not_dvd_sq_of_lt hp (by norm_num) (by omega),by omega,by omega⟩) ν j0 j1
  · intro ν hν
    exact WrapPrefixCheck.catValid_prefix_full (1/5) one_fifth_pos lam_twoTerm (nm:=16) (by rfl) depth 28 (max (NFr (1/lamFrame.norm) (-1/lamFrame.norm) 4 10) 44) ν hν (fun p hp h => ⟨not_dvd_sq_of_lt hp (by norm_num) (by omega),by omega⟩)
  · exact pcParams1
  · exact pcClasses1
  · intro x hx
    change x∈[(1,pcTmpl1.toK 10 22 bankHead.cF), (3,pcTmpl3.toK 10 22 bankHead.cF)] at hx
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl
    · exact pcTemplate1Head1
    · exact pcTemplate3Head1
#print axioms lamMinus_content_auto
theorem lamPlus_content_auto (depth : ℕ) (hd : depth≤64) :
    HasScaledContent (AltEven (1/5) one_fifth_pos (lambdaFrame true) depth) (altGeom (1/5) one_fifth_pos).scale (bankData.Λ:ℝ) := by
  apply pc_content_o 3 depth (max (NFr (1/mirNFrame.norm) (-1/mirNFrame.norm) 4 10) 44) (SmallBudget.add (SmallBudget.sqrtLog 5 96) SmallBudget.unit) hd cFr_lamPlus (catValid_neg (Fr:=lambdaFrame true) mir_Mn_neg (mirN_catValid depth)) (preValid_neg (Fr:=lambdaFrame true) mir_Mn_neg (mirN_preValid depth))
  · intro ν j0 j1
    exact catValid_neg (Fr:=lambdaFrame true) mir_Mn_neg (catValid_pre (1/5) one_fifth_pos mirN_twoTerm (nm:=16) (by rfl) depth 28 (max (NFr (1/mirNFrame.norm) (-1/mirNFrame.norm) 4 10) 44) (by norm_num) (fun p hp h => ⟨not_dvd_sq_of_lt hp (by norm_num) (by omega),by omega,by omega⟩) ν j0 j1)
  · intro ν hν
    exact catValid_neg (Fr:=lambdaFrame true) mir_Mn_neg (WrapPrefixCheck.catValid_prefix_full (1/5) one_fifth_pos mirN_twoTerm (nm:=16) (by rfl) depth 28 (max (NFr (1/mirNFrame.norm) (-1/mirNFrame.norm) 4 10) 44) ν hν (fun p hp h => ⟨not_dvd_sq_of_lt hp (by norm_num) (by omega),by omega⟩))
  · exact pcParams3
  · exact pcClasses3
  · intro x hx
    change x∈[(1,pcTmpl1.toK 10 22 bankHead.cF), (3,pcTmpl3.toK 10 22 bankHead.cF)] at hx
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl
    · exact pcTemplate1Head3
    · exact pcTemplate3Head3
#print axioms lamPlus_content_auto
end CatalanCore.Uniform.Bank.FourthsContent.Level3Auto
#print axioms CatalanCore.Uniform.Bank.FourthsContent.Level3Auto.pc_content_o
