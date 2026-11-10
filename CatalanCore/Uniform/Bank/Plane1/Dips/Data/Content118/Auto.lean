module
public import CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118.AutoP
public import CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118.AutoM
public import CatalanCore.Uniform.Bank.Plane1.Dips.Rows
public import CatalanCore.Uniform.Bank.Plane1.Dips.KnownZero.Catalogue
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 3200000
namespace CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape
open CatalanCore.Uniform.Content.BankShared CatalanCore.Uniform.Content.BankShared.KTerm
open CatalanCore.Uniform.Content.BankShared.Check CatalanCore.Uniform.Content.BankShared.TwoTerm
open CatalanCore.Uniform.Content.SmallPrimes CatalanCore.Uniform.Bank.Plane1
open CatalanCore.Uniform.Bank.Plane1.Dips CatalanFrames.P6
open CatalanCore.Arith.Hybrid
theorem quarter_pos : (0:ℚ)<1/4 := by norm_num
theorem quarter_le_one : (1/4:ℚ)≤1 := by norm_num
noncomputable def dipBudget : SmallBudget := SmallBudget.add (SmallBudget.sqrtLog 5 10) SmallBudget.unit

theorem quarter_preValid (σ : Support) (a b c : ℤ) (h0 : a+b+c=0) (depth : ℕ) :
    PreValid (1/4) quarter_pos (planeFrame σ a b c h0) depth 6 dipBudget (1/68) (9/4) := by
  intro i hi p hpf hpM h
  have hp : p.Prime := Fact.out
  have e1 : (((1/68:ℚ)):ℝ)=(1:ℝ)/68 := by norm_num
  rw [e1] at h
  have hfloor (r : ℕ) : ⌊((1 : ℝ) / 68) * (r : ℝ)⌋₊ = r / 68 := by
    simpa only [Nat.cast_one, Nat.cast_ofNat, one_mul] using (floor_frac 1 68 r)
  have hdiv : p ≤ i.1 / 68 := h.trans_eq (hfloor i.1)
  have h68 : 68 * p ≤ i.1 := by omega
  have h5 : 5 ≤ p := by
    have h2 : p≠2 := fun he => hpM (by rw [he];norm_num)
    have h3 : p≠3 := fun he => hpM (by rw [he];norm_num)
    have h4 : p≠4 := fun he => by rw [he] at hp;norm_num at hp
    have := hp.two_le
    omega
  have hr2 : i.1%2=0 := hi.2
  obtain ⟨hb1,hb2⟩ := altGeom_border_nat (1/4) quarter_pos 1 4 (by norm_num) (by norm_num) hr2
  have hb : 8*(altGeom (1/4) quarter_pos).borderSize i.1 < i.1+4 := by omega
  have hR : (8:ℝ)*((altGeom (1/4) quarter_pos).borderSize i.1:ℝ)<(i.1:ℝ)+4 := by exact_mod_cast hb
  obtain ⟨n,hn,hle⟩ := (planeBundle σ a b c h0).pre_gle
    (1/4) quarter_pos depth i hr2 (by omega) p h5 5 10 3 (9/4)
    (by omega) (by norm_num;omega) (by omega) (by omega) (by linarith) (by omega)
  refine ⟨n,hn,?_⟩
  have e2 : (((9/4:ℚ)):ℝ)=(9:ℝ)/4 := by norm_num
  rw [e2]
  exact hle

theorem quarter_nv0_even (σ : Support) (a b c : ℤ) (h0 : a+b+c=0)
    (ha : a≠0) (hb : b≠0) (hc : c≠0) :
    ∃ R0 : ℕ, ∀ s : ℕ, R0≤s → ∀ x : ℚ, ∃ n,
      (((altGeom (1/4) quarter_pos).family (planeFrame σ a b c h0) 64).restrictAdm (fun i=>i.1%2=0)).Adm n ∧
      (altGeom (1/4) quarter_pos).scale n=2*s ∧
      (((altGeom (1/4) quarter_pos).family (planeFrame σ a b c h0) 64).restrictAdm (fun i=>i.1%2=0)).evalQ n x≠0 := by
  let G : BlockGeom := altGeom (1/4) quarter_pos
  have hEq : G.selectionDepth (planeFrame σ a b c h0) 2=planeDepth := rfl
  have hdepth : G.selectionDepth (planeFrame σ a b c h0) 2≤64 := hEq.le.trans planeDepth_le
  obtain ⟨R0,hR⟩ := G.hasNV0 (planeFrame σ a b c h0) 2 64
    (by norm_num) (by show 1≤3;norm_num) (plane_w_ne ha hb hc)
    (fun i=>by simp [G,altGeom,single,commonB])
    (fun i=>by simp [G,altGeom,single,rowB])
    (fun i=>by simp [G,altGeom,single,colB]) hdepth
  refine ⟨R0,fun s hs x=>?_⟩
  obtain ⟨n,hn,hsc,hne⟩ := hR (2*s) (by omega) x
  exact ⟨n,⟨hn,by
    show n.1%2=0
    have hscale : G.scale n=n.1 := rfl
    omega⟩,hsc,hne⟩

theorem head_valid (σ : Support) :
    KCatValid (1/4) quarter_pos (planeFrame σ 4 (-3) (-1) (by norm_num)) 64
      (planeBundle σ 4 (-3) (-1) (by norm_num)).shifts 6 6 0 headCat := by
  intro br hbr
  simp only [headCat,List.mem_append,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false,or_assoc] at hbr
  rcases hbr with hbr | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact plane_trop_valid σ 4 (-3) (-1) (by norm_num) (1/4) quarter_pos quarter_le_one 64 6 6 0 (by norm_num) (by norm_num) br hbr
  · exact plane_knownZero_catalogue (1/4) quarter_pos σ 4 (-3) (-1) (by norm_num) 64 6 6 0 (by norm_num) (by norm_num) false (by simp) _ (by simp)
  · exact plane_knownZero_catalogue (1/4) quarter_pos σ 4 (-3) (-1) (by norm_num) 64 6 6 0 (by norm_num) (by norm_num) true (by norm_num) _ (by simp)
  · exact (planeBundle σ 4 (-3) (-1) (by norm_num)).prefix_valid (1/4) quarter_pos 64 6 6 0 0 0 0 0 (by norm_num) (by norm_num) _ (by simp)
  · exact (planeBundle σ 4 (-3) (-1) (by norm_num)).prefix_valid (1/4) quarter_pos 64 6 6 0 0 0 0 1 (by norm_num) (by norm_num) _ (by simp)
  · exact (planeBundle σ 4 (-3) (-1) (by norm_num)).prefix_valid (1/4) quarter_pos 64 6 6 0 0 0 0 2 (by norm_num) (by norm_num) _ (by simp)
  · exact (planeBundle σ 4 (-3) (-1) (by norm_num)).prefix_valid (1/4) quarter_pos 64 6 6 0 0 0 1 0 (by norm_num) (by norm_num) _ (by simp)
  · exact (planeBundle σ 4 (-3) (-1) (by norm_num)).prefix_valid (1/4) quarter_pos 64 6 6 0 0 0 1 1 (by norm_num) (by norm_num) _ (by simp)
  · exact (planeBundle σ 4 (-3) (-1) (by norm_num)).prefix_valid (1/4) quarter_pos 64 6 6 0 0 0 1 2 (by norm_num) (by norm_num) _ (by simp)
  · exact (planeBundle σ 4 (-3) (-1) (by norm_num)).prefix_valid (1/4) quarter_pos 64 6 6 0 0 0 2 0 (by norm_num) (by norm_num) _ (by simp)
  · exact (planeBundle σ 4 (-3) (-1) (by norm_num)).prefix_valid (1/4) quarter_pos 64 6 6 0 0 0 2 1 (by norm_num) (by norm_num) _ (by simp)
  · exact (planeBundle σ 4 (-3) (-1) (by norm_num)).prefix_valid (1/4) quarter_pos 64 6 6 0 0 0 2 2 (by norm_num) (by norm_num) _ (by simp)
  · exact (planeBundle σ 4 (-3) (-1) (by norm_num)).prefix_valid (1/4) quarter_pos 64 6 6 0 0 1 0 0 (by norm_num) (by norm_num) _ (by simp)
  · exact (planeBundle σ 4 (-3) (-1) (by norm_num)).prefix_valid (1/4) quarter_pos 64 6 6 0 0 1 0 1 (by norm_num) (by norm_num) _ (by simp)
  · exact (planeBundle σ 4 (-3) (-1) (by norm_num)).prefix_valid (1/4) quarter_pos 64 6 6 0 0 1 0 2 (by norm_num) (by norm_num) _ (by simp)
  · exact (planeBundle σ 4 (-3) (-1) (by norm_num)).prefix_valid (1/4) quarter_pos 64 6 6 0 0 1 1 0 (by norm_num) (by norm_num) _ (by simp)
  · exact (planeBundle σ 4 (-3) (-1) (by norm_num)).prefix_valid (1/4) quarter_pos 64 6 6 0 0 1 1 1 (by norm_num) (by norm_num) _ (by simp)
  · exact (planeBundle σ 4 (-3) (-1) (by norm_num)).prefix_valid (1/4) quarter_pos 64 6 6 0 0 1 1 2 (by norm_num) (by norm_num) _ (by simp)
  · exact (planeBundle σ 4 (-3) (-1) (by norm_num)).prefix_valid (1/4) quarter_pos 64 6 6 0 0 1 2 0 (by norm_num) (by norm_num) _ (by simp)
  · exact (planeBundle σ 4 (-3) (-1) (by norm_num)).prefix_valid (1/4) quarter_pos 64 6 6 0 0 1 2 1 (by norm_num) (by norm_num) _ (by simp)
  · exact (planeBundle σ 4 (-3) (-1) (by norm_num)).prefix_valid (1/4) quarter_pos 64 6 6 0 0 1 2 2 (by norm_num) (by norm_num) _ (by simp)
theorem bankP_ok : DipBankOK (1/4) quarter_pos 64 Support.plus 4 (-3) (-1) (by norm_num) bankP dipBudget 0 where
  check := bankP_check
  alpha := by change (1/4:ℚ)=2*(1/8);norm_num
  hdepth := le_rfl
  control := AltQ.ofFrame (1/4) quarter_pos quarter_le_one (planeFrame Support.plus 4 (-3) (-1) (by norm_num)) (cFr_plane Support.plus 4 (-3) (-1) (by norm_num))
  cat := head_valid Support.plus
  «prefix» := fun n j0 j1 j2 => (planeBundle Support.plus 4 (-3) (-1) (by norm_num)).prefix_valid (1/4) quarter_pos 64 6 6 0 n j0 j1 j2 (by norm_num) (by norm_num)
  d1x := plane_cat_valid Support.plus 4 (-3) (-1) (by norm_num) (1/4) quarter_pos quarter_le_one 64 6 6 0 (by norm_num) (by norm_num) [kbD1x] (by
    intro br hbr
    rw [List.mem_singleton] at hbr
    subst br
    exact Or.inl (by simp [planeTrop]))
  pre := quarter_preValid Support.plus 4 (-3) (-1) (by norm_num) 64
#print axioms bankP_ok
theorem bankM_ok : DipBankOK (1/4) quarter_pos 64 Support.minus 4 (-3) (-1) (by norm_num) bankM dipBudget 0 where
  check := bankM_check
  alpha := by change (1/4:ℚ)=2*(1/8);norm_num
  hdepth := le_rfl
  control := AltQ.ofFrame (1/4) quarter_pos quarter_le_one (planeFrame Support.minus 4 (-3) (-1) (by norm_num)) (cFr_plane Support.minus 4 (-3) (-1) (by norm_num))
  cat := head_valid Support.minus
  «prefix» := fun n j0 j1 j2 => (planeBundle Support.minus 4 (-3) (-1) (by norm_num)).prefix_valid (1/4) quarter_pos 64 6 6 0 n j0 j1 j2 (by norm_num) (by norm_num)
  d1x := plane_cat_valid Support.minus 4 (-3) (-1) (by norm_num) (1/4) quarter_pos quarter_le_one 64 6 6 0 (by norm_num) (by norm_num) [kbD1x] (by
    intro br hbr
    rw [List.mem_singleton] at hbr
    subst br
    exact Or.inl (by simp [planeTrop]))
  pre := quarter_preValid Support.minus 4 (-3) (-1) (by norm_num) 64
#print axioms bankM_ok
end CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118
#print axioms CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118.quarter_preValid
#print axioms CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118.quarter_nv0_even
