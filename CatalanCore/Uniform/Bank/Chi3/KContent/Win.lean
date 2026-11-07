module

public import CatalanCore.Uniform.Bank.Chi3.KContent.Trop
public import CatalanCore.Uniform.Content.BankShared.KTerm.Pre
public import CatalanCore.Uniform.Content.BankShared.KTerm.Prefix
public import CatalanCore.Uniform.Content.BankShared.Check.Layers
public import CatalanCore.Uniform.Content.BankShared.TwoTerm.Prefix
public import CatalanCore.Uniform.Bank.Chi3Content.M3

@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 1600000

/-! # The M3D windows and the prefix branches of chi_{-3} on the k-shift route (lane K)

* `lat_gap`, `KBundle.cutfree`, `KBundle.pre_gap`, `KBundle.prefix_valid` are generic (`KTerm.Win`, `KTerm.Pre`);
* `kbrWin_valid`: the window branch `kbrWin [n₀, n₁, n₂]` (`m3_gle_minor`);
* `kbrPre_valid`: the prefix branch `kbrPre n j₀ [j₁, j₂]` (`prefix_gle` through `preLayer`). -/

namespace CatalanCore.Uniform.Bank.Chi3.KContent
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.BankShared
  CatalanCore.Uniform.Content.BankShared.TwoTerm CatalanCore.Uniform.Content.BankShared.TwoTerm.Pre
  CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check
  CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanCore.Arith.Hybrid.ChainClasses CatalanCore.Rect
  CatalanFrames.HybCommon CatalanFrames.HybGen CatalanFrames.P6 CatalanFrames.P6Hybrid
  CatalanCore.Uniform.Bank.Chi3Content

/-- **The M3D window branch of chi_{-3}.** -/
theorem kbrWin_valid (depth N0 n0 n1 n2 : ℕ) :
    KCatValid (1 / 2) c12_pos p6Frame depth kShifts 6 6 N0 [kbrWin [n0, n1, n2]] := by
  intro b hb i hi hr0 p _ hPb _ hqN kv hroots hcond
  simp only [List.mem_singleton] at hb
  subst hb
  have hr := hi.2
  have h7 : 7 ≤ p := by omega
  set r := i.1 with hrdef
  set m := (altGeom (1 / 2) c12_pos).borderSize r with hmdef
  have hp2 := odd_of_ge_seven (Fact.out : p.Prime) h7
  obtain ⟨⟨jA, eA, -, -, -, hkAp⟩, ⟨jB, eB, -, -, -, hkBp⟩⟩ := chi3Bundle.roots_facts hroots
  have hsq : 3 * (r + 2 * m) < p * p := by omega
  have hG : GLE p (tropVal (HW (p6Inst r m).lev p r m)) ((AltEven (1 / 2) c12_pos p6Frame depth).Q i) :=
    chi3Bundle.gle_trop (1 / 2) c12_pos depth i hr hr0 p (by omega) hsq
  have hlo := kMx_ge r p m kv (.vr :: kWinLos 0 [n0, n1, n2]) (.tsub kN .vp)
  have hhi := kMn_le r p m kv (.add .vr .vp :: kWinHis 0 [n0, n1, n2]) kN
  obtain ⟨hlo1, hlo2⟩ := hlo
  obtain ⟨hhi1, hhi2⟩ := hhi
  have hev : (kbrWin [n0, n1, n2]).τ.evalN r p m kv =
      2 * r + (2 * m - ((kWinHi [n0, n1, n2]).evalN r p m kv - (kWinLo [n0, n1, n2]).evalN r p m kv)) := rfl
  have hd0 : (kbrWin [n0, n1, n2]).debit = 0 := rfl
  generalize haa : (kWinLo [n0, n1, n2]).evalN r p m kv = aa at hev
  generalize hbb : (kWinHi [n0, n1, n2]).evalN r p m kv = bb at hev
  have hlN : r + 2 * m - p ≤ aa := by rw [← haa]; exact hlo1
  have hlr : r ≤ aa := by rw [← haa]; exact hlo2 .vr (by simp)
  have hhN : bb ≤ r + 2 * m := by rw [← hbb]; exact hhi1
  have hhp : bb ≤ r + p := by rw [← hbb]; exact hhi2 (.add .vr .vp) (by simp)
  have hh0 : bb ≤ n0 * p := by rw [← hbb]; exact hhi2 (kLatPt 0 n0) (by simp [kWinHis])
  have hh1 : bb ≤ kv 0 + n1 * p := by rw [← hbb]; exact hhi2 (kLatPt 1 n1) (by simp [kWinHis])
  have hh2 : bb ≤ kv 1 + n2 * p := by rw [← hbb]; exact hhi2 (kLatPt 2 n2) (by simp [kWinHis])
  have hl0 : 1 ≤ n0 → (n0 - 1) * p ≤ aa := fun h => by
    rw [← haa]; exact hlo2 (kLatPt 0 (n0 - 1)) (by simp [kWinLos, h])
  have hl1 : 1 ≤ n1 → kv 0 + (n1 - 1) * p ≤ aa := fun h => by
    rw [← haa]; exact hlo2 (kLatPt 1 (n1 - 1)) (by simp [kWinLos, h])
  have hl2 : 1 ≤ n2 → kv 1 + (n2 - 1) * p ≤ aa := fun h => by
    rw [← haa]; exact hlo2 (kLatPt 2 (n2 - 1)) (by simp [kWinLos, h])
  by_cases hab : aa ≤ bb
  swap
  · refine ⟨_, hG.mono (XGm_D1 _ _ _ _), ?_⟩
    rw [hev, hd0]
    simp only [zero_mul, add_zero]
    omega
  have hmp : m < p := by
    have := hcond ⟨0, 1, -1, List.replicate 2 0, 0, true⟩ (by simp [kbrWin])
    simp only [KCond.Holds, KCond.L, List.replicate, dot] at this
    norm_num at this
    omega
  have hcutf := chi3Bundle.cutfree (A' := 0) (n0 := n0) (n1 := n1) (n2 := n2) (a := aa) (b := bb) (Fact.out : p.Prime)
    (by omega) (by omega) ⟨jA, eA⟩ hkAp ⟨jB, eB⟩ hkBp (by simpa using hl0) (by simpa using hh0)
    (by simpa using hl1) (by simpa using hh1) (by simpa using hl2) (by simpa using hh2)
  have hM : M3Hyp r m p aa bb :=
    { prime := Fact.out
      p5 := by omega
      hN := hsq
      hra := hlr
      hab := hab
      hb := hhN
      hbp := hhp
      hj := max_le hab (by omega)
      hcut := by
        intro x y hx1 hx2 hy1 hy2 t ht1 ht2 hcut
        have ha : (aa : ℤ) < t := by
          have : (aa : ℤ) ≤ min (x : ℤ) y := le_min (by exact_mod_cast hx1) (by exact_mod_cast hy1)
          omega
        have hb' : t < bb := by
          have hx : (x : ℤ) < bb := by exact_mod_cast hx2
          have hy : (y : ℤ) < bb := by exact_mod_cast hy2
          have : max (x : ℤ) y ≤ (bb : ℤ) - 1 := max_le (by omega) (by omega)
          omega
        rcases hcut with hs | ⟨j, hj⟩ | ⟨j, hj⟩
        · exact hcutf t ha hb' hs
        · exact hcutf t ha hb' (Or.inl ⟨j, by rw [hj]; ring⟩)
        · have hpz : (0 : ℤ) < p := by exact_mod_cast (by omega : 0 < p)
          have c1 : (r : ℤ) ≤ aa := by exact_mod_cast hlr
          have c2 : (bb : ℤ) ≤ r + p := by exact_mod_cast hhp
          exact not_between (x := r) (n := 0) (t := t) hpz (by linarith) (by linarith) j hj }
  have hg := chi3Bundle.gle_m3 (1 / 2) c12_pos depth (n := m3price r m p aa bb) i hr p (fun s => m3_gle_minor hM s)
  refine ⟨_, hg, ?_⟩
  rw [hev, hd0]
  simp only [zero_mul, add_zero, m3price]
  have : max aa (r + 2 * m - p) = aa := max_eq_left hlN
  rw [this]

/-- **The prefix branch of chi_{-3}** (Theorem 1 of the prefix rule): the generic `KBundle.prefix_valid`. -/
theorem kbrPre_valid (depth N0 n j0 j1 j2 : ℕ) :
    KCatValid (1 / 2) c12_pos p6Frame depth kShifts 6 6 N0 [kbrPre n j0 [j1, j2]] :=
  chi3Bundle.prefix_valid (1 / 2) c12_pos depth 6 6 N0 n j0 j1 j2 (by norm_num) (by norm_num)

end CatalanCore.Uniform.Bank.Chi3.KContent
