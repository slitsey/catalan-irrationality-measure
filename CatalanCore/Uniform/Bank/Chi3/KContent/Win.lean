import CatalanCore.Uniform.Bank.Chi3.KContent.Trop
import CatalanCore.Uniform.Content.BankShared.KTerm.Prefix
import CatalanCore.Uniform.Content.BankShared.Check.Layers
import CatalanCore.Uniform.Content.BankShared.TwoTerm.Prefix
import CatalanCore.Uniform.Bank.Chi3Content.M3
set_option Elab.async false
set_option maxHeartbeats 1600000

/-! # The M3D windows and the prefix branches of chi_{-3} on the k-shift route (lane K)

* `lat_gap`: an integer strictly between consecutive points of `A + x + p ℤ` (a window inside `[A + x + (n-1) p, A + x + n p]`)
  is not in the lattice;
* `chi3_cutfree`: a window `(a, b)` lying between consecutive points of each of the three lattices `p ℤ`, `k_A + p ℤ`,
  `k_B + p ℤ` (shifted by the multiple `p A'`) contains no singular point `p ∣ t`, `p ∣ 3 t - 2`, `p ∣ 2 t - 1`;
* `kbrWin_valid`: the window branch `kbrWin [n₀, n₁, n₂]` (`m3_gle_minor`);
* `kbrPre_valid`: the prefix branch `kbrPre n j₀ [j₁, j₂]` (`prefix_gle` through `preLayer`). -/

namespace CatalanCore.Uniform.Bank.Chi3.KContent
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.BankShared
  CatalanCore.Uniform.Content.BankShared.TwoTerm CatalanCore.Uniform.Content.BankShared.TwoTerm.Pre
  CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check
  CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanCore.Arith.Hybrid.ChainClasses CatalanCore.Rect
  CatalanFrames.HybCommon CatalanFrames.HybGen CatalanFrames.P6 CatalanFrames.P6Hybrid
  CatalanCore.Uniform.Bank.Chi3Content

/-! ### Cut-freeness of a window -/

theorem lat_gap {p : ℕ} (hp : 0 < p) {x A n a b : ℕ} (hx : x < p) (hA : A ≤ a)
    (hlo : 1 ≤ n → A + x + (n - 1) * p ≤ a) (hhi : b ≤ A + x + n * p) {t : ℤ} (h1 : (a : ℤ) < t)
    (h2 : t < b) (s : ℤ) (hs : t = ((A + x : ℕ) : ℤ) + s * p) : False := by
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp
  have hb : (b : ℤ) ≤ ((A + x : ℕ) : ℤ) + n * p := by exact_mod_cast hhi
  refine not_between (x := ((A + x : ℕ) : ℤ)) (n := (n : ℤ) - 1) (t := t) hpz ?_ ?_ s hs
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hxA : (A : ℤ) ≤ a := by exact_mod_cast hA
      have hxp : (x : ℤ) < p := by exact_mod_cast hx
      push_cast
      linarith
    · have h' : ((A + x + (n - 1) * p : ℕ) : ℤ) ≤ a := by exact_mod_cast hlo hn
      push_cast [Nat.cast_sub hn] at h' ⊢
      linarith
  · have e : ((n : ℤ) - 1 + 1) = n := by ring
    rw [e]
    linarith

theorem dvd_of_dvd_const {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) {c : ℤ} (hc : 0 < c) (hc3 : c ≤ 3) {u : ℤ}
    (h : (p : ℤ) ∣ c * u) : (p : ℤ) ∣ u := by
  have hpr : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  rcases hpr.dvd_or_dvd h with h' | h'
  · exfalso
    have := Int.le_of_dvd hc h'
    omega
  · exact h'

theorem chi3_cutfree {p kA kB A' n0 n1 n2 a b : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hA : p * A' ≤ a)
    (hkA : ∃ j, 3 * kA = j * p + 2) (hkAp : kA < p) (hkB : ∃ j, 2 * kB = j * p + 1) (hkBp : kB < p)
    (hl0 : 1 ≤ n0 → p * A' + 0 + (n0 - 1) * p ≤ a) (hh0 : b ≤ p * A' + 0 + n0 * p)
    (hl1 : 1 ≤ n1 → p * A' + kA + (n1 - 1) * p ≤ a) (hh1 : b ≤ p * A' + kA + n1 * p)
    (hl2 : 1 ≤ n2 → p * A' + kB + (n2 - 1) * p ≤ a) (hh2 : b ≤ p * A' + kB + n2 * p) :
    ∀ t : ℤ, (a : ℤ) < t → t < b → ¬ chi3Sing p t := by
  intro t h1 h2 hs
  have hp0 : 0 < p := hp.pos
  obtain ⟨jA, hjA⟩ := hkA
  obtain ⟨jB, hjB⟩ := hkB
  unfold chi3Sing at hs
  rcases hs with ⟨d, hd⟩ | ⟨d, hd⟩ | ⟨d, hd⟩
  · exact lat_gap hp0 (x := 0) (A := p * A') (n := n0) hp0 hA hl0 hh0 h1 h2 (d - A')
      (by push_cast; rw [hd]; ring)
  · have hjA' : (3 : ℤ) * kA = jA * p + 2 := by exact_mod_cast hjA
    have h3 : (p : ℤ) ∣ 3 * (t - kA) := ⟨d - jA, by linarith⟩
    obtain ⟨e, he⟩ := dvd_of_dvd_const hp h5 (by norm_num) (by norm_num) h3
    exact lat_gap hp0 (x := kA) (A := p * A') (n := n1) hkAp hA hl1 hh1 h1 h2 (e - A')
      (by push_cast; linarith)
  · have hjB' : (2 : ℤ) * kB = jB * p + 1 := by exact_mod_cast hjB
    have h3 : (p : ℤ) ∣ 2 * (t - kB) := ⟨d - jB, by linarith⟩
    obtain ⟨e, he⟩ := dvd_of_dvd_const hp h5 (by norm_num) (by norm_num) h3
    exact lat_gap hp0 (x := kB) (A := p * A') (n := n2) hkBp hA hl2 hh2 h1 h2 (e - A')
      (by push_cast; linarith)

/-! ### The Q-level bridges -/

theorem p6_gle_m3 (c : ℚ) (hc : 0 < c) (depth : ℕ) {n : ℕ} (i : ((altGeom c hc).family p6Frame depth).ι)
    (hr : i.1 % 2 = 0) (p : ℕ) [Fact p.Prime]
    (h : ∀ s : Finset (Fin i.1), GLE p n (commonMinorPoly p6Frame i.1 ((altGeom c hc).borderSize i.1) s)) :
    GLE p n (((altGeom c hc).family p6Frame depth).Q i) := by
  obtain ⟨r, S⟩ := i
  rw [altGeom_member_commonMinor c hc p6Frame depth hr S]
  exact h _

theorem p6_pre_gap (c : ℚ) (hc : 0 < c) (depth : ℕ) (i : ((altGeom c hc).family p6Frame depth).ι)
    (hi : ((altGeom c hc).family p6Frame depth).Adm i) (hr : i.1 % 2 = 0) (p : ℕ) [Fact p.Prime]
    (h5 : 5 ≤ p) (hN : 3 * (i.1 + 2 * (altGeom c hc).borderSize i.1) < p * p) (n a b : ℕ)
    (hW : Win p i.1 ((altGeom c hc).borderSize i.1) n ((altGeom c hc).borderSize i.1 - n * p) a b)
    (hgap : ∀ t : ℤ, (a : ℤ) < t → t < b → ¬ chi3Sing p t) :
    GLE p (2 * i.1 + 2 * (altGeom c hc).borderSize i.1 - (b - a))
      (((altGeom c hc).family p6Frame depth).Q i) := by
  have hk : ((altGeom c hc).geometry i.1).k = (altGeom c hc).borderSize i.1 :=
    geometry_k_eq_borderSize _ i.1
  have hN' : i.1 + 2 * (altGeom c hc).borderSize i.1 < p * p := by omega
  have hv : preValid (altGeom c hc) p6Frame n (fun _ _ => a) (fun _ _ => b) i.1 p := by
    refine ⟨altGeom_hybShape c hc hr, fun [hpf : Fact p.Prime] => ?_⟩
    rw [hk]
    refine ⟨chi3PoleData h5 hN, hN', hW, fun t h1 h2 => ⟨?_, ?_⟩⟩
    · rintro ⟨d, hd⟩
      refine hgap (t : ℤ) (by exact_mod_cast h1) (by exact_mod_cast h2) (Or.inl ⟨(d : ℤ), ?_⟩)
      rw [hd]; push_cast; ring
    · intro hs
      exact hgap (t : ℤ) (by exact_mod_cast h1) (by exact_mod_cast h2) hs
  have hg := (preLayer (altGeom c hc) p6Frame depth n (fun _ _ => a) (fun _ _ => b)).gle i hi p hv
  simp only [preLayer, zero_mul, add_zero, hk] at hg
  exact hg

/-! ### Setup shared by the window and the prefix branch -/

/-- The roots as hypotheses of `chi3_cutfree` and the congruence classes. -/
theorem roots_facts {p : ℕ} {kv : ℕ → ℕ}
    (hroots : ∀ n < kShifts.length, ∃ jn, (shAt kShifts n).q * kv n = jn * p + (shAt kShifts n).o ∧ 0 < jn ∧
      jn < (shAt kShifts n).q ∧ 0 < kv n ∧ kv n < p) :
    (∃ j, 3 * kv 0 = j * p + 2 ∧ 0 < j ∧ j < 3 ∧ 0 < kv 0 ∧ kv 0 < p) ∧
    (∃ j, 2 * kv 1 = j * p + 1 ∧ 0 < j ∧ j < 2 ∧ 0 < kv 1 ∧ kv 1 < p) :=
  ⟨hroots 0 (by decide), hroots 1 (by decide)⟩

theorem p6_prime_facts {p : ℕ} (hp : p.Prime) (h7 : 7 ≤ p) : p % 2 = 1 := by
  by_contra h
  have h2 : 2 ∣ p := by omega
  rcases hp.eq_one_or_self_of_dvd 2 h2 with h | h <;> omega


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
  have hp2 := p6_prime_facts (Fact.out : p.Prime) h7
  obtain ⟨⟨jA, eA, -, -, -, hkAp⟩, ⟨jB, eB, -, -, -, hkBp⟩⟩ := roots_facts hroots
  have hsq : 3 * (r + 2 * m) < p * p := by omega
  have hG : GLE p (tropVal (HW (p6Inst r m).lev p r m)) ((AltEven (1 / 2) c12_pos p6Frame depth).Q i) :=
    p6_gle_trop (1 / 2) c12_pos depth i hr hr0 p (by omega) hsq
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
  have hcutf := chi3_cutfree (A' := 0) (n0 := n0) (n1 := n1) (n2 := n2) (a := aa) (b := bb) (Fact.out : p.Prime)
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
  have hg := p6_gle_m3 (1 / 2) c12_pos depth (n := m3price r m p aa bb) i hr p (fun s => m3_gle_minor hM s)
  refine ⟨_, hg, ?_⟩
  rw [hev, hd0]
  simp only [zero_mul, add_zero, m3price]
  have : max aa (r + 2 * m - p) = aa := max_eq_left hlN
  rw [this]

/-- **The prefix branch of chi_{-3}** (Theorem 1 of the prefix rule). -/
theorem kbrPre_valid (depth N0 n j0 j1 j2 : ℕ) :
    KCatValid (1 / 2) c12_pos p6Frame depth kShifts 6 6 N0 [kbrPre n j0 [j1, j2]] := by
  intro b hb i hi hr0 p _ hPb _ hqN kv hroots hcond
  simp only [List.mem_singleton] at hb
  subst hb
  have hr := hi.2
  have h7 : 7 ≤ p := by omega
  set r := i.1 with hrdef
  set m := (altGeom (1 / 2) c12_pos).borderSize r with hmdef
  have hp2 := p6_prime_facts (Fact.out : p.Prime) h7
  obtain ⟨⟨jA, eA, -, -, -, hkAp⟩, ⟨jB, eB, -, -, -, hkBp⟩⟩ := roots_facts hroots
  have hsq : 3 * (r + 2 * m) < p * p := by omega
  have hG : GLE p (tropVal (HW (p6Inst r m).lev p r m)) ((AltEven (1 / 2) c12_pos p6Frame depth).Q i) :=
    p6_gle_trop (1 / 2) c12_pos depth i hr hr0 p (by omega) hsq
  have hlo := kMx_ge r p m kv (.vr :: .add .ap (.smul j0 .vp) :: kPoleLos 0 [j1, j2]) (.tsub (kNn n) .vp)
  have hhi := kMn_le r p m kv (.add .vr .vp :: .add .ap (.smul (j0 + 1) .vp) :: kPoleHis 0 [j1, j2]) (kNn n)
  obtain ⟨hlo1, hlo2⟩ := hlo
  obtain ⟨hhi1, hhi2⟩ := hhi
  have hev : (kbrPre n j0 [j1, j2]).τ.evalN r p m kv =
      2 * r + (2 * m - ((kPreHi n j0 [j1, j2]).evalN r p m kv - (kPreLo n j0 [j1, j2]).evalN r p m kv)) := rfl
  have hd0 : (kbrPre n j0 [j1, j2]).debit = 0 := rfl
  generalize haa : (kPreLo n j0 [j1, j2]).evalN r p m kv = aa at hev
  generalize hbb : (kPreHi n j0 [j1, j2]).evalN r p m kv = bb at hev
  have hlN : r + 2 * (m - n * p) - p ≤ aa := by rw [← haa]; exact hlo1
  have hlr : r ≤ aa := by rw [← haa]; exact hlo2 .vr (by simp)
  have hl0 : p * (r / p) + j0 * p ≤ aa := by
    rw [← haa]; exact hlo2 (.add .ap (.smul j0 .vp)) (by simp)
  have hl1 : j1 ≠ 0 → p * (r / p) + (kv 0 + (j1 - 1) * p) ≤ aa := fun h => by
    rw [← haa]; exact hlo2 (.add .ap (.add (.vk 0) (.smul (j1 - 1) .vp))) (by simp [kPoleLos, h])
  have hl2 : j2 ≠ 0 → p * (r / p) + (kv 1 + (j2 - 1) * p) ≤ aa := fun h => by
    rw [← haa]; exact hlo2 (.add .ap (.add (.vk 1) (.smul (j2 - 1) .vp))) (by simp [kPoleLos, h])
  have hhN : bb ≤ r + 2 * (m - n * p) := by rw [← hbb]; exact hhi1
  have hhp : bb ≤ r + p := by rw [← hbb]; exact hhi2 (.add .vr .vp) (by simp)
  have hh0 : bb ≤ p * (r / p) + (j0 + 1) * p := by
    rw [← hbb]; exact hhi2 (.add .ap (.smul (j0 + 1) .vp)) (by simp)
  have hh1 : bb ≤ p * (r / p) + (kv 0 + j1 * p) := by
    rw [← hbb]; exact hhi2 (.add .ap (.add (.vk 0) (.smul j1 .vp))) (by simp [kPoleHis])
  have hh2 : bb ≤ p * (r / p) + (kv 1 + j2 * p) := by
    rw [← hbb]; exact hhi2 (.add .ap (.add (.vk 1) (.smul j2 .vp))) (by simp [kPoleHis])
  by_cases hab : aa < bb
  swap
  · refine ⟨_, hG.mono (XGm_D1 _ _ _ _), ?_⟩
    rw [hev, hd0]
    simp only [zero_mul, add_zero]
    omega
  have hnp : n * p ≤ m := by
    by_contra h
    have : m - n * p = 0 := by omega
    omega
  have hApr : p * (r / p) ≤ r := Nat.mul_div_le r p
  have hW : Win p r m n (m - n * p) aa bb := ⟨by omega, hp2, hlr, hab.le, hhp, hhN, by omega⟩
  have hgap := chi3_cutfree (A' := r / p) (n0 := j0 + 1) (n1 := j1) (n2 := j2) (a := aa) (b := bb)
    (Fact.out : p.Prime) (by omega) (by omega) ⟨jA, eA⟩ hkAp ⟨jB, eB⟩ hkBp
    (fun _ => by simpa using hl0) (by simpa using hh0)
    (fun h => by have := hl1 (by omega); omega) (by omega)
    (fun h => by have := hl2 (by omega); omega) (by omega)
  have hgp : GLE p (2 * r + 2 * m - (bb - aa)) ((AltEven (1 / 2) c12_pos p6Frame depth).Q i) :=
    p6_pre_gap (1 / 2) c12_pos depth i hi.1 hr p (by omega) hsq n aa bb hW hgap
  refine ⟨_, hgp, ?_⟩
  rw [hev, hd0]
  simp only [zero_mul, add_zero]
  omega

end CatalanCore.Uniform.Bank.Chi3.KContent
