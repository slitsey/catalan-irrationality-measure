import CatalanCore.Uniform.Content.BankShared.Check.Content
import CatalanCore.Uniform.Content.BankShared.TwoTerm.LP
import CatalanCore.Uniform.Content.BankShared.TwoTerm.M3D
import CatalanCore.Uniform.Content.BankShared.TwoTerm.Trop
set_option Elab.async false

/-! # The branch catalogue from the generic two-term layer lemmas (lane C1L; C4's `BankShared.TwoTerm`)

`CatValid` (the hypothesis of Theorem D) for the generic catalogue, from the branch theorems of lane C4:

* `catValid_tableT`: table T (`T_gle_D1`, `D1x`, `D2`, `D3`, `D45`, `D6`) for any hybrid instance `I` of the frame
  with arithmetic and level data, when every prime `p > P_bad` is good and its tropical pole index is the root
  datum `k`;
* `catValid_LP`: LP1, LP2 (`lp1_gle_tt`, `lp2_gle_tt`);
* `catValid_win`: every M3D window `brWin n0 n1` (`m3_gap_tt`; the window is cut-free by construction);
* `catValid_twoTerm`: the catalogue `tableT ++ ([brLP1, brLP2, brRank] ++ windows)`, given the rank branch
  (lane C2L) as the one remaining hypothesis. -/

namespace CatalanCore.Uniform.Content.BankShared.Check
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.BankShared
  CatalanCore.Uniform.Content.Member CatalanCore.Arith.Hybrid CatalanCore.Arith.Hybrid.ChainClasses
  CatalanCore.Uniform.Content.Smith CatalanCore.Basic CatalanCore.Arith CatalanFrames.HybCommon
  CatalanFrames.HybGen TwoTerm Cat

/-! ### The conditions in ℕ form -/

section Holds
variable {r p m k : ℕ}

theorem holds_Pler (h : cPler.Holds r p m k) : p ≤ r := by
  simp only [cPler, Cond.Holds, Cond.L, Bool.false_eq_true, ite_false] at h; push_cast at h; omega
theorem holds_Rltp (h : cRltp.Holds r p m k) : r < p := by
  simp only [cRltp, Cond.Holds, Cond.L, ite_true] at h; push_cast at h; omega
theorem holds_2mltp (h : c2mltp.Holds r p m k) : 2 * m < p := by
  simp only [c2mltp, Cond.Holds, Cond.L, ite_true] at h; push_cast at h; omega
theorem holds_Kler (h : cKler.Holds r p m k) : k ≤ r := by
  simp only [cKler, Cond.Holds, Cond.L, Bool.false_eq_true, ite_false] at h; push_cast at h; omega
theorem holds_Rlek (h : cRlek.Holds r p m k) : r ≤ k := by
  simp only [cRlek, Cond.Holds, Cond.L, Bool.false_eq_true, ite_false] at h; push_cast at h; omega
theorem holds_Nlep (h : cNlep.Holds r p m k) : r + 2 * m ≤ p := by
  simp only [cNlep, Cond.Holds, Cond.L, Bool.false_eq_true, ite_false] at h; push_cast at h; omega
theorem holds_Nle2p (h : cNle2p.Holds r p m k) : r + 2 * m ≤ 2 * p := by
  simp only [cNle2p, Cond.Holds, Cond.L, Bool.false_eq_true, ite_false] at h; push_cast at h; omega
theorem holds_Rltpk (h : cRltpk.Holds r p m k) : r < p + k := by
  simp only [cRltpk, Cond.Holds, Cond.L, ite_true] at h; push_cast at h; omega
theorem holds_Nlepk (h : cNlepk.Holds r p m k) : r + 2 * m ≤ p + k := by
  simp only [cNlepk, Cond.Holds, Cond.L, Bool.false_eq_true, ite_false] at h; push_cast at h; omega
theorem holds_Pltrm (h : cPltrm.Holds r p m k) : p < r + m := by
  simp only [cPltrm, Cond.Holds, Cond.L, ite_true] at h; push_cast at h; omega
theorem holds_Mltp (h : cMltp.Holds r p m k) : m < p := by
  simp only [cMltp, Cond.Holds, Cond.L, ite_true] at h; push_cast at h; omega

end Holds

theorem catValid_append {c : ℚ} {hc : 0 < c} {Fr : Frame} {depth q o Pbad N0 : ℕ} {l₁ l₂ : List Branch}
    (h₁ : CatValid c hc Fr depth q o Pbad N0 l₁) (h₂ : CatValid c hc Fr depth q o Pbad N0 l₂) :
    CatValid c hc Fr depth q o Pbad N0 (l₁ ++ l₂) := by
  intro b hb
  rcases List.mem_append.1 hb with hb | hb
  · exact h₁ b hb
  · exact h₂ b hb

/-! ### LP1 and LP2 -/

theorem catValid_LP (c : ℚ) (hc : 0 < c) {Fr : Frame} {q o : ℕ} (T : TwoTermData Fr q o) {nm : ℕ}
    (hnorm : Fr.norm = (nm : ℚ)) (depth Pbad N0 : ℕ)
    (hP : ∀ p : ℕ, p.Prime → Pbad < p → ¬ p ∣ nm ∧ 5 ≤ p ∧ 2 * q ≤ p) :
    CatValid c hc Fr depth q o Pbad N0 [brLP1, brLP2] := by
  intro b hb i hi hr0 p _ hPb _ hqN j k hk hj0 hjq hk0 hkp hcond
  obtain ⟨hpn, hp5, hpq⟩ := hP p Fact.out hPb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · have h1 := holds_Nle2p (hcond cNle2p (by simp [brLP1]))
    have h2 := holds_Pler (hcond cPler (by simp [brLP1]))
    have h3 := holds_Rltpk (hcond cRltpk (by simp [brLP1]))
    have hg := lp1_gle_tt c hc T hnorm depth i hi.1 hi.2 p k j hpn hp5 hpq hk hk0 hkp hj0 h1 h2 h3
    exact ⟨_, hg, by simp only [brLP1, one_mul]; exact le_refl _⟩
  · have h1 := holds_Rltp (hcond cRltp (by simp [brLP2]))
    have h2 := holds_Kler (hcond cKler (by simp [brLP2]))
    have h3 := holds_Nlepk (hcond cNlepk (by simp [brLP2]))
    have h4 := holds_Pltrm (hcond cPltrm (by simp [brLP2]))
    have hg := lp2_gle_tt c hc T hnorm depth i hi.1 hi.2 p k j hpn hp5 hpq hk hk0 hkp hj0 h3 h1 h2 h4
    exact ⟨_, hg, by simp only [brLP2, one_mul]; exact le_refl _⟩

/-! ### The M3D windows -/

/-- An integer strictly between consecutive members of `x + p ℤ` is not in `x + p ℤ`. -/
theorem not_between {p x n t : ℤ} (hp : 0 < p) (h1 : x + n * p < t) (h2 : t < x + (n + 1) * p)
    (s : ℤ) (hs : t = x + s * p) : False := by
  rw [hs] at h1 h2
  have u : n * p < s * p := by linarith
  have v : s * p < (n + 1) * p := by linarith
  have u' : n < s := lt_of_mul_lt_mul_right u hp.le
  have v' : s < n + 1 := lt_of_mul_lt_mul_right v hp.le
  omega

theorem catValid_win (c : ℚ) (hc : 0 < c) {Fr : Frame} {q o : ℕ} (T : TwoTermData Fr q o) {nm : ℕ}
    (hnorm : Fr.norm = (nm : ℚ)) (depth Pbad N0 : ℕ) (hq : 0 < q)
    (hP : ∀ p : ℕ, p.Prime → Pbad < p → ¬ p ∣ nm ∧ q < p) (n0 n1 : ℕ) :
    CatValid c hc Fr depth q o Pbad N0 [brWin n0 n1] := by
  intro b hb i hi hr0 p _ hPb _ hqN j k hk hj0 hjq hk0 hkp hcond
  obtain ⟨hpn, hqp⟩ := hP p Fact.out hPb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  subst hb
  have hmp := holds_Mltp (hcond cMltp (by simp [brWin]))
  set r := i.1 with hrdef
  set m := (altGeom c hc).borderSize i.1 with hmdef
  set a := (winLo n0 n1).evalN r p m k with ha
  set bb := (winHi n0 n1).evalN r p m k with hbdef
  have hev : (tWin n0 n1).evalN r p m k = 2 * r + (2 * m - (bb - a)) := rfl
  have hp0 : 0 < p := by omega
  have hlo : r + 2 * m - p ≤ a ∧ r ≤ a ∧ n0 * p ≤ a ∧ (n1 ≠ 0 → k + (n1 - 1) * p ≤ a) := by
    by_cases hn1 : n1 = 0
    · have e : a = max (max (r + 2 * m - p) r) (max (n0 * p) r) := by
        rw [ha]; simp only [winLo, if_pos hn1]; rfl
      rw [e]
      exact ⟨(le_max_left _ _).trans (le_max_left _ _), (le_max_right _ _).trans (le_max_left _ _),
        (le_max_left _ _).trans (le_max_right _ _), fun h => absurd hn1 h⟩
    · have e : a = max (max (r + 2 * m - p) r) (max (n0 * p) (k + (n1 - 1) * p)) := by
        rw [ha]; simp only [winLo, if_neg hn1]; rfl
      rw [e]
      exact ⟨(le_max_left _ _).trans (le_max_left _ _), (le_max_right _ _).trans (le_max_left _ _),
        (le_max_left _ _).trans (le_max_right _ _), fun _ => (le_max_right _ _).trans (le_max_right _ _)⟩
  have hhi : bb ≤ r + 2 * m ∧ bb ≤ r + p ∧ bb ≤ (n0 + 1) * p ∧ bb ≤ k + n1 * p := by
    have e : bb = min (min (r + 2 * m) (r + p)) (min ((n0 + 1) * p) (k + n1 * p)) := by
      rw [hbdef]; rfl
    rw [e]
    exact ⟨(min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
      (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
  by_cases hab : a ≤ bb
  · refine ⟨_, m3_gap_tt c hc T hnorm depth i hi.1 hi.2 p hpn hqN a bb hlo.2.1 hlo.1 hab hhi.1 hhi.2.1 ?_,
      by simp only [brWin, hev, zero_mul, add_zero]; exact le_refl _⟩
    intro t h1 h2 hcut
    have hpz : (0 : ℤ) < p := by exact_mod_cast hp0
    have hn0a : ((n0 * p : ℕ) : ℤ) ≤ a := by exact_mod_cast hlo.2.2.1
    have hn0b : (bb : ℤ) ≤ ((n0 + 1) * p : ℕ) := by exact_mod_cast hhi.2.2.1
    have hra : (r : ℤ) ≤ a := by exact_mod_cast hlo.2.1
    have hrb : (bb : ℤ) ≤ ((r + p : ℕ) : ℤ) := by exact_mod_cast hhi.2.1
    have hkb : (bb : ℤ) ≤ ((k + n1 * p : ℕ) : ℤ) := by exact_mod_cast hhi.2.2.2
    push_cast at hn0a hn0b hrb hkb
    unfold Cut ttSing at hcut
    rcases hcut with (⟨s, hs⟩ | hdk) | ⟨s, hs⟩ | ⟨s, hs⟩
    · exact not_between (x := 0) (n := n0) (t := t) hpz (by linarith) (by linarith) s (by rw [hs]; ring)
    · -- `p ∣ q t - o` forces `t ≡ k (mod p)`
      have hkz : (q : ℤ) * k = j * p + o := by exact_mod_cast hk
      have hdiv : (p : ℤ) ∣ (q : ℤ) * (t - k) := by
        have : (q : ℤ) * (t - k) = ((q : ℤ) * t - o) - j * p := by linarith
        rw [this]; exact dvd_sub hdk (dvd_mul_left _ _)
      have hcop : IsCoprime (p : ℤ) (q : ℤ) :=
        Nat.isCoprime_iff_coprime.2 (coprime_of_lt (Fact.out : p.Prime) hq hqp)
      obtain ⟨s, hs⟩ := hcop.dvd_of_dvd_mul_left hdiv
      have hts : t = k + s * p := by linarith
      by_cases hn1 : n1 = 0
      · -- below the first pole cut: `t < k` and `t > a ≥ 0`
        have hkp' : (k : ℤ) < p := by exact_mod_cast hkp
        have ht0 : (0 : ℤ) < t := by have : (0 : ℤ) ≤ r := Nat.cast_nonneg r; linarith
        have htk : t < k := by rw [hn1] at hkb; push_cast at hkb; linarith
        exact not_between (x := k) (n := -1) (t := t) hpz (by linarith) (by linarith) s hts
      · have hka : (((k + (n1 - 1) * p : ℕ)) : ℤ) ≤ a := by exact_mod_cast hlo.2.2.2 hn1
        have hn1' : ((n1 - 1 : ℕ) : ℤ) = (n1 : ℤ) - 1 := by
          rw [Nat.cast_sub (by omega)]; rfl
        push_cast [hn1'] at hka
        exact not_between (x := k) (n := (n1 : ℤ) - 1) (t := t) hpz (by linarith) (by linarith) s hts
    · exact not_between (x := 0) (n := n0) (t := t) hpz (by linarith) (by linarith) s (by rw [hs]; ring)
    · exact not_between (x := r) (n := 0) (t := t) hpz (by linarith) (by linarith) s hs
  · -- an empty window: the price `2 r + 2 m`
    have hab' : bb < a := lt_of_not_ge hab
    set a' := max (r + 2 * m - p) r
    refine ⟨_, m3_gap_tt c hc T hnorm depth i hi.1 hi.2 p hpn hqN a' a' (le_max_right _ _)
      (le_max_left _ _) le_rfl (max_le (by omega) (by omega)) (max_le (by omega) (by omega))
      (fun t h1 h2 => absurd (lt_trans h1 h2) (lt_irrefl _)), ?_⟩
    simp only [brWin, hev, zero_mul, add_zero, Nat.sub_self]
    omega

/-! ### Table T -/

theorem catValid_tableT {Fr : Frame} (I : HybInst Fr) [∀ r m, I.DiagOK r m] {Lc : ℕ}
    (hL : I.cd.L = Lc) {Gd : ℕ → Prop} (Lv : LevelFacts I Gd (fun q c => c < I.cd.kq q))
    (c : ℚ) (hc : 0 < c) (hc1 : c ≤ 1) (depth q o Pbad N0 : ℕ) (hLq : Lc ≤ q)
    (hP : ∀ p : ℕ, p.Prime → Pbad < p → p ∉ I.cd.bad ∧ Gd p ∧ p ≠ 2)
    (hkq : ∀ p : ℕ, p.Prime → Pbad < p → ∀ j k : ℕ, q * k = j * p + o → 0 < j → j < q → 0 < k →
      k < p → I.cd.kq p = k) :
    CatValid c hc Fr depth q o Pbad N0 tableT := by
  intro b hb i hi hr0 p _ hPb _ hqN j k hk hj0 hjq hk0 hkp hcond
  obtain ⟨hnb, hG, hp2⟩ := hP p Fact.out hPb
  have hkq' := hkq p Fact.out hPb j k hk hj0 hjq hk0 hkp
  have hsq : Lc * (i.1 + 2 * (altGeom c hc).borderSize i.1) < p * p :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ hLq) hqN
  have hr1 : 1 ≤ i.1 := hr0
  have hr := hi.2
  have hmr : 2 * (altGeom c hc).borderSize i.1 ≤ i.1 := by
    obtain ⟨-, h2⟩ := altGeom_border c hc hr
    have h3 : (2 * ((altGeom c hc).borderSize i.1 : ℚ)) < i.1 + 1 := by
      have : c * (i.1 : ℚ) ≤ i.1 := by
        have := Nat.cast_nonneg (α := ℚ) i.1; nlinarith
      linarith
    have : 2 * (altGeom c hc).borderSize i.1 < i.1 + 1 := by exact_mod_cast h3
    omega
  simp only [tableT, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, T_gle_D1 I hL c hc depth i hr hr1 p hnb hsq, by simp only [brD1, zero_mul, add_zero]; exact le_refl _⟩
  · exact ⟨_, T_gle_D1x I hL c hc depth i hr hr1 p hnb hsq hp2,
      by simp only [brD1x, zero_mul, add_zero]; exact le_refl _⟩
  · have h1 := holds_2mltp (hcond c2mltp (by simp [brD2]))
    have h2 := holds_Pler (hcond cPler (by simp [brD2]))
    have h3 := holds_Kler (hcond cKler (by simp [brD2]))
    have hg := T_gle_D2 I hL c hc depth i hr hr1 p hnb hsq Lv hG h1 h2 (by rw [hkq']; exact h3)
    rw [hkq'] at hg
    exact ⟨_, hg, by simp only [brD2, zero_mul, add_zero]; exact le_refl _⟩
  · have h1 := holds_2mltp (hcond c2mltp (by simp [brD3]))
    have h2 := holds_Pler (hcond cPler (by simp [brD3]))
    exact ⟨_, T_gle_D3 I hL c hc depth i hr hr1 p hnb hsq Lv h1 h2,
      by simp only [brD3, zero_mul, add_zero]; exact le_refl _⟩
  · have h1 := holds_Rltp (hcond cRltp (by simp [brD45]))
    have hg := T_gle_D45 I hL c hc depth i hr hr1 p hnb hsq Lv hG h1 hmr
    rw [hkq'] at hg
    exact ⟨_, hg, by simp only [brD45, zero_mul, add_zero]; exact le_refl _⟩
  · have h1 := holds_Nlep (hcond cNlep (by simp [brD6]))
    have h2 := holds_Rlek (hcond cRlek (by simp [brD6]))
    have hg := T_gle_D6 I hL c hc depth i hr hr1 p hnb hsq Lv hG h1 (by rw [hkq']; exact h2)
    rw [hkq'] at hg
    exact ⟨_, hg, by simp only [brD6, zero_mul, add_zero]; exact le_refl _⟩

/-! ### The two-term catalogue -/

/-- **The catalogue of a two-term bank**: table T, LP1, LP2, the rank branch and any M3D windows, given the rank
branch (lane C2L) as the one remaining hypothesis. -/
theorem catValid_twoTerm {Fr : Frame} (I : HybInst Fr) [∀ r m, I.DiagOK r m] {Lc : ℕ}
    (hL : I.cd.L = Lc) {Gd : ℕ → Prop} (Lv : LevelFacts I Gd (fun q c => c < I.cd.kq q))
    (c : ℚ) (hc : 0 < c) (hc1 : c ≤ 1) {q o : ℕ} (T : TwoTermData Fr q o) {nm : ℕ}
    (hnorm : Fr.norm = (nm : ℚ)) (depth Pbad N0 : ℕ) (hq : 0 < q) (hLq : Lc ≤ q)
    (hP : ∀ p : ℕ, p.Prime → Pbad < p →
      ¬ p ∣ nm ∧ 5 ≤ p ∧ 2 * q ≤ p ∧ p ∉ I.cd.bad ∧ Gd p ∧ p ≠ 2)
    (hkq : ∀ p : ℕ, p.Prime → Pbad < p → ∀ j k : ℕ, q * k = j * p + o → 0 < j → j < q → 0 < k →
      k < p → I.cd.kq p = k)
    (hrank : CatValid c hc Fr depth q o Pbad N0 [brRank]) (wins : List (ℕ × ℕ)) :
    CatValid c hc Fr depth q o Pbad N0
      (tableT ++ ([brLP1, brLP2, brRank] ++ wins.map (fun w => brWin w.1 w.2))) := by
  refine catValid_append (catValid_tableT I hL Lv c hc hc1 depth q o Pbad N0 hLq
    (fun p hp h => ⟨(hP p hp h).2.2.2.1, (hP p hp h).2.2.2.2.1, (hP p hp h).2.2.2.2.2⟩) hkq) ?_
  have hLP := catValid_LP c hc T hnorm depth Pbad N0 (fun p hp h => ⟨(hP p hp h).1, (hP p hp h).2.1,
    (hP p hp h).2.2.1⟩)
  have hW : CatValid c hc Fr depth q o Pbad N0 (wins.map (fun w => brWin w.1 w.2)) := by
    intro b hb
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hb
    exact catValid_win c hc T hnorm depth Pbad N0 hq
      (fun p hp h => ⟨(hP p hp h).1, by have := (hP p hp h).2.2.1; omega⟩) w.1 w.2 _ (by simp)
  intro b hb
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with (rfl | rfl | rfl) | hb
  · exact hLP _ (by simp)
  · exact hLP _ (by simp)
  · exact hrank _ (by simp)
  · exact hW b hb

end CatalanCore.Uniform.Content.BankShared.Check
