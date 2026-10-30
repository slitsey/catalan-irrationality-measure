module

public import CatalanCore.Uniform.Content.BankShared.Check.LP2W
public import CatalanCore.Uniform.Content.BankShared.TwoTerm.Prefix

@[expose] public section
set_option Elab.async false

/-! # The prefix branches `brPre n j0 j1` (paper `prefix-rule-2026-10-29`, section 5)

`brPre n j0 j1` is the window bound of Theorem 1 at the strip `n` (border `N_n = r + 2(m - n p)`),
for the window between the multiples `ap + j0 p`, `ap + (j0 + 1) p` (`ap = p ⌊r/p⌋`) and the pole
cuts `ap + k + (j1 - 1) p`, `ap + k + j1 p` (`j1 = 0`: below `ap + k`), intersected with
`[max(r, N_n - p), min(N_n, r + p))`; price `2r + (2m - (hi - lo))`, debit 0, **no conditions**.
It is valid for every `n, j0, j1` (`catValid_pre`; an empty window gives `2r + 2m`).

A bank opts in by data only: it appends `pres.map (fun x => brPre x.1 x.2.1 x.2.2)` to its catalogue
(e.g. `pres` = all `(n, j0, j1)` with `1 ≤ n ≤ nmax`, `j0 < 2`, `j1 < 3`) and cites
`catValid_bankWP` / `catValid_bankUFwP` (the LP2W catalogues followed by the prefix branches) or, for
any other valid catalogue, `catValid_withPre`. -/

namespace CatalanCore.Uniform.Content.BankShared.Check
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.BankShared
  CatalanCore.Uniform.Content.Member CatalanCore.Uniform.Content.RankProducer
  CatalanCore.Uniform.Content.UFSimple CatalanCore.Uniform.Content.Smith CatalanCore.Basic CatalanCore.Arith
  CatalanCore.Arith.Hybrid CatalanCore.Arith.Hybrid.ChainClasses TwoTerm Cat

open Expr

namespace Cat

/-- `N_n = r + 2(m - n p)`. -/
def eNn (n : ℕ) : Expr := add vr (smul 2 (tsub vm (smul n vp)))
/-- The left end of the prefix window. -/
def preLo (n j0 j1 : ℕ) : Expr :=
  mx (mx (tsub (eNn n) vp) vr)
    (mx (add ap (smul j0 vp)) (if j1 = 0 then vr else add ap (add vk (smul (j1 - 1) vp))))
/-- The right end of the prefix window. -/
def preHi (n j0 j1 : ℕ) : Expr :=
  mn (mn (eNn n) (add vr vp)) (mn (add ap (smul (j0 + 1) vp)) (add ap (add vk (smul j1 vp))))
/-- The prefix price `2r + (2m - (hi - lo))`. -/
def tPre (n j0 j1 : ℕ) : Expr := add (smul 2 vr) (tsub (smul 2 vm) (tsub (preHi n j0 j1) (preLo n j0 j1)))

end Cat

/-- **The prefix branch** (no conditions, debit 0). -/
def brPre (n j0 j1 : ℕ) : Branch := ⟨tPre n j0 j1, [], 0⟩

theorem catValid_pre (c : ℚ) (hc : 0 < c) {Fr : Frame} {q o : ℕ} (T : TwoTermData Fr q o) {nm : ℕ}
    (hnorm : Fr.norm = (nm : ℚ)) (depth Pbad N0 : ℕ) (hq : 0 < q)
    (hP : ∀ p : ℕ, p.Prime → Pbad < p → ¬ p ∣ nm ∧ 5 ≤ p ∧ q < p) (n j0 j1 : ℕ) :
    CatValid c hc Fr depth q o Pbad N0 [brPre n j0 j1] := by
  intro br hb i hi hr0 p _ hPb _ hqN j k hk hj0 hjq hk0 hkp _
  obtain ⟨hpn, hp5, hqp⟩ := hP p Fact.out hPb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  subst hb
  have hp0 : 0 < p := by omega
  have hp2 : p % 2 = 1 := Nat.odd_iff.1 ((Fact.out : p.Prime).odd_of_ne_two (by omega))
  set r := i.1 with hrdef
  set m := (altGeom c hc).borderSize i.1 with hmdef
  set aa := (preLo n j0 j1).evalN r p m k with haa
  set bb := (preHi n j0 j1).evalN r p m k with hbb
  have hev : (tPre n j0 j1).evalN r p m k = 2 * r + (2 * m - (bb - aa)) := rfl
  have hlo : r + 2 * (m - n * p) - p ≤ aa ∧ r ≤ aa ∧ p * (r / p) + j0 * p ≤ aa ∧
      (j1 ≠ 0 → p * (r / p) + (k + (j1 - 1) * p) ≤ aa) := by
    by_cases hn1 : j1 = 0
    · have e : aa = max (max (r + 2 * (m - n * p) - p) r) (max (p * (r / p) + j0 * p) r) := by
        rw [haa]; simp only [preLo, if_pos hn1]; rfl
      rw [e]
      exact ⟨(le_max_left _ _).trans (le_max_left _ _), (le_max_right _ _).trans (le_max_left _ _),
        (le_max_left _ _).trans (le_max_right _ _), fun h => absurd hn1 h⟩
    · have e : aa = max (max (r + 2 * (m - n * p) - p) r)
          (max (p * (r / p) + j0 * p) (p * (r / p) + (k + (j1 - 1) * p))) := by
        rw [haa]; simp only [preLo, if_neg hn1]; rfl
      rw [e]
      exact ⟨(le_max_left _ _).trans (le_max_left _ _), (le_max_right _ _).trans (le_max_left _ _),
        (le_max_left _ _).trans (le_max_right _ _),
        fun _ => (le_max_right _ _).trans (le_max_right _ _)⟩
  have hhi : bb ≤ r + 2 * (m - n * p) ∧ bb ≤ r + p ∧ bb ≤ p * (r / p) + (j0 + 1) * p ∧
      bb ≤ p * (r / p) + (k + j1 * p) := by
    have e : bb = min (min (r + 2 * (m - n * p)) (r + p))
        (min (p * (r / p) + (j0 + 1) * p) (p * (r / p) + (k + j1 * p))) := by
      rw [hbb]; rfl
    rw [e]
    exact ⟨(min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
      (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
  by_cases hab : aa < bb
  · have hnp : n * p ≤ m := by
      by_contra h
      have : m - n * p = 0 := by omega
      omega
    have W : Pre.Win p r m n (m - n * p) aa bb :=
      ⟨by omega, hp2, hlo.2.1, le_of_lt hab, hhi.2.1, hhi.1, by omega⟩
    have hdm := Nat.div_add_mod r p
    generalize hA : r / p = A at hlo hhi hdm
    have hgap : ∀ t : ℤ, (aa : ℤ) < t → t < bb → ¬ Cut p r (ttSing p q o) t := by
      intro t h1 h2 hcut
      have hpz : (0 : ℤ) < p := by exact_mod_cast hp0
      have c1 : ((p * A + j0 * p : ℕ) : ℤ) ≤ aa := by exact_mod_cast hlo.2.2.1
      have c2 : (bb : ℤ) ≤ ((p * A + (j0 + 1) * p : ℕ) : ℤ) := by exact_mod_cast hhi.2.2.1
      have c3 : (r : ℤ) ≤ aa := by exact_mod_cast hlo.2.1
      have c4 : (bb : ℤ) ≤ ((r + p : ℕ) : ℤ) := by exact_mod_cast hhi.2.1
      have c5 : (bb : ℤ) ≤ ((p * A + (k + j1 * p) : ℕ) : ℤ) := by exact_mod_cast hhi.2.2.2
      have c6 : ((p * A : ℕ) : ℤ) ≤ r := by exact_mod_cast (show p * A ≤ r by omega)
      push_cast at c1 c2 c4 c5 c6
      unfold Cut ttSing at hcut
      rcases hcut with (⟨s, hs⟩ | hdk) | ⟨s, hs⟩ | ⟨s, hs⟩
      · exact not_between (x := 0) (n := (A : ℤ) + j0) (t := t) hpz (by linarith) (by linarith) s
          (by rw [hs]; ring)
      · have hkz : (q : ℤ) * k = j * p + o := by exact_mod_cast hk
        have hdiv : (p : ℤ) ∣ (q : ℤ) * (t - k) := by
          have : (q : ℤ) * (t - k) = ((q : ℤ) * t - o) - j * p := by linarith
          rw [this]; exact dvd_sub hdk (dvd_mul_left _ _)
        have hcop : IsCoprime (p : ℤ) (q : ℤ) :=
          Nat.isCoprime_iff_coprime.2 (coprime_of_lt (Fact.out : p.Prime) hq hqp)
        obtain ⟨s, hs⟩ := hcop.dvd_of_dvd_mul_left hdiv
        have hts : t = k + s * p := by linarith
        have hkp' : (k : ℤ) < p := by exact_mod_cast hkp
        by_cases hn1 : j1 = 0
        · rw [hn1] at c5
          push_cast at c5
          exact not_between (x := k) (n := (A : ℤ) - 1) (t := t) hpz (by linarith) (by linarith) s hts
        · have hka : ((p * A + (k + (j1 - 1) * p) : ℕ) : ℤ) ≤ aa := by exact_mod_cast hlo.2.2.2 hn1
          have hn1' : ((j1 - 1 : ℕ) : ℤ) = (j1 : ℤ) - 1 := by
            rw [Nat.cast_sub (by omega)]; rfl
          push_cast [hn1'] at hka
          exact not_between (x := k) (n := (A : ℤ) + j1 - 1) (t := t) hpz (by linarith) (by linarith) s hts
      · exact not_between (x := 0) (n := (A : ℤ) + j0) (t := t) hpz (by linarith) (by linarith) s
          (by rw [hs]; ring)
      · exact not_between (x := r) (n := 0) (t := t) hpz (by linarith) (by linarith) s hs
    refine ⟨_, Pre.pre_gap_tt c hc T hnorm depth i hi.1 hi.2 p hpn hqN n aa bb W hgap, ?_⟩
    simp only [brPre, hev, zero_mul, add_zero]
    omega
  · have hW := (Pre.win_triv p r m hp0 hp2).norm
    refine ⟨_, Pre.pre_gap_tt c hc T hnorm depth i hi.1 hi.2 p hpn hqN (m / p) (r + m % p) (r + m % p)
      hW (fun t h1 h2 => absurd (lt_trans h1 h2) (lt_irrefl _)), ?_⟩
    simp only [brPre, hev, zero_mul, add_zero]
    omega

/-- Any list of prefix branches is valid. -/
theorem catValid_pres (c : ℚ) (hc : 0 < c) {Fr : Frame} {q o : ℕ} (T : TwoTermData Fr q o) {nm : ℕ}
    (hnorm : Fr.norm = (nm : ℚ)) (depth Pbad N0 : ℕ) (hq : 0 < q)
    (hP : ∀ p : ℕ, p.Prime → Pbad < p → ¬ p ∣ nm ∧ 5 ≤ p ∧ q < p) (pres : List (ℕ × ℕ × ℕ)) :
    CatValid c hc Fr depth q o Pbad N0 (pres.map (fun x => brPre x.1 x.2.1 x.2.2)) := by
  intro br hbr
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 hbr
  exact catValid_pre c hc T hnorm depth Pbad N0 hq hP x.1 x.2.1 x.2.2 _ (by simp)

/-- **Appending the prefix branches to any valid catalogue.** -/
theorem catValid_withPre (c : ℚ) (hc : 0 < c) {Fr : Frame} {q o : ℕ} (T : TwoTermData Fr q o) {nm : ℕ}
    (hnorm : Fr.norm = (nm : ℚ)) (depth Pbad N0 : ℕ) (hq : 0 < q)
    (hP : ∀ p : ℕ, p.Prime → Pbad < p → ¬ p ∣ nm ∧ 5 ≤ p ∧ 2 * q ≤ p) {cat : List Branch}
    (h : CatValid c hc Fr depth q o Pbad N0 cat) (pres : List (ℕ × ℕ × ℕ)) :
    CatValid c hc Fr depth q o Pbad N0 (cat ++ pres.map (fun x => brPre x.1 x.2.1 x.2.2)) :=
  catValid_append h (catValid_pres c hc T hnorm depth Pbad N0 hq
    (fun p hp hb => ⟨(hP p hp hb).1, (hP p hp hb).2.1, by have := (hP p hp hb).2.2; omega⟩) pres)

/-- **`catValid_bankW` with the prefix branches**: catalogue
`tableT ++ [LP1, LP2w, R] ++ windows ++ prefixes`. -/
theorem catValid_bankWP {Fr : Frame} (I : HybInst Fr) [∀ r m, I.DiagOK r m] {Lc : ℕ}
    (hL : I.cd.L = Lc) {Gd : ℕ → Prop}
    (Lv : CatalanFrames.HybCommon.LevelFacts I Gd (fun q c => c < I.cd.kq q))
    (c : ℚ) (hc : 0 < c) (hc1 : c ≤ 1) {q o : ℕ} (T : TwoTermData Fr q o) {nm : ℕ}
    (hnorm : Fr.norm = (nm : ℚ)) (depth Pbad K : ℕ) (hK : 2 ≤ c * K) (hq : 0 < q) (hLq : Lc ≤ q)
    (hP : ∀ p : ℕ, p.Prime → Pbad < p →
      ¬ p ∣ nm ∧ 5 ≤ p ∧ 2 * q ≤ p ∧ p ∉ I.cd.bad ∧ Gd p ∧ p ≠ 2)
    (hkq : ∀ p : ℕ, p.Prime → Pbad < p → ∀ j k : ℕ, q * k = j * p + o → 0 < j → j < q → 0 < k →
      k < p → I.cd.kq p = k) (wins : List (ℕ × ℕ)) (pres : List (ℕ × ℕ × ℕ)) :
    CatValid c hc Fr depth q o Pbad (NFr (1 / Fr.norm) (-1 / Fr.norm) q K)
      (tableT ++ ([brLP1, brLP2w, brRank] ++ wins.map (fun w => brWin w.1 w.2)) ++
        pres.map (fun x => brPre x.1 x.2.1 x.2.2)) :=
  catValid_withPre c hc T hnorm depth Pbad _ hq
    (fun p hp hb => ⟨(hP p hp hb).1, (hP p hp hb).2.1, (hP p hp hb).2.2.1⟩)
    (catValid_bankW I hL Lv c hc hc1 T hnorm depth Pbad K hK hq hLq hP hkq wins) pres

/-- **`catValid_bankUFw` with the prefix branches**: catalogue
`tableT ++ [LP1, LP2w, R, S] ++ windows ++ prefixes`. -/
theorem catValid_bankUFwP {Fr : Frame} (I : HybInst Fr) [∀ r m, I.DiagOK r m] {Lc : ℕ}
    (hL : I.cd.L = Lc) {Gd : ℕ → Prop}
    (Lv : CatalanFrames.HybCommon.LevelFacts I Gd (fun q c => c < I.cd.kq q))
    (c : ℚ) (hc : 0 < c) (hc1 : c ≤ 1) {q o : ℕ} (T : TwoTermData Fr q o) {nm : ℕ}
    (hnorm : Fr.norm = (nm : ℚ)) (depth Pbad K N1 : ℕ) (hK : 2 ≤ c * K) (hN1 : (q : ℚ) * (2 + c) ≤ c * N1)
    (hq : 0 < q) (hLq : Lc ≤ q)
    (hP : ∀ p : ℕ, p.Prime → Pbad < p →
      ¬ p ∣ nm ∧ 5 ≤ p ∧ 2 * q ≤ p ∧ p ∉ I.cd.bad ∧ Gd p ∧ p ≠ 2)
    (hkq : ∀ p : ℕ, p.Prime → Pbad < p → ∀ j k : ℕ, q * k = j * p + o → 0 < j → j < q → 0 < k →
      k < p → I.cd.kq p = k) (wins : List (ℕ × ℕ)) (pres : List (ℕ × ℕ × ℕ)) :
    CatValid c hc Fr depth q o Pbad (max (NFr (1 / Fr.norm) (-1 / Fr.norm) q K) N1)
      (tableT ++ ([brLP1, brLP2w, brRank, brS] ++ wins.map (fun w => brWin w.1 w.2)) ++
        pres.map (fun x => brPre x.1 x.2.1 x.2.2)) :=
  catValid_withPre c hc T hnorm depth Pbad _ hq
    (fun p hp hb => ⟨(hP p hp hb).1, (hP p hp hb).2.1, (hP p hp hb).2.2.1⟩)
    (catValid_bankUFw I hL Lv c hc hc1 T hnorm depth Pbad K N1 hK hN1 hq hLq hP hkq wins) pres

end CatalanCore.Uniform.Content.BankShared.Check

#print axioms CatalanCore.Uniform.Content.BankShared.Check.catValid_pre
#print axioms CatalanCore.Uniform.Content.BankShared.Check.catValid_bankWP
#print axioms CatalanCore.Uniform.Content.BankShared.Check.catValid_bankUFwP
