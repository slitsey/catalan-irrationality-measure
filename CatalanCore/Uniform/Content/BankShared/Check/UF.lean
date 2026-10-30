module

public import CatalanCore.Uniform.Content.BankShared.Check.Rank
public import CatalanCore.Uniform.Content.BankShared.TwoTerm.UF

@[expose] public section
set_option Elab.async false

/-! # The UF branch S (lane C1L; C1/PAPER.md Lemma 3)

* `tS`: the closed UF price as an `𝔈`-expression, the minimum of the four `closedBound` candidates WITHOUT the
  `CandOK` tests; `evalN_tCand` (the candidates are `closedBound` at C4/UF's window data, by `rfl`);
* `closedPrice_le_tS` (Lemma 3, the direction used): `closedPrice ≤ tS` for `1 ≤ m`, `2m ≤ p`, `1 ≤ ρ < p`
  (a candidate failing `CandOK` has an empty window and costs `2r + m`, which the first candidate never
  exceeds);
* `brS = ⟨tS, [2m ≤ p, 1 ≤ m], 1⟩`; `catValid_uf` from `uf_gle_tt` (C4) for every prime above a bound `N0`
  with `c N0 ≥ q (2 + c)` (which gives `q (r + p) ≤ p²` on `2m ≤ p`);
* `catValid_mono`, and `catValid_bankUF`: table T, LP1, LP2, rank, UF and windows, with
  `N0 = max (NFr …) N1`. -/

namespace CatalanCore.Uniform.Content.BankShared.Check
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.BankShared
  CatalanCore.Uniform.Content.Member CatalanCore.Uniform.Content.UFSimple CatalanCore.Uniform.Content.Smith
  CatalanCore.Uniform.Content.RankProducer CatalanCore.Basic CatalanCore.Arith CatalanCore.Arith.Hybrid
  TwoTerm Cat Expr

namespace Cat

def eB (κ : Bool) : Expr := if κ then add ap vp else ap
def eL (ζ : Bool) : Expr := if ζ then vk else cst 0
def eU (ζ : Bool) : Expr := if ζ then tsub vp (cst 1) else tsub vk (cst 1)
def eUb (κ ζ : Bool) : Expr := if κ then mn (eU ζ) (tsub sp (cst 1)) else eU ζ
def eOvl (a b : Expr) : Expr := tsub (mn eN (add b (cst 1))) (mx vr a)
def eBeta (w0 w1 : Expr) : Expr :=
  add (add (eOvl w0 w1) (eOvl (add w0 vp) (add w1 vp))) (eOvl (tsub w0 vp) (tsub w1 vp))
def eCB (t0 tv w0 : Expr) : Expr :=
  tsub (smul 2 (add vr vm))
    (add (add vm (tsub (tsub (mn (add tv (cst 1)) eN) t0) vm))
      (tsub (tsub (tsub (mn (add tv (cst 1)) eN) t0) vm)
        (tsub vp (add (tsub (add tv (cst 1)) w0) (tsub (smul 2 vm) (eBeta w0 tv))))))
def tCand (κ ζ : Bool) : Expr :=
  eCB (mx vr (add (eB κ) (eL ζ))) (add (eB κ) (eUb κ ζ)) (add (eB κ) (eL ζ))
def tS : Expr := mn (mn (tCand false false) (tCand false true)) (mn (tCand true false) (tCand true true))
/-- `1 ≤ m` -/
def c1lem : Cond := ⟨0, 0, 1, 0, -1, false⟩

end Cat

/-- The UF branch (debit 1). -/
def brS : Branch := ⟨tS, [c2mlep, c1lem], 1⟩

theorem evalN_tCand (r p m k : ℕ) (κ ζ : Bool) :
    (tCand κ ζ).evalN r p m k = closedBound m r p (max r (candB r p κ + candL k ζ))
      (candB r p κ + candUb r p k κ ζ) (candB r p κ + candL k ζ) := by
  cases κ <;> cases ζ <;> rfl

theorem closedBound_le' (m r p t0 tv w0 : ℕ) : closedBound m r p t0 tv w0 ≤ 2 * r + m := by
  unfold closedBound; omega

theorem closedBound_of_empty (m r p t0 tv w0 : ℕ) (h : min (tv + 1) (r + 2 * m) ≤ t0) :
    closedBound m r p t0 tv w0 = 2 * r + m := by
  unfold closedBound
  have h0 : min (tv + 1) (r + 2 * m) - t0 = 0 := by omega
  rw [h0]
  omega

/-- A candidate failing `CandOK` has an empty window. -/
theorem closedBound_notOK (m r p k : ℕ) (κ ζ : Bool) (hp : 0 < p) (h2m : 2 * m ≤ p)
    (hn : ¬ CandOK m r p k κ ζ) :
    closedBound m r p (max r (candB r p κ + candL k ζ)) (candB r p κ + candUb r p k κ ζ)
      (candB r p κ + candL k ζ) = 2 * r + m := by
  apply closedBound_of_empty
  unfold CandOK at hn
  by_cases h1 : max r (candB r p κ + candL k ζ) < r + 2 * m
  · by_cases h2 : max r (candB r p κ + candL k ζ) ≤ candB r p κ + candUb r p k κ ζ
    · -- `κ` and `r mod p = 0`: the credited end is the block start `r + p`
      have h3 : κ = true ∧ ¬ 1 ≤ r % p := by
        by_contra hc
        apply hn
        refine ⟨h1, h2, fun hk => ?_⟩
        by_contra h4
        exact hc ⟨hk, h4⟩
      obtain ⟨rfl, h4⟩ := h3
      have hs : r % p = 0 := by omega
      have hA : p * (r / p) = r := by have := Nat.div_add_mod r p; omega
      have hub : candUb r p k true ζ = 0 := by
        show min (candU p k ζ) (r % p - 1) = 0
        rw [hs]; exact Nat.min_zero _
      have hB : candB r p true = r + p := by
        show p * (r / p) + p = r + p
        rw [hA]
      simp only [hub, hB] at h2 ⊢
      have : r + p ≤ max r (r + p + candL k ζ) := (Nat.le_add_right _ _).trans (le_max_right _ _)
      omega
    · omega
  · omega

theorem closedPrice_le_cand (m r p k : ℕ) (κ ζ : Bool) :
    closedPrice m r p k ≤ candPrice m r p k κ ζ := by
  unfold closedPrice
  cases κ <;> cases ζ
  · exact (min_le_left _ _).trans (min_le_left _ _)
  · exact (min_le_left _ _).trans (min_le_right _ _)
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans (min_le_right _ _)

/-- The first candidate is admissible, so `closedPrice ≤ 2r + m`. -/
theorem closedPrice_le_two (m r p k : ℕ) (hp : 0 < p) (hm1 : 1 ≤ m) (hk1 : 1 ≤ k) (hkp : k < p) :
    closedPrice m r p k ≤ 2 * r + m := by
  have hok := candOK_first (r := r) hp hm1 hk1 hkp
  refine (closedPrice_le_cand m r p k false (decide (k ≤ r % p))).trans ?_
  unfold candPrice
  rw [if_pos hok]
  exact closedBound_le' _ _ _ _ _ _

/-- **Lemma 3** (the direction used): `closedPrice ≤ tS`. -/
theorem closedPrice_le_tS (m r p k : ℕ) (hp : 0 < p) (hm1 : 1 ≤ m) (h2m : 2 * m ≤ p) (hk1 : 1 ≤ k)
    (hkp : k < p) : closedPrice m r p k ≤ tS.evalN r p m k := by
  have hle := closedPrice_le_two m r p k hp hm1 hk1 hkp
  have hc : ∀ κ ζ : Bool, closedPrice m r p k ≤ (tCand κ ζ).evalN r p m k := by
    intro κ ζ
    rw [evalN_tCand]
    by_cases hok : CandOK m r p k κ ζ
    · have := closedPrice_le_cand m r p k κ ζ
      unfold candPrice at this
      rwa [if_pos hok] at this
    · rw [closedBound_notOK m r p k κ ζ hp h2m hok]; exact hle
  show closedPrice m r p k ≤ min (min ((tCand false false).evalN r p m k) ((tCand false true).evalN r p m k))
    (min ((tCand true false).evalN r p m k) ((tCand true true).evalN r p m k))
  exact le_min (le_min (hc _ _) (hc _ _)) (le_min (hc _ _) (hc _ _))

theorem catValid_mono {c : ℚ} {hc : 0 < c} {Fr : Frame} {depth q o Pbad N0 N1 : ℕ} {l : List Branch}
    (h : CatValid c hc Fr depth q o Pbad N0 l) (hN : N0 ≤ N1) : CatValid c hc Fr depth q o Pbad N1 l :=
  fun b hb i hi hr0 p _ hPb hN1 => h b hb i hi hr0 p hPb (lt_of_le_of_lt hN hN1)

/-- **The UF branch is valid** (`uf_gle_tt`), above a bound `N0` with `c N0 ≥ q (2 + c)`. -/
theorem catValid_uf (c : ℚ) (hc : 0 < c) {Fr : Frame} {q o : ℕ} (T : TwoTermData Fr q o) {nm : ℕ}
    (hnorm : Fr.norm = (nm : ℚ)) (depth Pbad N0 : ℕ) (hN0 : (q : ℚ) * (2 + c) ≤ c * N0)
    (hP : ∀ p : ℕ, p.Prime → Pbad < p → ¬ p ∣ nm ∧ 2 < p ∧ q < p) :
    CatValid c hc Fr depth q o Pbad N0 [brS] := by
  intro b hb i hi hr0 p _ hPb hN hqN j k hk hj0 hjq hk0 hkp hcond
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  subst hb
  obtain ⟨hpn, hp2, hqp⟩ := hP p Fact.out hPb
  have hp0 : 0 < p := by omega
  have h2m : 2 * (altGeom c hc).borderSize i.1 ≤ p := by
    have h := hcond c2mlep (by simp [brS])
    simp only [c2mlep, Cond.Holds, Cond.L, Bool.false_eq_true, ite_false] at h; push_cast at h; omega
  have hm1 : 1 ≤ (altGeom c hc).borderSize i.1 := by
    have h := hcond c1lem (by simp [brS])
    simp only [c1lem, Cond.Holds, Cond.L, Bool.false_eq_true, ite_false] at h; push_cast at h; omega
  -- `q (r + p) ≤ p²` from `2m ≤ p`, `c r - 1 ≤ 2m` and `c p > q (2 + c)`
  have hsq : q * (i.1 + p) ≤ p * p := by
    obtain ⟨hb1, -⟩ := altGeom_border c hc hi.2
    have h1 : c * (i.1 : ℚ) ≤ p + 1 := by
      have : (2 * ((altGeom c hc).borderSize i.1 : ℚ)) ≤ p := by exact_mod_cast h2m
      linarith
    have hpN : (N0 : ℚ) + 1 ≤ p := by exact_mod_cast hN
    have hq0 : (0 : ℚ) ≤ q := Nat.cast_nonneg q
    have h2 : (q : ℚ) * (2 + c) ≤ c * p := by
      have := mul_le_mul_of_nonneg_left hpN hc.le
      linarith
    have hp1 : (1 : ℚ) ≤ p := by exact_mod_cast hp0
    -- c q (r + p) ≤ q (p + 1) + c q p ≤ q p + q p + c q p ≤ c p²
    have h3 : c * ((q : ℚ) * (i.1 + p)) ≤ c * ((p : ℚ) * p) := by
      have e1 : c * ((q : ℚ) * (i.1 + p)) = (q : ℚ) * (c * i.1) + c * q * p := by ring
      have e2 : (q : ℚ) * (c * i.1) ≤ q * (p + 1) := mul_le_mul_of_nonneg_left h1 hq0
      have e3 : (q : ℚ) * (p + 1) ≤ q * p + q * p := by
        have := mul_le_mul_of_nonneg_left hp1 hq0
        linarith
      have e4 : (q : ℚ) * (2 + c) * p ≤ c * p * p := by
        have := mul_le_mul_of_nonneg_right h2 (by linarith : (0 : ℚ) ≤ p)
        linarith
      linarith
    have h4 : (q : ℚ) * (i.1 + p) ≤ (p : ℚ) * p := le_of_mul_le_mul_left h3 hc
    exact_mod_cast h4
  have hg := uf_gle_tt c hc T hnorm depth i hi.1 hi.2 hr0 p k j hm1 hsq h2m hpn hp2 hqp hk hj0 hjq
  refine ⟨_, hg, ?_⟩
  have := closedPrice_le_tS ((altGeom c hc).borderSize i.1) i.1 p k hp0 hm1 h2m hk0 hkp
  simp only [brS, one_mul]
  omega

/-- **The catalogue of a two-term bank with UF, fully instantiated**: table T, LP1, LP2, rank, UF and any M3D
windows, with `N0 = max (NFr …) N1`, `c N1 ≥ q (2 + c)`. -/
theorem catValid_bankUF {Fr : Frame} (I : HybInst Fr) [∀ r m, I.DiagOK r m] {Lc : ℕ}
    (hL : I.cd.L = Lc) {Gd : ℕ → Prop}
    (Lv : CatalanFrames.HybCommon.LevelFacts I Gd (fun q c => c < I.cd.kq q))
    (c : ℚ) (hc : 0 < c) (hc1 : c ≤ 1) {q o : ℕ} (T : TwoTermData Fr q o) {nm : ℕ}
    (hnorm : Fr.norm = (nm : ℚ)) (depth Pbad K N1 : ℕ) (hK : 2 ≤ c * K) (hN1 : (q : ℚ) * (2 + c) ≤ c * N1)
    (hq : 0 < q) (hLq : Lc ≤ q)
    (hP : ∀ p : ℕ, p.Prime → Pbad < p →
      ¬ p ∣ nm ∧ 5 ≤ p ∧ 2 * q ≤ p ∧ p ∉ I.cd.bad ∧ Gd p ∧ p ≠ 2)
    (hkq : ∀ p : ℕ, p.Prime → Pbad < p → ∀ j k : ℕ, q * k = j * p + o → 0 < j → j < q → 0 < k →
      k < p → I.cd.kq p = k) (wins : List (ℕ × ℕ)) :
    CatValid c hc Fr depth q o Pbad (max (NFr (1 / Fr.norm) (-1 / Fr.norm) q K) N1)
      (tableT ++ ([brLP1, brLP2, brRank, brS] ++ wins.map (fun w => brWin w.1 w.2))) := by
  set N0 := max (NFr (1 / Fr.norm) (-1 / Fr.norm) q K) N1
  have hT := catValid_tableT I hL Lv c hc hc1 depth q o Pbad N0 hLq
    (fun p hp h => ⟨(hP p hp h).2.2.2.1, (hP p hp h).2.2.2.2.1, (hP p hp h).2.2.2.2.2⟩) hkq
  have hLP := catValid_LP c hc T hnorm depth Pbad N0 (fun p hp h => ⟨(hP p hp h).1, (hP p hp h).2.1,
    (hP p hp h).2.2.1⟩)
  have hR := catValid_mono (catValid_rank c hc T depth Pbad K hK
    (fun p hp h => by have := (hP p hp h).2.2.1; omega)) (le_max_left _ _ : _ ≤ N0)
  have hS := catValid_uf c hc T hnorm depth Pbad N0
    (by
      have : (N1 : ℚ) ≤ N0 := by exact_mod_cast le_max_right _ _
      have := mul_le_mul_of_nonneg_left this hc.le
      linarith)
    (fun p hp h => ⟨(hP p hp h).1, by have := (hP p hp h).2.1; omega,
      by have := (hP p hp h).2.2.1; omega⟩)
  have hW : CatValid c hc Fr depth q o Pbad N0 (wins.map (fun w => brWin w.1 w.2)) := by
    intro b hb
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hb
    exact catValid_win c hc T hnorm depth Pbad N0 hq
      (fun p hp h => ⟨(hP p hp h).1, by have := (hP p hp h).2.2.1; omega⟩) w.1 w.2 _ (by simp)
  refine catValid_append hT ?_
  intro b hb
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with (rfl | rfl | rfl | rfl) | hb
  · exact hLP _ (by simp)
  · exact hLP _ (by simp)
  · exact hR _ (by simp)
  · exact hS _ (by simp)
  · exact hW b hb

end CatalanCore.Uniform.Content.BankShared.Check
