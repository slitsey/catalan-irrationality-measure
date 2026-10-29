import CatalanCore.Uniform.Content.BankShared.Check.Layers
import CatalanCore.Uniform.Content.BankShared.TwoTerm.Class
import CatalanCore.Uniform.Content.RankProducer.Closed
set_option Elab.async false

/-! # The rank branch from C2L's closed rank layer (lane C1L)

* `rankPrice_eq`: C2's closed price `rankPrice` (with the `(0,0), (1,0)` exclusion) equals the catalogue
  expression `tRank` (without it), because those two windows are already counted in `W_D0`
  (C1/PAPER.md §2.3, R);
* `catValid_rank`: the rank branch `brRank` of the catalogue is valid, from `rankClosedLayer`, with
  `N0 = NFr (1/norm) (-1/norm) q K` (C2L's choice-built bound, never evaluated) and any `K` with `c K ≥ 2`. -/

namespace CatalanCore.Uniform.Content.BankShared.Check
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.BankShared
  CatalanCore.Uniform.Content.Member CatalanCore.Uniform.Content.RankProducer
  CatalanCore.Uniform.Content.UFSimple CatalanCore.Uniform.Content.Smith CatalanCore.Basic CatalanCore.Arith
  CatalanCore.Arith.Hybrid TwoTerm Cat

theorem max_max_distrib (a b c : ℕ) : max a (max b c) = max (max a b) (max a c) := by omega

theorem max_excl (X a a' b b' c c' d d' : ℕ) (ha : max X a = max X a') (hb : max X b = max X b')
    (hc : max X c = max X c') (hd : max X d = max X d') :
    max X (max (max a b) (max c d)) = max X (max (max a' b') (max c' d')) := by
  rw [max_max_distrib, max_max_distrib X a b, max_max_distrib X c d, ha, hb, hc, hd,
    ← max_max_distrib X a' b', ← max_max_distrib X c' d', ← max_max_distrib]

theorem wc_absorb (m r p k h : ℕ) (z : Bool) (X : ℕ) (h0 : Wk m r p k 0 false ≤ X)
    (h1 : Wk m r p k 1 false ≤ X) : max X (Wc m r p k h z) = max X (Wk m r p k h z) := by
  unfold Wc
  split_ifs with hc
  · obtain ⟨hh, rfl⟩ := hc
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hh with rfl | rfl
    · rw [max_eq_left (Nat.zero_le _), max_eq_left h0]
    · rw [max_eq_left (Nat.zero_le _), max_eq_left h1]
  · rfl

/-- **C2's closed rank price is the catalogue expression `tRank`.** -/
theorem rankPrice_eq (m r p k : ℕ) (hp : 0 < p) (hk : 1 ≤ k) :
    rankPrice m r p k = tRank.evalN r p m k := by
  set X := max (m + nsqC m r p k) (Wk m r p k 0 false + Wk m r p k 1 false + 2 * nsqC m r p k) with hX
  have h0 : Wk m r p k 0 false ≤ X :=
    le_max_of_le_right (le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))
  have h1 : Wk m r p k 1 false ≤ X :=
    le_max_of_le_right (le_trans (Nat.le_add_left _ _) (Nat.le_add_right _ _))
  have e : rankPrice m r p k = 2 * (r + m) - max X
      (max (max (Wk m r p k (r / p) false) (Wk m r p k (r / p) true))
        (max (Wk m r p k (r / p + 1) false) (Wk m r p k (r / p + 1) true))) := by
    unfold rankPrice
    rw [max_excl X _ _ _ _ _ _ _ _ (wc_absorb m r p k _ _ X h0 h1) (wc_absorb m r p k _ _ X h0 h1)
      (wc_absorb m r p k _ _ X h0 h1) (wc_absorb m r p k _ _ X h0 h1)]
  have w0 : Wk m r p k 0 false = min (r + 2 * m) k - r := by
    show min (r + 2 * m) (p * 0 + (k - 1) + 1) - max r (p * 0 + 0) = _
    omega
  have w1 : Wk m r p k 1 false = min (r + 2 * m) (p + k) - max r p := by
    show min (r + 2 * m) (p * 1 + (k - 1) + 1) - max r (p * 1 + 0) = _
    omega
  have w2 : Wk m r p k (r / p) false = min (r + 2 * m) (p * (r / p) + k) - max r (p * (r / p)) := by
    show min (r + 2 * m) (p * (r / p) + (k - 1) + 1) - max r (p * (r / p) + 0) = _
    generalize p * (r / p) = A
    omega
  have w3 : Wk m r p k (r / p) true = min (r + 2 * m) (p * (r / p) + p) - max r (p * (r / p) + k) := by
    show min (r + 2 * m) (p * (r / p) + (p - 1) + 1) - max r (p * (r / p) + k) = _
    generalize p * (r / p) = A
    omega
  have w4 : Wk m r p k (r / p + 1) false =
      min (r + 2 * m) (p * (r / p) + p + k) - max r (p * (r / p) + p) := by
    show min (r + 2 * m) (p * (r / p + 1) + (k - 1) + 1) - max r (p * (r / p + 1) + 0) = _
    rw [Nat.mul_succ]
    generalize p * (r / p) = A
    omega
  have w5 : Wk m r p k (r / p + 1) true =
      min (r + 2 * m) (p * (r / p) + p + p) - max r (p * (r / p) + p + k) := by
    show min (r + 2 * m) (p * (r / p + 1) + (p - 1) + 1) - max r (p * (r / p + 1) + k) = _
    rw [Nat.mul_succ]
    generalize p * (r / p) = A
    omega
  rw [e, hX, w0, w1, w2, w3, w4, w5]
  rfl

/-- **The rank branch is valid** (C2L's `rankClosedLayer`), for `N0 = NFr (1/norm) (-1/norm) q K`. -/
theorem catValid_rank (c : ℚ) (hc : 0 < c) {Fr : Frame} {q o : ℕ} (T : TwoTermData Fr q o)
    (depth Pbad K : ℕ) (hK : 2 ≤ c * K) (hP : ∀ p : ℕ, p.Prime → Pbad < p → q < p) :
    CatValid c hc Fr depth q o Pbad (NFr (1 / Fr.norm) (-1 / Fr.norm) q K) [brRank] := by
  intro b hb i hi hr0 p _ hPb hN0 hqN j k hk hj0 hjq hk0 hkp hcond
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  subst hb
  have hqp := hP p Fact.out hPb
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hm : 2 * (altGeom c hc).borderSize i.1 < p := by
    have h := hcond c2mltp (by simp [brRank])
    simp only [c2mltp, Cond.Holds, Cond.L, ite_true] at h; push_cast at h; omega
  -- the pole residue of the layer is the root datum `k`
  set ρ : ℕ → ℕ := fun p => poleIndex q (q - o) p with hρdef
  have hρk : ρ p = k := by
    have ho := T.o_pos
    have hoq := T.o_lt
    have hk' : q * k = j * p + (q - (q - o)) := by rw [show q - (q - o) = o by omega]; exact hk
    exact (rootClass_unique (Fact.out : p.Prime) (by omega) (by omega) hqp hjq hk').2.symm
  -- `(r + 2m)/p ≤ K`
  have hKr : (i.1 + 2 * (altGeom c hc).borderSize i.1) / p ≤ K := by
    obtain ⟨hb1, -⟩ := altGeom_border c hc hi.2
    have h1 : c * (i.1 : ℚ) - 1 < p := by
      have : (2 * ((altGeom c hc).borderSize i.1 : ℚ)) < p := by exact_mod_cast hm
      linarith
    have hp1 : (1 : ℚ) ≤ p := by exact_mod_cast hp0
    have h2 : c * (i.1 : ℚ) < c * (K * p) := by
      have : (2 : ℚ) * p ≤ c * K * p := mul_le_mul_of_nonneg_right hK (by positivity)
      nlinarith
    have h3 : (i.1 : ℚ) < K * p := lt_of_mul_lt_mul_left h2 hc.le
    have h4 : i.1 < K * p := by exact_mod_cast h3
    have h5 : i.1 + 2 * (altGeom c hc).borderSize i.1 < (K + 1) * p := by
      rw [Nat.add_mul, Nat.one_mul]; omega
    exact Nat.lt_succ_iff.1 ((Nat.div_lt_iff_lt_mul hp0).2 h5)
  have hv : RankHyp c hc q o (NFr (1 / Fr.norm) (-1 / Fr.norm) q K) K i.1 p (ρ p) := by
    rw [hρk]
    refine ⟨hi.2, hr0, hm, by rw [sq]; exact hqN, hN0, hKr, ?_, hk0, hkp⟩
    refine ⟨j, ?_⟩
    have : q * k - o = j * p := by omega
    rw [this, mul_comm]
  let L := rankClosedLayer (c := c) (hc := hc) (depth := depth) T K
    (fun r p => RankHyp c hc q o (NFr (1 / Fr.norm) (-1 / Fr.norm) q K) K r p (ρ p)) ρ
    (by intro r p _ h; exact h)
  have hg := L.gle i hi.1 p hv
  have hb : L.base i.1 p = rankPrice ((altGeom c hc).borderSize i.1) i.1 p (ρ p) := by
    rw [rankClosedLayer_base]
  have hd : L.debit = 0 := rankClosedLayer_debit T K _ ρ _
  rw [hb, hd, hρk, rankPrice_eq _ _ _ _ hp0 hk0, zero_mul, add_zero] at hg
  exact ⟨_, hg, by simp only [brRank, zero_mul, add_zero]; exact le_refl _⟩

/-- **The catalogue of a two-term bank, fully instantiated**: table T, LP1, LP2, the rank branch and any M3D
windows are valid with `N0 = NFr`, given the T-layer data of the frame. -/
theorem catValid_bank {Fr : Frame} (I : HybInst Fr) [∀ r m, I.DiagOK r m] {Lc cm : ℕ}
    (B : CatalanFrames.HybGen.ArithmeticInfo I Lc cm) {Gd : ℕ → Prop}
    (Lv : CatalanFrames.HybCommon.LevelFacts I Gd (fun q c => c < I.cd.kq q))
    (c : ℚ) (hc : 0 < c) (hc1 : c ≤ 1) {q o : ℕ} (T : TwoTermData Fr q o) {nm : ℕ}
    (hnorm : Fr.norm = (nm : ℚ)) (depth Pbad K : ℕ) (hK : 2 ≤ c * K) (hq : 0 < q) (hLq : Lc ≤ q)
    (hP : ∀ p : ℕ, p.Prime → Pbad < p →
      ¬ p ∣ nm ∧ 5 ≤ p ∧ 2 * q ≤ p ∧ p ∉ I.cd.bad ∧ Gd p ∧ p ≠ 2)
    (hkq : ∀ p : ℕ, p.Prime → Pbad < p → ∀ j k : ℕ, q * k = j * p + o → 0 < j → j < q → 0 < k →
      k < p → I.cd.kq p = k) (wins : List (ℕ × ℕ)) :
    CatValid c hc Fr depth q o Pbad (NFr (1 / Fr.norm) (-1 / Fr.norm) q K)
      (tableT ++ ([brLP1, brLP2, brRank] ++ wins.map (fun w => brWin w.1 w.2))) :=
  catValid_twoTerm I B Lv c hc hc1 T hnorm depth Pbad _ hq hLq hP hkq
    (catValid_rank c hc T depth Pbad K hK (fun p hp h => by have := (hP p hp h).2.2.1; omega)) wins

end CatalanCore.Uniform.Content.BankShared.Check
