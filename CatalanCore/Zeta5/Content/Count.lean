module

public import CatalanCore.Zeta5.Content.Parity
public import CatalanCore.Zeta5.Profile.Gref

@[expose] public section

/-!
# ZC27: the parity gain counts `p · g_ref(K/p) + O(M)` classes

For `InnerHyp p n M L₀` (`K = 40 n`, `x = K/p`), the class counts in `kpar` are exact functions
of the residues `v = K mod p`, `v' = N mod p` and of `E = innerE`:

* `ℓ_K(a)` is odd iff `a ≤ t_K`, with `t_K = v` (`2v < p`) or `p − v − 1` (`2v > p`); the even
  group is `S = (t_K, m]`, `|S| = m − t_K`; inside `S`, `ℓ_N(a)` is odd iff `a ≤ t_N`, so
  `#{a ∈ S : ℓ_N odd} = (t_N − t_K)₊`;
* `e_c = |S ∩ ε|` satisfies `e_c = (E − t_K)₊` (`2v < p`; `S` is the lower group) and
  `e_c = min(E, |S|)` (`2v > p`; `S` is the top group);
* `T odd`:  `k ≥ |S| − (t_N − t_K)₊ − e_c − L₀`; `T even`: `k ≥ e_c − (t_N − t_K)₊ − L₀`.

With `m T + E = 46 n − L₀ − 3⌊N/p⌋` and `m · 23x/10 = 46 n − 46 n/p`, the base `T` is
`⌊23x/10⌋` or `⌊23x/10⌋ − 1`, and `E = p u + O(M)` (`u = 23x/20 − ⌊23x/10⌋/2`) in the first case.
Comparing with `g_ref = (e − q)₊` (`T` even) or `(s − e − q)₊` (`T` odd) gives
`kpar_ge : p · g_ref(K/p) − 30 M ≤ k` (`kpar_ge`), uniformly; at the transitions
`T = ⌊23x/10⌋ − 1` the two formulas agree up to `O(M)` (allocation continuity).
-/

open Finset

set_option linter.deprecated false

namespace Apery

open CatalanCore.Zeta5.Profile

/-- The threshold `t`: `a ≤ t` iff `a_c(v)` is odd. -/
def thr (p v : ℕ) : ℕ := if v ≤ p / 2 then v else p - v - 1

lemma aCnt_spec {p m v a : ℕ} (hm : 2 * m + 1 = p) (hv : v < p) (ha1 : 1 ≤ a) (ham : a ≤ m) :
    (a ≤ thr p v → aCnt p v a = 1) ∧
    (thr p v < a → aCnt p v a = if v ≤ m then 0 else 2) := by
  have hpm : p / 2 = m := by omega
  unfold aCnt thr
  rw [hpm]
  constructor <;> intro h <;> split_ifs at h ⊢ <;> omega

lemma thr_le {p m v : ℕ} (hm : 2 * m + 1 = p) (hv : v < p) : thr p v ≤ m := by
  have hpm : p / 2 = m := by omega
  unfold thr; rw [hpm]; split_ifs <;> omega

lemma card_filter_fin (k : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    (univ.filter (fun a : Fin k => P a)).card = ((range k).filter P).card := by
  refine Finset.card_bij (fun a _ => (a : ℕ)) ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨a.isLt, ha⟩
  · intro a _ b _ h; exact Fin.ext h
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_range] at hb
    exact ⟨⟨b, hb.1⟩, by simp [hb.2], rfl⟩

lemma card_Ioc_fin (m t u : ℕ) (hu : u ≤ m) :
    (univ.filter (fun a : Fin (m + 1) => t < (a : ℕ) ∧ (a : ℕ) ≤ u)).card = u - t := by
  refine (card_filter_fin (m + 1) (fun a => t < a ∧ a ≤ u)).trans ?_
  have : (range (m + 1)).filter (fun a => t < a ∧ a ≤ u) = Ioc t u := by
    ext a; simp only [mem_filter, mem_range, mem_Ioc]; omega
  rw [this, Nat.card_Ioc]

lemma card_split {α : Type*} [DecidableEq α] (s : Finset α) (P1 P2 R : α → Prop)
    [DecidablePred P1] [DecidablePred P2] [DecidablePred R]
    (h1 : ∀ a ∈ s, (P1 a ∨ P2 a) ↔ R a) (h2 : ∀ a ∈ s, P1 a → ¬ P2 a) :
    (s.filter P1).card + (s.filter P2).card = (s.filter R).card := by
  rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter.mpr h2), ← Finset.filter_or]
  exact congrArg _ (Finset.filter_congr h1)

section
variable {p n M L0 : ℕ}

lemma lK_class (H : InnerHyp p n M L0) (a : Fin (p / 2 + 1)) (ha : a ≠ 0) :
    lK p n a = 2 * (40 * n / p) + aCnt p (40 * n % p) a := by
  haveI : Fact p.Prime := ⟨H.prime⟩
  have h1 : 1 ≤ (a : ℕ) := Nat.one_le_iff_ne_zero.mpr (fun h => ha (Fin.ext h))
  have h2 : (a : ℕ) ≤ p / 2 := Nat.lt_succ_iff.mp a.isLt
  unfold lK
  exact SX_class H.p_odd h1 h2 _

lemma lN_class (H : InnerHyp p n M L0) (a : Fin (p / 2 + 1)) (ha : a ≠ 0) :
    lN p n a = 2 * (3 * n / p) + aCnt p (3 * n % p) a := by
  haveI : Fact p.Prime := ⟨H.prime⟩
  have h1 : 1 ≤ (a : ℕ) := Nat.one_le_iff_ne_zero.mpr (fun h => ha (Fin.ext h))
  have h2 : (a : ℕ) ≤ p / 2 := Nat.lt_succ_iff.mp a.isLt
  unfold lN
  exact SX_class H.p_odd h1 h2 _

/-- **The integer counts behind `kpar`.** -/
theorem kpar_int (H : InnerHyp p n M L0) :
    ∃ ec : ℕ,
      (innerT p n L0 % 2 = 0 →
        (ec : ℤ) - ((thr p (3 * n % p) - thr p (40 * n % p) : ℕ) : ℤ) - L0 ≤ kpar p n L0) ∧
      (innerT p n L0 % 2 = 1 →
        ((p / 2 - thr p (40 * n % p) : ℕ) : ℤ) - ((thr p (3 * n % p) - thr p (40 * n % p) : ℕ) : ℤ)
          - ec - L0 ≤ kpar p n L0) ∧
      ec ≤ innerE p n L0 ∧ ec ≤ p / 2 - thr p (40 * n % p) ∧
      innerE p n L0 ≤ thr p (40 * n % p) + ec ∧
      (40 * n % p ≤ p / 2 → 0 < ec → thr p (40 * n % p) + ec ≤ innerE p n L0) ∧
      (p / 2 < 40 * n % p → ec < p / 2 - thr p (40 * n % p) → ec = innerE p n L0) := by
  classical
  have hm := H.p_odd
  have hpp : 0 < p := H.prime.pos
  set v := 40 * n % p with hvdef
  set w := 3 * n % p with hwdef
  set tK := thr p v with htK
  set tN := thr p w with htN
  have hv : v < p := Nat.mod_lt _ hpp
  have hw : w < p := Nat.mod_lt _ hpp
  have htKm : tK ≤ p / 2 := thr_le hm hv
  have htNm : tN ≤ p / 2 := thr_le hm hw
  set eps := epsSet p n L0 with hepsdef
  set S := parS p n with hSdef
  -- classes
  have hval : ∀ a : Fin (p / 2 + 1), a ≠ 0 → 1 ≤ (a : ℕ) ∧ (a : ℕ) ≤ p / 2 := fun a ha =>
    ⟨Nat.one_le_iff_ne_zero.mpr (fun h => ha (Fin.ext h)), Nat.lt_succ_iff.mp a.isLt⟩
  have hne : ∀ a : Fin (p / 2 + 1), 1 ≤ (a : ℕ) → a ≠ 0 := fun a h h0 => by
    rw [h0] at h; simp at h
  have hlK : ∀ a : Fin (p / 2 + 1), a ≠ 0 → lK p n a = 2 * (40 * n / p) + aCnt p v a :=
    fun a ha => lK_class H a ha
  have hlN : ∀ a : Fin (p / 2 + 1), a ≠ 0 → lN p n a = 2 * (3 * n / p) + aCnt p w a :=
    fun a ha => lN_class H a ha
  have hSmem : ∀ a : Fin (p / 2 + 1), a ∈ S ↔ tK < (a : ℕ) := by
    intro a
    rw [hSdef, parS, Finset.mem_filter]
    constructor
    · rintro ⟨-, ha, hev⟩
      obtain ⟨h1, h2⟩ := hval a ha
      rw [hlK a ha] at hev
      by_contra hc
      push Not at hc
      have := (aCnt_spec hm hv h1 h2).1 hc
      omega
    · intro hlt
      have ha : a ≠ 0 := hne a (by omega)
      obtain ⟨h1, h2⟩ := hval a ha
      refine ⟨Finset.mem_univ _, ha, ?_⟩
      rw [hlK a ha, (aCnt_spec hm hv h1 h2).2 hlt]
      split_ifs <;> omega
  have hNodd : ∀ a ∈ S, lN p n a % 2 = 1 ↔ (a : ℕ) ≤ tN := by
    intro a haS
    have ha : a ≠ 0 := hne a (by have := (hSmem a).1 haS; omega)
    obtain ⟨h1, h2⟩ := hval a ha
    rw [hlN a ha]
    constructor
    · intro h
      by_contra hc
      push Not at hc
      rw [(aCnt_spec hm hw h1 h2).2 hc] at h
      split_ifs at h <;> omega
    · intro h
      rw [(aCnt_spec hm hw h1 h2).1 h]; omega
  -- |S| and the odd part of S
  have hScard : S.card = p / 2 - tK := by
    have : S = univ.filter (fun a : Fin (p / 2 + 1) => tK < (a : ℕ) ∧ (a : ℕ) ≤ p / 2) := by
      ext a
      rw [hSmem a, Finset.mem_filter]
      have := Nat.lt_succ_iff.mp a.isLt
      simp only [Finset.mem_univ, true_and]
      omega
    rw [this, card_Ioc_fin (p / 2) tK (p / 2) le_rfl]
  have hQcard : (S.filter (fun a : Fin (p / 2 + 1) => lN p n a % 2 = 1)).card = tN - tK := by
    have : S.filter (fun a : Fin (p / 2 + 1) => lN p n a % 2 = 1) =
        univ.filter (fun a : Fin (p / 2 + 1) => tK < (a : ℕ) ∧ (a : ℕ) ≤ tN) := by
      ext a
      rw [Finset.mem_filter, Finset.mem_filter]
      simp only [Finset.mem_univ, true_and]
      constructor
      · rintro ⟨haS, ho⟩
        exact ⟨(hSmem a).1 haS, (hNodd a haS).1 ho⟩
      · rintro ⟨h1, h2⟩
        have haS := (hSmem a).2 h1
        exact ⟨haS, (hNodd a haS).2 h2⟩
    rw [this, card_Ioc_fin (p / 2) tK tN htNm]
  -- the ε-part
  obtain ⟨hsub, hcard, hprop⟩ := H.epsSet_spec
  set ec := (S.filter (fun a => a ∈ eps)).card with hecdef
  have hTop : (univ.filter (fun a : Fin (p / 2 + 1) => 0 < (a : ℕ) ∧ (a : ℕ) ≤ tK)).card = tK := by
    rw [card_Ioc_fin (p / 2) 0 tK htKm]; omega
  have hsplitE : ec + (eps.filter (fun a => a ∉ S)).card = innerE p n L0 := by
    rw [← hcard]
    have h := card_split eps (fun a => a ∈ S) (fun a => a ∉ S) (fun _ => True)
      (fun a _ => by tauto) (fun a _ h h' => h' h)
    rw [Finset.filter_true_of_mem (fun _ _ => trivial)] at h
    rw [← h]
    congr 1
    rw [hecdef, Finset.filter_mem_eq_inter, Finset.filter_mem_eq_inter, Finset.inter_comm]
  have hnotS : eps.filter (fun a => a ∉ S) ⊆
      univ.filter (fun a : Fin (p / 2 + 1) => 0 < (a : ℕ) ∧ (a : ℕ) ≤ tK) := by
    intro a ha
    rw [Finset.mem_filter] at ha ⊢
    have ha0 : a ≠ 0 := (Finset.mem_erase.mp (hsub ha.1)).1
    obtain ⟨h1, _⟩ := hval a ha0
    have := (hSmem a).not.mp ha.2
    exact ⟨Finset.mem_univ _, by omega, by omega⟩
  have hnotS_le : (eps.filter (fun a => a ∉ S)).card ≤ tK := by
    rw [← hTop]; exact Finset.card_le_card hnotS
  have hec_E : ec ≤ innerE p n L0 := by omega
  have hec_S : ec ≤ p / 2 - tK := by
    rw [← hScard]; exact Finset.card_filter_le _ _
  -- the counts in `kpar`
  set A0 := (S.filter (fun a : Fin (p / 2 + 1) => lN p n a % 2 = 0 ∧ a ∈ eps)).card with hA0
  set X := (S.filter (fun a : Fin (p / 2 + 1) => lN p n a % 2 = 1 ∧ a ∈ eps)).card with hX
  set B := (S.filter (fun a : Fin (p / 2 + 1) => lN p n a % 2 = 1 ∧ a ∉ eps)).card with hB
  set A1 := (S.filter (fun a : Fin (p / 2 + 1) => lN p n a % 2 = 0 ∧ a ∉ eps)).card with hA1
  set B1 := (S.filter (fun a : Fin (p / 2 + 1) => lN p n a % 2 = 1 ∧ a ∈ eps ∧
    0 < innerL p n L0 a)).card with hB1
  have e1 : A0 + X = ec := by
    refine card_split S (fun a : Fin (p / 2 + 1) => lN p n a % 2 = 0 ∧ a ∈ eps)
      (fun a : Fin (p / 2 + 1) => lN p n a % 2 = 1 ∧ a ∈ eps) (fun a => a ∈ eps) ?_ ?_
    · intro a _
      constructor
      · rintro (⟨_, h⟩ | ⟨_, h⟩) <;> exact h
      · intro h
        rcases Nat.mod_two_eq_zero_or_one (lN p n a) with h' | h'
        · exact Or.inl ⟨h', h⟩
        · exact Or.inr ⟨h', h⟩
    · intro a _ h h'
      have := h.1; have := h'.1; omega
  have e2 : X + B = tN - tK := by
    rw [← hQcard]
    exact card_split S _ _ _ (fun a _ => by tauto) (fun a _ h h' => by tauto)
  have e3 : A0 + A1 + (tN - tK) = p / 2 - tK := by
    rw [← hQcard, ← hScard]
    have h0 : A0 + A1 = (S.filter (fun a : Fin (p / 2 + 1) => lN p n a % 2 = 0)).card :=
      card_split S _ _ _ (fun a _ => by tauto) (fun a _ h h' => by tauto)
    rw [h0]
    have h := card_split S (fun a : Fin (p / 2 + 1) => lN p n a % 2 = 0) (fun a : Fin (p / 2 + 1) => lN p n a % 2 = 1) (fun _ => True)
      (fun a _ => by simp only [iff_true]; omega) (fun a _ h h' => by omega)
    rw [Finset.filter_true_of_mem (fun _ _ => trivial)] at h
    exact h
  have e4 : B1 ≤ X := by
    apply Finset.card_le_card
    intro a ha
    rw [Finset.mem_filter] at ha ⊢
    exact ⟨ha.1, ha.2.1, ha.2.2.1⟩
  refine ⟨ec, ?_, ?_, hec_E, hec_S, by omega, ?_, ?_⟩
  · intro hT
    unfold kpar
    rw [if_neg (by omega)]
    rw [← hSdef, ← hepsdef]
    rw [← hA0, ← hB]
    push_cast
    omega
  · intro hT
    unfold kpar
    rw [if_pos hT]
    rw [← hSdef, ← hepsdef]
    rw [← hA1, ← hB1]
    push_cast
    omega
  · intro hvm hpos
    -- some class of `S` carries an extra row; then all top classes do
    obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
    rw [Finset.mem_filter] at ha
    have hall : univ.filter (fun a : Fin (p / 2 + 1) => 0 < (a : ℕ) ∧ (a : ℕ) ≤ tK) ⊆
        eps.filter (fun a => a ∉ S) := by
      intro c hc
      rw [Finset.mem_filter] at hc ⊢
      have hc0 : c ≠ 0 := hne c (by omega)
      have hcS : c ∉ S := fun h => by have := (hSmem c).1 h; omega
      refine ⟨?_, hcS⟩
      by_contra hce
      have := hprop a ha.2 c (Finset.mem_erase.mpr ⟨hc0, Finset.mem_univ _⟩) hce
      have ha0 : a ≠ 0 := hne a (by have := (hSmem a).1 ha.1; omega)
      obtain ⟨a1, a2⟩ := hval a ha0
      obtain ⟨c1, c2⟩ := hval c hc0
      rw [hlK a ha0, hlK c hc0] at this
      rw [(aCnt_spec hm hv c1 c2).1 hc.2.2, (aCnt_spec hm hv a1 a2).2 ((hSmem a).1 ha.1),
        if_pos hvm] at this
      omega
    have := Finset.card_le_card hall
    rw [hTop] at this
    omega
  · intro hvm hlt
    -- some class of `S` has no extra row; then every extra class lies in `S`
    have hex : ∃ c ∈ S, c ∉ eps := by
      by_contra hc
      push Not at hc
      have : S.filter (fun a => a ∈ eps) = S := Finset.filter_true_of_mem hc
      rw [← hScard] at hlt
      rw [hecdef, this] at hlt
      exact lt_irrefl _ hlt
    obtain ⟨c, hcS, hce⟩ := hex
    have hempty : eps.filter (fun a => a ∉ S) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro a ha haS
      have hc0 : c ≠ 0 := hne c (by have := (hSmem c).1 hcS; omega)
      have ha0 : a ≠ 0 := (Finset.mem_erase.mp (hsub ha)).1
      have := hprop a ha c (Finset.mem_erase.mpr ⟨hc0, Finset.mem_univ _⟩) hce
      obtain ⟨a1, a2⟩ := hval a ha0
      obtain ⟨c1, c2⟩ := hval c hc0
      have haT : (a : ℕ) ≤ tK := by have := (hSmem a).not.mp haS; omega
      rw [hlK a ha0, hlK c hc0] at this
      rw [(aCnt_spec hm hv a1 a2).1 haT, (aCnt_spec hm hv c1 c2).2 ((hSmem c).1 hcS),
        if_neg (by omega)] at this
      omega
    rw [hempty, Finset.card_empty] at hsplitE
    omega

end

/-! ### The comparison with `g_ref` -/

/-- The real comparison, on abstract data. -/
lemma kpar_core {x P mR ER Δ Sc Qc ec kp L0 tK : ℝ} {g T : ℤ} {vlo : Prop}
    (hP : 0 < P) (hmP : 2 * mR + 1 = P) (hg : gT x = g)
    (hrel : mR * ((g : ℝ) - T) = Δ + ER - mR * (2 * gu x))
    (hev : T % 2 = 0 → ec - Qc - L0 ≤ kp) (hod : T % 2 = 1 → Sc - Qc - ec - L0 ≤ kp)
    (hk0 : 0 ≤ kp) (hec0 : 0 ≤ ec) (hecE : ec ≤ ER) (hecS : ec ≤ Sc) (hEtK : ER ≤ tK + ec)
    (h4 : vlo → 0 < ec → tK + ec ≤ ER) (h5 : ¬ vlo → ec < Sc → ec = ER)
    (hER0 : 0 ≤ ER) (hERm : ER < mR) (htK0 : 0 ≤ tK)
    (hte1 : vlo → P * tri x = tK) (hte2 : ¬ vlo → P * tri x = tK + 1)
    (hSc : Sc = mR - tK) (hQgq : Qc ≤ P * gq x + 1)
    (hge : Int.fract x < 1 / 2 ↔ vlo)
    (hΔ0 : 0 < Δ) (hΔm : Δ < mR) (hL0 : 0 ≤ L0) :
    P * gref x ≤ kp + Δ + L0 + 3 := by
  have hu0 := gu_bounds x
  have hm0 : 0 < mR := by linarith
  have hd : g = T ∨ g = T + 1 := by
    have hlo : (-1 : ℝ) < (g : ℝ) - T := by
      by_contra hc; push Not at hc
      have : mR * ((g : ℝ) - T) ≤ -mR := by nlinarith
      nlinarith
    have hhi : (g : ℝ) - T < 2 := by
      by_contra hc; push Not at hc
      have : 2 * mR ≤ mR * ((g : ℝ) - T) := by nlinarith
      nlinarith
    have hlo' : (-1 : ℤ) < g - T := by
      have : ((-1 : ℤ) : ℝ) < ((g - T : ℤ) : ℝ) := by push_cast; exact hlo
      exact_mod_cast this
    have hhi' : g - T < 2 := by
      have : ((g - T : ℤ) : ℝ) < ((2 : ℤ) : ℝ) := by push_cast; exact hhi
      exact_mod_cast this
    omega
  have hgs : P * gs x = mR + 1 / 2 - P * tri x := by unfold gs; rw [← hmP]; ring
  have hgsS : Sc ≤ P * gs x + 1 / 2 ∧ P * gs x ≤ Sc + 1 / 2 := by
    rw [hgs, hSc]
    by_cases hv : vlo
    · rw [hte1 hv]; constructor <;> linarith
    · rw [hte2 hv]; constructor <;> linarith
  have hPu : P * gu x = 2 * mR * gu x + gu x := by rw [← hmP]; ring
  have hPgq0 : 0 ≤ P * gq x := mul_nonneg hP.le (gq_nonneg x)
  have hPte0 : 0 ≤ P * tri x := mul_nonneg hP.le (tri_nonneg x)
  have hge_lo : vlo → ge x = max 0 (gu x - tri x) := fun h => by
    unfold ge; rw [if_pos (hge.2 h)]
  have hge_hi : ¬ vlo → ge x = min (gu x) (gs x) := fun h => by
    unfold ge; rw [if_neg (fun h' => h (hge.1 h'))]
  unfold gref
  rw [hg]
  rcases hd with hd | hd
  · -- `T = ⌊23x/10⌋`
    subst hd
    rw [sub_self, mul_zero] at hrel
    split_ifs with hpar
    · have hk := hev hpar
      rw [mul_max_of_nonneg _ _ hP.le, mul_zero, mul_sub]
      apply max_le (by linarith)
      by_cases hvm : vlo
      · rw [hge_lo hvm, mul_max_of_nonneg _ _ hP.le, mul_zero, mul_sub, hte1 hvm]
        have : max 0 (P * gu x - tK) ≤ ec + Δ + 1 :=
          max_le (by linarith) (by nlinarith)
        linarith
      · rw [hge_hi hvm]
        have : P * min (gu x) (gs x) ≤ ec + Δ + 1 := by
          rcases lt_or_ge ec Sc with hlt | hge'
          · have e := h5 hvm hlt
            have := mul_le_mul_of_nonneg_left (min_le_left (gu x) (gs x)) hP.le
            nlinarith
          · have := mul_le_mul_of_nonneg_left (min_le_right (gu x) (gs x)) hP.le
            linarith [hgsS.2]
        linarith
    · have hTo : g % 2 = 1 := by omega
      have hk := hod hTo
      rw [mul_max_of_nonneg _ _ hP.le, mul_zero, mul_sub, mul_sub]
      apply max_le (by linarith)
      by_cases hvm : vlo
      · rw [hge_lo hvm]
        have hlow : ec ≤ P * max 0 (gu x - tri x) + Δ + 1 := by
          rcases lt_or_ge 0 ec with hpos | h0
          · have e := h4 hvm hpos
            have := mul_le_mul_of_nonneg_left (le_max_right 0 (gu x - tri x)) hP.le
            rw [mul_sub, hte1 hvm] at this
            nlinarith
          · have := mul_nonneg hP.le (le_max_left 0 (gu x - tri x))
            linarith
        linarith [hgsS.1, hgsS.2]
      · rw [hge_hi hvm]
        have hlow : ec ≤ P * min (gu x) (gs x) + Δ + 1 := by
          rcases min_choice (gu x) (gs x) with e | e <;> rw [e]
          · nlinarith
          · linarith [hgsS.1]
        linarith [hgsS.1, hgsS.2]
  · -- `T = ⌊23x/10⌋ − 1`
    subst hd
    have hrel' : ER = mR - Δ + mR * (2 * gu x) := by push_cast at hrel; linarith
    have hPu_small : P * gu x < Δ + 1 / 2 := by nlinarith
    split_ifs with hpar
    · rw [mul_max_of_nonneg _ _ hP.le, mul_zero]
      apply max_le (by linarith)
      have hgeu : ge x ≤ gu x := by
        unfold ge
        split_ifs
        · exact max_le hu0.1 (by have := tri_nonneg x; linarith)
        · exact min_le_left _ _
      have := mul_le_mul_of_nonneg_left hgeu hP.le
      have := mul_nonneg hP.le (gq_nonneg x)
      nlinarith
    · have hTe : T % 2 = 0 := by omega
      have hk := hev hTe
      rw [mul_max_of_nonneg _ _ hP.le, mul_zero, mul_sub, mul_sub]
      apply max_le (by linarith)
      have hge0 : 0 ≤ P * ge x := mul_nonneg hP.le (ge_bounds x).1
      have h2u : 0 ≤ mR * (2 * gu x) := by nlinarith
      have hSec : Sc ≤ ec + Δ := by
        by_cases hvm : vlo
        · rw [hSc]; linarith
        · rcases lt_or_ge ec Sc with hlt | hge'
          · have e := h5 hvm hlt
            rw [hSc]; linarith
          · linarith
      linarith [hgsS.1]

lemma fract_div_nat (N p : ℕ) (hp : 0 < p) :
    Int.fract ((N : ℝ) / p) = ((N % p : ℕ) : ℝ) / p := by
  have hP : (0 : ℝ) < p := by exact_mod_cast hp
  rw [Int.fract_eq_iff]
  refine ⟨by positivity, ?_, ((N / p : ℕ) : ℤ), ?_⟩
  · rw [div_lt_one hP]; exact_mod_cast Nat.mod_lt N hp
  · have h : (N : ℝ) = p * ((N / p : ℕ) : ℝ) + ((N % p : ℕ) : ℝ) := by
      exact_mod_cast (Nat.div_add_mod N p).symm
    rw [h, Int.cast_natCast]; field_simp <;> ring

lemma p_tri_div (N p : ℕ) (hp : 0 < p) :
    (p : ℝ) * tri ((N : ℝ) / p) =
      if N % p ≤ p / 2 then ((N % p : ℕ) : ℝ) else p - ((N % p : ℕ) : ℝ) := by
  have hP : (0 : ℝ) < p := by exact_mod_cast hp
  unfold tri
  rw [fract_div_nat N p hp]
  split_ifs with h
  · have h2 : (2 : ℝ) * ((N % p : ℕ) : ℝ) ≤ p := by
      exact_mod_cast (by omega : 2 * (N % p) ≤ p)
    rw [min_eq_left (by rw [le_sub_iff_add_le, ← add_div, div_le_one hP]; linarith)]
    field_simp
  · have h2 : (p : ℝ) ≤ 2 * ((N % p : ℕ) : ℝ) := by
      exact_mod_cast (by omega : p ≤ 2 * (N % p))
    rw [min_eq_right (by rw [sub_le_iff_le_add, ← add_div, one_le_div hP]; linarith)]
    field_simp

lemma thr_cast (p v : ℕ) (hv : v < p) :
    ((thr p v : ℕ) : ℝ) = if v ≤ p / 2 then (v : ℝ) else p - v - 1 := by
  unfold thr
  split_ifs with h
  · rfl
  · have : p - v - 1 + v + 1 = p := by omega
    have h' : ((p - v - 1 : ℕ) : ℝ) + v + 1 = p := by exact_mod_cast this
    linarith

section
variable {p n M L0 : ℕ}

/-- **ZC27.** The parity gain counts at least `p · g_ref(K/p) − 30 M` classes. -/
theorem kpar_ge (H : InnerHyp p n M L0) :
    (p : ℝ) * gref (((40 * n : ℕ) : ℝ) / p) - 30 * M ≤ kpar p n L0 := by
  obtain ⟨ec, hev, hod, h1, h2, h3, h4, h5⟩ := kpar_int H
  have hm := H.p_odd
  have hpp : 0 < p := H.prime.pos
  have hv : 40 * n % p < p := Nat.mod_lt _ hpp
  have hw : 3 * n % p < p := Nat.mod_lt _ hpp
  have hTot := H.tot_eq
  have hE := H.E_lt
  have hb := H.mN_lt
  have hp200 := H.p200
  have hM := H.hM
  have hL0a := H.hL0a
  have hL0b := H.hL0b
  have hpM := H.hpM
  have hb3 : 3 * n / p ≤ 3 * n := Nat.div_le_self _ _
  have hL37 : L0 ≤ 37 * n := by nlinarith [H.hK]
  have htKm : thr p (40 * n % p) ≤ p / 2 := thr_le hm hv
  have hm100 : 100 * M ≤ p / 2 := by omega
  have hP : (0 : ℝ) < p := by exact_mod_cast hpp
  have hmP : 2 * ((p / 2 : ℕ) : ℝ) + 1 = p := by exact_mod_cast hm
  have hal : (al : ℝ) = 3 / 40 := rfl
  have hax : (al : ℝ) * (((40 * n : ℕ) : ℝ) / p) = ((3 * n : ℕ) : ℝ) / p := by
    rw [hal]; push_cast; ring
  -- the triangle values against the thresholds
  have hte := p_tri_div (40 * n) p hpp
  have htn := p_tri_div (3 * n) p hpp
  have htKc := thr_cast p (40 * n % p) hv
  have htNc := thr_cast p (3 * n % p) hw
  have hPgq1 : (p : ℝ) * tri ((al : ℝ) * (((40 * n : ℕ) : ℝ) / p)) -
      p * tri (((40 * n : ℕ) : ℝ) / p) ≤ p * gq (((40 * n : ℕ) : ℝ) / p) := by
    unfold gq; rw [← mul_sub]; exact mul_le_mul_of_nonneg_left (le_max_right _ _) hP.le
  have hPgq0 : 0 ≤ (p : ℝ) * gq (((40 * n : ℕ) : ℝ) / p) := mul_nonneg hP.le (gq_nonneg _)
  rw [hax] at hPgq1
  have hQgq : (((thr p (3 * n % p) - thr p (40 * n % p) : ℕ) : ℕ) : ℝ) ≤
      p * gq (((40 * n : ℕ) : ℝ) / p) + 1 := by
    by_cases h : thr p (40 * n % p) ≤ thr p (3 * n % p)
    · rw [Nat.cast_sub h]
      split_ifs at hte htn htKc htNc <;> linarith
    · rw [Nat.sub_eq_zero_of_le (by omega), Nat.cast_zero]; linarith
  -- the totals
  have htot : ((p / 2 : ℕ) : ℝ) * (innerT p n L0 : ℝ) + (innerE p n L0 : ℝ) =
      46 * n - L0 - 3 * ((3 * n / p : ℕ) : ℝ) := by
    have e : ((p / 2 * innerT p n L0 + innerE p n L0 : ℕ) : ℝ) = (innerTot p n L0 : ℝ) := by
      exact_mod_cast hTot
    unfold innerTot at e
    push_cast [Nat.cast_sub hL37, Nat.cast_sub hb3] at e
    linarith
  have hkey : ((p / 2 : ℕ) : ℝ) * ((23 / 10 : ℝ) * (((40 * n : ℕ) : ℝ) / p)) =
      46 * n - 46 * n / p := by
    have : ((p / 2 : ℕ) : ℝ) = ((p : ℝ) - 1) / 2 := by linarith
    rw [this]; push_cast; field_simp; ring
  have hbM : ((3 * n / p : ℕ) : ℝ) + 1 ≤ M := by exact_mod_cast hb
  have hb0 : (0 : ℝ) ≤ ((3 * n / p : ℕ) : ℝ) := Nat.cast_nonneg _
  have hMR : (40 : ℝ) ≤ M := by exact_mod_cast hM
  have hL0aR : 2 * (M : ℝ) ≤ L0 := by exact_mod_cast hL0a
  have hL0bR : (L0 : ℝ) ≤ 13 * M + 10 := by exact_mod_cast hL0b
  have hm100R : 100 * (M : ℝ) ≤ ((p / 2 : ℕ) : ℝ) := by exact_mod_cast hm100
  have hnP : 46 * (n : ℝ) / p < 2 * M := by
    have h1' : (40 : ℝ) * n < p * M := by exact_mod_cast hpM
    rw [div_lt_iff₀ hP]; nlinarith
  have hnP0 : 0 ≤ 46 * (n : ℝ) / p := by positivity
  have hgu : gu (((40 * n : ℕ) : ℝ) / p) =
      23 / 20 * (((40 * n : ℕ) : ℝ) / p) - (gT (((40 * n : ℕ) : ℝ) / p) : ℝ) / 2 := rfl
  have hmain := kpar_core (x := ((40 * n : ℕ) : ℝ) / p) (P := p) (mR := ((p / 2 : ℕ) : ℝ))
    (ER := (innerE p n L0 : ℝ)) (Δ := L0 + 3 * ((3 * n / p : ℕ) : ℝ) - 46 * n / p)
    (Sc := ((p / 2 - thr p (40 * n % p) : ℕ) : ℝ))
    (Qc := ((thr p (3 * n % p) - thr p (40 * n % p) : ℕ) : ℝ)) (ec := (ec : ℝ))
    (kp := (kpar p n L0 : ℝ)) (L0 := (L0 : ℝ)) (tK := ((thr p (40 * n % p) : ℕ) : ℝ))
    (g := gT (((40 * n : ℕ) : ℝ) / p)) (T := (innerT p n L0 : ℤ))
    (vlo := 40 * n % p ≤ p / 2) hP hmP rfl
    (by
      rw [hgu, show (((innerT p n L0 : ℕ) : ℤ) : ℝ) = (innerT p n L0 : ℝ) from Int.cast_natCast _]
      linear_combination -htot + hkey)
    (fun hT => by
      have : innerT p n L0 % 2 = 0 := by omega
      have := hev this
      exact_mod_cast this)
    (fun hT => by
      have : innerT p n L0 % 2 = 1 := by omega
      have := hod this
      exact_mod_cast this)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by exact_mod_cast h1) (by exact_mod_cast h2)
    (by exact_mod_cast h3)
    (fun hv' hpos => by
      have := h4 hv' (by exact_mod_cast hpos)
      exact_mod_cast this)
    (fun hv' hlt => by
      have := h5 (by omega) (by exact_mod_cast hlt)
      exact_mod_cast this)
    (Nat.cast_nonneg _) (by exact_mod_cast hE) (Nat.cast_nonneg _)
    (fun hv' => by rw [hte, if_pos hv', htKc, if_pos hv'])
    (fun hv' => by rw [hte, if_neg hv', htKc, if_neg hv']; ring)
    (by rw [Nat.cast_sub htKm]) hQgq
    (by
      rw [fract_div_nat (40 * n) p hpp, div_lt_iff₀ hP]
      constructor
      · intro h
        by_contra hc
        have : (p : ℝ) ≤ 2 * ((40 * n % p : ℕ) : ℝ) := by exact_mod_cast (by omega : p ≤ 2 * (40 * n % p))
        linarith
      · intro h
        have : (2 : ℝ) * ((40 * n % p : ℕ) : ℝ) < p := by exact_mod_cast (by omega : 2 * (40 * n % p) < p)
        linarith)
    (by linarith) (by linarith) (Nat.cast_nonneg _)
  linarith

end

end Apery
