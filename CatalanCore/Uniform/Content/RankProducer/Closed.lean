module

public import CatalanCore.Uniform.Content.RankProducer.ClosedPrice
public import CatalanCore.Uniform.Content.RankProducer.ClosedPalette
public import CatalanCore.Uniform.Content.BankShared.Reindex
public import CatalanCore.Uniform.Content.Smith.TwoTerm

@[expose] public section
set_option Elab.async false

/-! # The generic closed rank layer (Theorem R of C2/PAPER.md, lane C2L)

**Theorem R (Lean form).**  Let `Fr` be a frame with a two-pole digamma presentation (`TwoPole`:
pole `1` with coefficient `c0`, pole `(q-o)/q` with coefficient `c1`, any signs, any normalisation)
on `altGeom c`.  At every `(r, p)` of the validity region `RankHyp` (`r` even, `2m < p`,
`q (r + 2m) < p²`, `NFr < p`, digits `≤ K`, UF's pole residue `ρ`) and for every retained set,
there is a certificate `RankMember` of price at most

  `rankPrice m r p ρ = 2(r+m) - max(m + nsq, W(0,0) + W(1,0) + 2 nsq, W'(h,z), W'(h+1,z))`.

`rankPoleLayer`: the rank `DebitLayer` with base `rankPrice` and debit `0`.
`rankClosedLayer`: the same for ANY frame with `TwoTermData Fr q o` (the input of
`UFSimple.ufClosedLayer`), through the canonical frame `ttFrame` with the same `Mn`.

The bound `NFr` comes from the existence route of Lemma 3 (`exists_normal`): it is a definite
natural number, but it is not computed; no determinant is evaluated.
-/

namespace CatalanCore.Uniform.Content.RankProducer
open Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Uniform
  CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.Member
  CatalanCore.Uniform.Content.Wire CatalanCore.Uniform.Content.Shape
  CatalanCore.Uniform.Content.Smith
open scoped Classical

/-- A two-pole digamma presentation `(u, q)` of a frame: pole `1` at `j1`, pole `(qq-o)/qq` at
`j2`.  The coefficients `w j / norm` are arbitrary. -/
structure TwoPole (Fr : Frame) (u q : Fin Fr.d → ℕ) (qq o : ℕ) where
  j1 : Fin Fr.d
  j2 : Fin Fr.d
  hne : j1 ≠ j2
  hall : ∀ j, j = j1 ∨ j = j2
  hu1 : u j1 = 1
  hq1 : q j1 = 1
  hq2 : q j2 = qq
  hu2 : u j2 = qq - o
  ho : 0 < o
  hoq : o < qq

/-- **The bound `N_Fr`** of Theorem R: the class bounds `clsBnd` of every class `(j, k, z)`,
`j < qq`, `k ≤ K`, and the coefficient denominators. -/
noncomputable def NFr (c0 c1 : ℚ) (qq K : ℕ) : ℕ :=
  3 + qq + c0.den + c1.den + ∑ j ∈ range qq, ∑ k ∈ range (K + 1),
    (clsBnd (ttL c0 c1 qq j false) (ttE c0 c1 qq j false) k false +
      clsBnd (ttL c0 c1 qq j true) (ttE c0 c1 qq j true) k true)

/-- **The validity region of Theorem R** at `(r, p)`, with UF's pole residue `ρ`. -/
structure RankHyp (c : ℚ) (hc : 0 < c) (qq o N K r p ρ : ℕ) : Prop where
  hr2 : r % 2 = 0
  hr0 : 0 < r
  hpm : 2 * (altGeom c hc).borderSize r < p
  hB : qq * (r + 2 * (altGeom c hc).borderSize r) < p ^ 2
  hN : N < p
  hK : (r + 2 * (altGeom c hc).borderSize r) / p ≤ K
  hρ : p ∣ qq * ρ - o
  hρ1 : 1 ≤ ρ
  hρp : ρ < p

theorem clsBnd_le_NFr (c0 c1 : ℚ) (qq K j k : ℕ) (z : Bool) (hj : j < qq) (hk : k ≤ K) :
    clsBnd (ttL c0 c1 qq j z) (ttE c0 c1 qq j z) k z ≤ NFr c0 c1 qq K := by
  have h1 : clsBnd (ttL c0 c1 qq j z) (ttE c0 c1 qq j z) k z ≤
      clsBnd (ttL c0 c1 qq j false) (ttE c0 c1 qq j false) k false +
        clsBnd (ttL c0 c1 qq j true) (ttE c0 c1 qq j true) k true := by
    cases z <;> omega
  have h2 := Finset.single_le_sum (f := fun k => clsBnd (ttL c0 c1 qq j false)
      (ttE c0 c1 qq j false) k false + clsBnd (ttL c0 c1 qq j true) (ttE c0 c1 qq j true) k true)
    (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (show k < K + 1 by omega))
  have h3 := Finset.single_le_sum (f := fun j => ∑ k ∈ range (K + 1),
      (clsBnd (ttL c0 c1 qq j false) (ttE c0 c1 qq j false) k false +
        clsBnd (ttL c0 c1 qq j true) (ttE c0 c1 qq j true) k true))
    (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hj)
  unfold NFr
  omega

section Wit
variable (Fr : Frame) (u q : Fin Fr.d → ℕ) {qq o : ℕ} (P : TwoPole Fr u q qq o)
  (c0 c1 : ℚ) (hc0 : (frameDigamma Fr u q).c P.j1 = c0)
  (hc1 : (frameDigamma Fr u q).c P.j2 = c1)

include hc0 hc1 in
/-- The band facts of a `RankMember` (coefficients, denominators, compact band). -/
theorem closed_band (p : ℕ) [hp : Fact p.Prime] (B : ℕ) (hqp : qq < p)
    (hc0p : c0.den < p) (hc1p : c1.den < p) (hBq : qq * (B + 1) < p ^ 2) :
    (∀ j, (frameDigamma Fr u q).c j ∈ S p) ∧ (∀ j, ¬ p ∣ (frameDigamma Fr u q).q j) ∧
      (∀ j, (frameDigamma Fr u q).q j * B + (frameDigamma Fr u q).u j ≤ p ^ 2) ∧
      B < p ^ 2 := by
  have hq0 : 0 < qq := by have := P.ho; have := P.hoq; omega
  have hmul : B + 1 ≤ qq * (B + 1) := Nat.le_mul_of_pos_left _ hq0
  refine ⟨fun j => ?_, fun j => ?_, fun j => ?_, by omega⟩
  · rcases P.hall j with rfl | rfl
    · rw [hc0]; exact rational_mem_of_den_lt p c0 hc0p
    · rw [hc1]; exact rational_mem_of_den_lt p c1 hc1p
  · rcases P.hall j with rfl | rfl
    · show ¬ p ∣ q P.j1
      rw [P.hq1]; exact hp.out.not_dvd_one
    · show ¬ p ∣ q P.j2
      rw [P.hq2]; exact Nat.not_dvd_of_pos_of_lt hq0 hqp
  · rcases P.hall j with rfl | rfl
    · show q P.j1 * B + u P.j1 ≤ p ^ 2
      rw [P.hq1, P.hu1]; omega
    · show q P.j2 * B + u P.j2 ≤ p ^ 2
      rw [P.hq2, P.hu2]
      have : qq * B + qq = qq * (B + 1) := by ring
      omega

include hc0 hc1 in
/-- The fibre palette of the two-pole frame at a prime, in the class `j = (qq ρ - o) / p`. -/
theorem closed_palette (p : ℕ) [hp : Fact p.Prime] (ρ : ℕ) (hqp : qq < p) (hρ : p ∣ qq * ρ - o)
    (hρ1 : 1 ≤ ρ) (hρp : ρ < p) :
    ∀ x0 < p, ∀ d, (frameDigamma Fr u q).Lf p (x0 + p * d) =
        ttL c0 c1 qq ((qq * ρ - o) / p) (decide (ρ ≤ x0)) d ∧
      (frameDigamma Fr u q).E p (x0 + p * d) =
        ttE c0 c1 qq ((qq * ρ - o) / p) (decide (ρ ≤ x0)) d := by
  intro x0 hx0 d
  have hq0 : 0 < qq := by have := P.ho; have := P.hoq; omega
  have hqρ : qq ≤ qq * ρ := Nat.le_mul_of_pos_right qq hρ1
  have hw : qq * (ρ - 1) + (qq - o) = p * ((qq * ρ - o) / p) := by
    rw [Nat.mul_div_cancel' hρ, Nat.mul_sub_one]
    have := P.hoq
    omega
  have hdec : decide (ρ - 1 < x0) = decide (ρ ≤ x0) := decide_eq_decide.2 (by omega)
  have h := twoPole_LfE (frameDigamma Fr u q) P.j1 P.j2 P.hne P.hall P.hu1 P.hq1 P.hq2 P.hu2 hq0
    p (Nat.not_dvd_of_pos_of_lt hq0 hqp) (ρ - 1) ((qq * ρ - o) / p) (by omega) hw x0 d hx0
  rw [hc0, hc1, hdec] at h
  exact h

end Wit

/-- The class index `(qq ρ - o) / p` is `< qq`. -/
theorem class_lt {qq o p ρ : ℕ} (hp : 0 < p) (hq0 : 0 < qq) (hρ : p ∣ qq * ρ - o)
    (hρp : ρ < p) : (qq * ρ - o) / p < qq := by
  have h1 : qq * ρ < qq * p := Nat.mul_lt_mul_of_pos_left hρp hq0
  have e : p * ((qq * ρ - o) / p) = qq * ρ - o := Nat.mul_div_cancel' hρ
  have h2 : p * ((qq * ρ - o) / p) < p * qq := by
    rw [e, Nat.mul_comm p qq]; omega
  exact Nat.lt_of_mul_lt_mul_left h2

/-- **Theorem R at one member and one prime**, on any hybrid-shaped geometry with border size `m`. -/
theorem closed_wit_core {G : BlockGeom} {r : ℕ} (hs : HybShape G r)
    (T : Finset (G.geometry r).C) (Fr : Frame) (u q : Fin Fr.d → ℕ) {qq o : ℕ}
    (P : TwoPole Fr u q qq o) (c0 c1 : ℚ) (hc0 : (frameDigamma Fr u q).c P.j1 = c0)
    (hc1 : (frameDigamma Fr u q).c P.j2 = c1) (K : ℕ) (p : ℕ) [hp : Fact p.Prime] (ρ m : ℕ)
    (hk : (G.geometry r).k = m) (hr0 : 0 < r) (hpm : 2 * m < p)
    (hB : qq * (r + 2 * m) < p ^ 2) (hN : NFr c0 c1 qq K < p) (hK : (r + 2 * m) / p ≤ K)
    (hρ : p ∣ qq * ρ - o) (hρ1 : 1 ≤ ρ) (hρp : ρ < p) :
    ∃ M : RankMember Fr u q (fun a : (G.geometry r).C => (a : ℕ)) (G.geometry r).xs
        (G.geometry r).ys T p, M.price ≤ rankPrice m r p ρ := by
  have hp0 := hp.out.pos
  have hN3 : 3 + qq + c0.den + c1.den ≤ NFr c0 c1 qq K := by unfold NFr; omega
  have hq0 : 0 < qq := by have := P.ho; have := P.hoq; omega
  have hB1 : qq * (r + 2 * m - 1 + 1) < p ^ 2 := by
    rw [show r + 2 * m - 1 + 1 = r + 2 * m by omega]; exact hB
  obtain ⟨hcoef, hpq, hbd, hBp⟩ := closed_band Fr u q P c0 c1 hc0 hc1 p (r + 2 * m - 1)
    (by omega) (by omega) (by omega) hB1
  have hpal := closed_palette Fr u q P c0 c1 hc0 hc1 p ρ (by omega) hρ hρ1 hρp
  have hjq := class_lt hp0 hq0 hρ hρp
  have hBr : r + 2 * (G.geometry r).k ≤ r + 2 * m - 1 + 1 := by rw [hk]; omega
  have hpm' : 2 * (G.geometry r).k < p := by rw [hk]; exact hpm
  have hBnd : ∀ (kk : ℕ) (z : Bool), kk ≤ (r + 2 * (G.geometry r).k) / p →
      clsBnd (ttL c0 c1 qq ((qq * ρ - o) / p) z) (ttE c0 c1 qq ((qq * ρ - o) / p) z) kk z < p := by
    intro kk z hkk
    rw [hk] at hkk
    exact lt_of_le_of_lt (clsBnd_le_NFr c0 c1 qq K ((qq * ρ - o) / p) kk z hjq (le_trans hkk hK)) hN
  have key := exists_member_closed hs T Fr u q p (r + 2 * m - 1) hcoef hpq (by omega) hbd hBp hBr
    hpm' (fun z => ttL c0 c1 qq ((qq * ρ - o) / p) z) (fun z => ttE c0 c1 qq ((qq * ρ - o) / p) z)
    ρ hρ1 hρp (fun x0 hx0 d => (hpal x0 hx0 d).1) (fun x0 hx0 d => (hpal x0 hx0 d).2)
    (ttE_zero c0 c1 qq _) hBnd
  obtain ⟨M, hM⟩ := key
  exact ⟨M, hM.trans (le_of_eq (congrArg (fun x => rankPrice x r p ρ) hk))⟩

/-- **Theorem R at one member and one prime** on `altGeom c`. -/
theorem closed_wit (Fr : Frame) (u q : Fin Fr.d → ℕ) {qq o : ℕ} (P : TwoPole Fr u q qq o)
    (c0 c1 : ℚ) (hc0 : (frameDigamma Fr u q).c P.j1 = c0)
    (hc1 : (frameDigamma Fr u q).c P.j2 = c1) (K : ℕ) {c : ℚ} {hc : 0 < c} (r : ℕ)
    (T : Finset ((altGeom c hc).geometry r).C) (p : ℕ) [hp : Fact p.Prime] (ρ : ℕ)
    (H : RankHyp c hc qq o (NFr c0 c1 qq K) K r p ρ) :
    ∃ M : RankMember Fr u q (fun a : ((altGeom c hc).geometry r).C => (a : ℕ))
        ((altGeom c hc).geometry r).xs ((altGeom c hc).geometry r).ys T p,
      M.price ≤ rankPrice ((altGeom c hc).borderSize r) r p ρ :=
  closed_wit_core (altGeom_hybShape c hc H.hr2) T Fr u q P c0 c1 hc0 hc1 K p ρ
    ((altGeom c hc).borderSize r) (BankShared.geometry_k_eq_borderSize _ r) H.hr0 H.hpm H.hB H.hN
    H.hK H.hρ H.hρ1 H.hρp

/-- **The closed rank layer of a two-pole frame** (debit `0`, base `rankPrice`). -/
noncomputable def rankPoleLayer {c : ℚ} {hc : 0 < c} {depth : ℕ} (Fr : Frame)
    (u q : Fin Fr.d → ℕ) (hu : ∀ j, Fr.μ j = u j / q j) (hq : ∀ j, 0 < q j) {qq o : ℕ}
    (P : TwoPole Fr u q qq o) (c0 c1 : ℚ) (hc0 : (frameDigamma Fr u q).c P.j1 = c0)
    (hc1 : (frameDigamma Fr u q).c P.j2 = c1) (K : ℕ) (valid : ℕ → ℕ → Prop) (ρ : ℕ → ℕ)
    (hv : ∀ r p : ℕ, ∀ [Fact p.Prime], valid r p → RankHyp c hc qq o (NFr c0 c1 qq K) K r p (ρ p)) :
    DebitLayer (altGeom c hc) Fr depth :=
  DebitLayer.rank (altGeom c hc) Fr depth u q hu hq valid
    (fun r p => rankPrice ((altGeom c hc).borderSize r) r p (ρ p)) 0
    (fun i _ p _ hvp => by
      obtain ⟨M, hM⟩ := closed_wit Fr u q P c0 c1 hc0 hc1 K i.1 i.2 p (ρ p) (hv i.1 p hvp)
      exact ⟨M, by rw [zero_mul, add_zero]; exact hM⟩)

section Pole
variable {c : ℚ} {hc : 0 < c} {depth : ℕ} {Fr : Frame} {u q : Fin Fr.d → ℕ}
  {hu : ∀ j, Fr.μ j = u j / q j} {hq : ∀ j, 0 < q j} {qq o : ℕ} {P : TwoPole Fr u q qq o}
  {c0 c1 : ℚ} {hc0 : (frameDigamma Fr u q).c P.j1 = c0} {hc1 : (frameDigamma Fr u q).c P.j2 = c1}
  {K : ℕ} {valid : ℕ → ℕ → Prop} {ρ : ℕ → ℕ}
  {hv : ∀ r p : ℕ, ∀ [Fact p.Prime], valid r p → RankHyp c hc qq o (NFr c0 c1 qq K) K r p (ρ p)}

theorem rankPoleLayer_base :
    (rankPoleLayer (depth := depth) Fr u q hu hq P c0 c1 hc0 hc1 K valid ρ hv).base =
      fun r p => rankPrice ((altGeom c hc).borderSize r) r p (ρ p) := rfl

theorem rankPoleLayer_debit :
    (rankPoleLayer (depth := depth) Fr u q hu hq P c0 c1 hc0 hc1 K valid ρ hv).debit = 0 := rfl

theorem rankPoleLayer_valid :
    (rankPoleLayer (depth := depth) Fr u q hu hq P c0 c1 hc0 hc1 K valid ρ hv).valid = valid := rfl

end Pole

/-! ## Any frame with `TwoTermData`: the canonical frame and the transport -/

/-- The canonical two-term frame `ψ(z + 1) - ψ(z + (q-o)/q)` with normalisation `N`. -/
noncomputable def ttFrame (q o : ℕ) (ho : 0 < o) (hoq : o < q) (N : ℚ) (hN : 0 < N)
    (xs δ0 : ℚ) (n0off : ℕ) : Frame where
  d := 2
  μ := ![((q - o : ℕ) : ℚ) / q, 1]
  w := ![-1, 1]
  norm := N
  xs := xs
  δ0 := δ0
  n0off := n0off
  hμ := by
    have hq0 : (0 : ℚ) < q := by exact_mod_cast (show 0 < q by omega)
    have h1 : (0 : ℚ) < ((q - o : ℕ) : ℚ) := by exact_mod_cast (show 0 < q - o by omega)
    have h2 : ((q - o : ℕ) : ℚ) ≤ q := by exact_mod_cast (show q - o ≤ q by omega)
    intro i
    fin_cases i
    · exact ⟨div_pos h1 hq0, (div_le_one hq0).2 h2⟩
    · exact ⟨one_pos, le_rfl⟩
  hμinj := by
    have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
    have hne : ((q - o : ℕ) : ℚ) / q ≠ 1 := by
      intro h
      rw [div_eq_one_iff_eq hq0] at h
      have : q - o = q := by exact_mod_cast h
      omega
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hne
    · exact fun h => hne h.symm
    · exact absurd rfl hij
  hw := by simp [Fin.sum_univ_two]
  hnorm := hN

/-- Numerators of the canonical frame's shifts. -/
def ttU (q o : ℕ) : Fin 2 → ℕ := ![q - o, 1]
/-- Denominators of the canonical frame's shifts. -/
def ttQ (q : ℕ) : Fin 2 → ℕ := ![q, 1]

section TT
variable (q o : ℕ) (ho : 0 < o) (hoq : o < q) (N : ℚ) (hN : 0 < N) (xs δ0 : ℚ) (n0off : ℕ)

theorem ttFrame_hu :
    ∀ j : Fin 2, (ttFrame q o ho hoq N hN xs δ0 n0off).μ j = (ttU q o j : ℚ) / ttQ q j := by
  intro j
  fin_cases j
  · rfl
  · show (1 : ℚ) = ((1 : ℕ) : ℚ) / ((1 : ℕ) : ℚ)
    norm_num

theorem ttFrame_hq (hq : 0 < q) : ∀ j : Fin 2, 0 < ttQ q j := by
  intro j
  fin_cases j
  · exact hq
  · show 0 < 1; omega

/-- The canonical frame's two-pole presentation. -/
def ttPole : TwoPole (ttFrame q o ho hoq N hN xs δ0 n0off) (ttU q o) (ttQ q) q o where
  j1 := (1 : Fin 2)
  j2 := (0 : Fin 2)
  hne := by show (1 : Fin 2) ≠ (0 : Fin 2); decide
  hall := by
    intro j
    rcases j with ⟨v, hv⟩
    change v < 2 at hv
    interval_cases v
    · right; rfl
    · left; rfl
  hu1 := rfl
  hq1 := rfl
  hq2 := rfl
  hu2 := rfl
  ho := ho
  hoq := hoq

theorem ttFrame_c1 : (frameDigamma (ttFrame q o ho hoq N hN xs δ0 n0off) (ttU q o) (ttQ q)).c
    (ttPole q o ho hoq N hN xs δ0 n0off).j1 = 1 / N := by
  simp [frameDigamma, ttFrame, ttPole]

theorem ttFrame_c2 : (frameDigamma (ttFrame q o ho hoq N hN xs δ0 n0off) (ttU q o) (ttQ q)).c
    (ttPole q o ho hoq N hN xs δ0 n0off).j2 = -1 / N := by
  simp [frameDigamma, ttFrame, ttPole]

theorem ttFrame_twoTerm : TwoTermData (ttFrame q o ho hoq N hN xs δ0 n0off) q o where
  o_pos := ho
  o_lt := hoq
  delta_eq := by
    intro t ht
    have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
    have ht0 : (t : ℚ) ≠ 0 := by exact_mod_cast (show t ≠ 0 by omega)
    have hd0 : (q : ℚ) * t - o ≠ 0 := by
      have h1 : (o : ℚ) < q := by exact_mod_cast hoq
      have h2 : (1 : ℚ) ≤ t := by exact_mod_cast ht
      have h3 : (0 : ℚ) < q := by exact_mod_cast (show 0 < q by omega)
      nlinarith
    have e1 : (t : ℚ) - 1 + ((q - o : ℕ) : ℚ) / q = ((q : ℚ) * t - o) / q := by
      rw [Nat.cast_sub hoq.le]; field_simp; ring
    have e2 : (t : ℚ) - 1 + 1 = t := by ring
    show (∑ i : Fin 2, ((![-1, 1] : Fin 2 → ℤ) i : ℚ) /
        ((t : ℚ) - 1 + (![((q - o : ℕ) : ℚ) / q, 1] : Fin 2 → ℚ) i)) = _
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [e1, e2]
    push_cast
    field_simp
    ring
  dsq_eq := by
    intro t ht
    have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
    have ht0 : (t : ℚ) ≠ 0 := by exact_mod_cast (show t ≠ 0 by omega)
    have hd0 : (q : ℚ) * t - o ≠ 0 := by
      have h1 : (o : ℚ) < q := by exact_mod_cast hoq
      have h2 : (1 : ℚ) ≤ t := by exact_mod_cast ht
      have h3 : (0 : ℚ) < q := by exact_mod_cast (show 0 < q by omega)
      nlinarith
    have e1 : (t : ℚ) - 1 + ((q - o : ℕ) : ℚ) / q = ((q : ℚ) * t - o) / q := by
      rw [Nat.cast_sub hoq.le]; field_simp; ring
    have e2 : (t : ℚ) - 1 + 1 = t := by ring
    show (∑ i : Fin 2, ((![-1, 1] : Fin 2 → ℤ) i : ℚ) /
        ((t : ℚ) - 1 + (![((q - o : ℕ) : ℚ) / q, 1] : Fin 2 → ℚ) i) ^ 2) = _
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [e1, e2]
    push_cast
    field_simp
    ring

end TT

/-- Two frames with the same two-term data and normalisation have the same entries. -/
theorem mn_eq_of_twoTerm {Fr Fr' : Frame} {q o : ℕ} (T : TwoTermData Fr q o)
    (T' : TwoTermData Fr' q o) (hN : Fr.norm = Fr'.norm) (a b : ℕ) : Fr.Mn a b = Fr'.Mn a b := by
  unfold Frame.Mn
  have hD : ∀ k ∈ Ioc (min a b) (max a b), Fr.Delta k = Fr'.Delta k := fun k hk => by
    have : 1 ≤ k := by have := (Finset.mem_Ioc.1 hk).1; omega
    rw [T.delta_eq k this, T'.delta_eq k this]
  have hS : ∀ k ∈ Icc 1 a, Fr.Dsq k = Fr'.Dsq k := fun k hk => by
    have : 1 ≤ k := (Finset.mem_Icc.1 hk).1
    rw [T.dsq_eq k this, T'.dsq_eq k this]
  rw [Finset.sum_congr rfl hD, Finset.sum_congr rfl hS, hN]

/-- Frames with the same entries have the same member polynomials. -/
theorem polynomial_eq_of_mn {Fr Fr' : Frame} (h : ∀ a b, Fr.Mn a b = Fr'.Mn a b)
    (G : NodeFamily) (i : G.Index) : G.polynomial Fr i = G.polynomial Fr' i := by
  unfold NodeFamily.polynomial Rect.FullN Rect.blkA Rect.blkB Rect.blkC Rect.blkD
  simp only [h]

/-- A debit layer transfers between frames with the same entries. -/
def DebitLayer.ofMn {G : BlockGeom} {Fr Fr' : Frame} {depth : ℕ} (L : DebitLayer G Fr' depth)
    (h : ∀ a b, Fr.Mn a b = Fr'.Mn a b) : DebitLayer G Fr depth where
  base := L.base
  debit := L.debit
  valid := L.valid
  gle := fun i hi p _ hv => by
    have := L.gle i hi p hv
    show GLE p _ (NodeFamily.polynomial Fr G.geometry i)
    rw [polynomial_eq_of_mn h]
    exact this

/-- **The generic closed rank layer** of any frame with `TwoTermData Fr q o` (any member, any
normalisation): base `rankPrice`, debit `0`, valid on the region `RankHyp` with
`N = NFr (1/norm) (-1/norm) q K`.  The bank supplies its validity predicate, the digit bound `K`
and UF's pole residue `ρ p` (`p ∣ q ρ - o`). -/
noncomputable def rankClosedLayer {c : ℚ} {hc : 0 < c} {depth : ℕ} {Fr : Frame} {q o : ℕ}
    (T : TwoTermData Fr q o) (K : ℕ) (valid : ℕ → ℕ → Prop) (ρ : ℕ → ℕ)
    (hv : ∀ r p : ℕ, ∀ [Fact p.Prime], valid r p →
      RankHyp c hc q o (NFr (1 / Fr.norm) (-1 / Fr.norm) q K) K r p (ρ p)) :
    DebitLayer (altGeom c hc) Fr depth :=
  DebitLayer.ofMn
    (rankPoleLayer (ttFrame q o T.o_pos T.o_lt Fr.norm Fr.hnorm Fr.xs Fr.δ0 Fr.n0off)
      (ttU q o) (ttQ q) (ttFrame_hu q o T.o_pos T.o_lt Fr.norm Fr.hnorm Fr.xs Fr.δ0 Fr.n0off)
      (ttFrame_hq q (by have := T.o_pos; have := T.o_lt; omega))
      (ttPole q o T.o_pos T.o_lt Fr.norm Fr.hnorm Fr.xs Fr.δ0 Fr.n0off)
      (1 / Fr.norm) (-1 / Fr.norm)
      (ttFrame_c1 q o T.o_pos T.o_lt Fr.norm Fr.hnorm Fr.xs Fr.δ0 Fr.n0off)
      (ttFrame_c2 q o T.o_pos T.o_lt Fr.norm Fr.hnorm Fr.xs Fr.δ0 Fr.n0off) K valid ρ hv)
    (mn_eq_of_twoTerm T (ttFrame_twoTerm q o T.o_pos T.o_lt Fr.norm Fr.hnorm Fr.xs Fr.δ0 Fr.n0off)
      rfl)

section Closed
variable {c : ℚ} {hc : 0 < c} {depth : ℕ} {Fr : Frame} {q o : ℕ} (T : TwoTermData Fr q o) (K : ℕ)
  (valid : ℕ → ℕ → Prop) (ρ : ℕ → ℕ)
  (hv : ∀ r p : ℕ, ∀ [Fact p.Prime], valid r p →
    RankHyp c hc q o (NFr (1 / Fr.norm) (-1 / Fr.norm) q K) K r p (ρ p))

theorem rankClosedLayer_base : (rankClosedLayer (depth := depth) T K valid ρ hv).base =
    fun r p => rankPrice ((altGeom c hc).borderSize r) r p (ρ p) := rfl

theorem rankClosedLayer_debit : (rankClosedLayer (depth := depth) T K valid ρ hv).debit = 0 := rfl

theorem rankClosedLayer_valid : (rankClosedLayer (depth := depth) T K valid ρ hv).valid = valid :=
  rfl

end Closed

#print axioms rankPoleLayer
#print axioms rankClosedLayer
#print axioms rankClosedLayer_base
#print axioms rankClosedLayer_valid
end CatalanCore.Uniform.Content.RankProducer
