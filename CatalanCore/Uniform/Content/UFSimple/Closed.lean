module

public import CatalanCore.Uniform.Content.UFSimple.Cell

@[expose] public section

/-!
# UF simplification (H18): the closed UF price and the uniform UF layer

**Theorem C (Lean form).** For a two-term frame, the alternating geometry, an even `r`, a prime
`p` and the pole residue `ρ` (`p ∣ q ρ - o`, `1 ≤ ρ < p`), write `r = A + s` with
`A = p ⌊r/p⌋`.  The four joint types `(k, z) ∈ {h, h+1} × {0, 1}` give the candidates

  `B = A` or `A + p`,  `ℓ = 0` or `ρ`,  `u_z = ρ - 1` or `p - 1`,
  `ū = u_z` (k = h) or `min u_z (s - 1)` (k = h + 1),

with selected window `[max r (B+ℓ), B+ū]` and credited residue window `[B+ℓ, B+ū]` (top
extension included).  `candPrice` is `closedBound` of a candidate whose `J` is nonempty and the
trivial `2(r+m)` otherwise; `closedPrice` is the minimum of the four.

`exists_datum_closed`: a `SmithJKDatum` with price `≤ closedPrice` exists at every such `(r, p)`.
`ufClosedLayer`: the UF `DebitLayer` (debit 1) with base `closedPrice`, for ANY two-term bank.
No family, cover, polygon, kill certificate or data table enters.
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.UFMoments
  CatalanCore.Uniform.Content.UFWedge CatalanCore.Uniform.Content.Smith
  CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.UFWire
  CatalanCore.Uniform.Content.Member CatalanCore.Uniform.Content.UFFamily3

namespace CatalanCore.Uniform.Content.UFSimple

variable {c : ℚ} {hc : 0 < c} {Fr : Frame} {q o : ℕ}

/-- No singular index strictly inside a block-bit window `(B + ℓ, B + u]`. -/
theorem noSing_blk (T : TwoTermData Fr q o) {p B ℓ uz ρ : ℕ} [Fact p.Prime] (hqp : q < p)
    (hB : p ∣ B) (huz : uz < p) (hρ : p ∣ q * ρ - o) (hρ1 : 1 ≤ ρ) (hρp : ρ < p)
    (hout : ρ ≤ ℓ ∨ uz < ρ) :
    ∀ k : ℕ, B + ℓ < k → k ≤ B + uz → ¬ ttSing p q o (k : ℤ) := by
  intro k hk1 hk2 hs
  have hp := (Fact.out : p.Prime)
  rw [ttSing_nat T (by omega)] at hs
  obtain ⟨b, rfl⟩ := hB
  rcases hs with hs | hs
  · obtain ⟨j, hj⟩ := hs
    have h1 : b < j := by
      rcases Nat.lt_or_ge b j with h | h
      · exact h
      · have := Nat.mul_le_mul_left p h; omega
    have h2 : j < b + 1 := by
      rcases Nat.lt_or_ge j (b + 1) with h | h
      · exact h
      · have := Nat.mul_le_mul_left p h; rw [Nat.mul_add] at this; omega
    omega
  · have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
    have hoq := T.o_lt
    have ho := T.o_pos
    have e1 : (((q * k - o : ℕ)) : ℤ) = q * k - o := by
      have h' : q ≤ q * k := Nat.le_mul_of_pos_right q (by omega)
      have : o ≤ q * k := by omega
      push_cast [this]; ring
    have e2 : (((q * ρ - o : ℕ)) : ℤ) = q * ρ - o := by
      have h' : q ≤ q * ρ := Nat.le_mul_of_pos_right q hρ1
      have : o ≤ q * ρ := by omega
      push_cast [this]; ring
    have d1 := Int.natCast_dvd_natCast.2 hs
    have d2 := Int.natCast_dvd_natCast.2 hρ
    rw [e1] at d1
    rw [e2] at d2
    have d3 : (p : ℤ) ∣ (q : ℤ) * ((k : ℤ) - (p * b + ρ : ℕ)) := by
      have d4 : (p : ℤ) ∣ (q : ℤ) * (p * b) := ⟨q * b, by ring⟩
      have := dvd_sub (dvd_sub d1 d2) d4
      have e : (q : ℤ) * k - o - (q * ρ - o) - q * (p * b) = (q : ℤ) * ((k : ℤ) - (p * b + ρ : ℕ)) := by
        push_cast; ring
      rwa [e] at this
    rcases hpp.dvd_or_dvd d3 with hq' | hq'
    · have := Int.le_of_dvd (by exact_mod_cast (by omega : 0 < q)) hq'
      have : (q : ℤ) < p := by exact_mod_cast hqp
      omega
    · have := eq_of_dvd_window (p := p) (a := p * b) (b := p * b + (p - 1)) (k := k)
        (k' := p * b + ρ) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega) hq'
      omega

/-- The bundled hypotheses of the closed UF layer at `(r, p)`. -/
structure ClosedHyp (c : ℚ) (hc : 0 < c) (Fr : Frame) (q o r p ρ : ℕ) [Fact p.Prime] : Prop where
  hr2 : r % 2 = 0
  hr0 : 0 < r
  hm1 : 1 ≤ (altGeom c hc).borderSize r
  hNp : r + p < p * p
  hpm : 2 * (altGeom c hc).borderSize r ≤ p
  hp2 : 2 < p
  hq0 : 0 < q
  hqp : q < p
  hsq : ∀ t, 1 ≤ t → t < r + p → ¬ p ^ 2 ∣ q * t - o
  hnorm : Fr.norm ∈ S p
  hnorm0 : red p Fr.norm ≠ 0
  hρ : p ∣ q * ρ - o
  hρ1 : 1 ≤ ρ
  hρp : ρ < p

set_option maxHeartbeats 1600000 in
/-- **The generic candidate**: a datum of price `closedBound` from the linear facts. -/
theorem exists_datum_gen (T : TwoTermData Fr q o) {r p m B L ℓ uz ub ρ : ℕ} [Fact p.Prime]
    (H : ClosedHyp c hc Fr q o r p ρ) (hbs : (altGeom c hc).borderSize r = m)
    (hBL : B = L * p) (huz : uz < p) (hub : ub ≤ uz)
    (hok1 : max r (B + ℓ) < r + 2 * m) (hok2 : max r (B + ℓ) ≤ B + ub)
    (htvp : B + ub < r + p) (hR : r + 2 * m ≤ B + ℓ + 2 * p) (hrB : B + ℓ < r → r < B + p)
    (hS : p ∣ (B + ℓ) ∨ p ∣ q * (B + ℓ) - o) (hE : p ∣ (B + uz + 1) ∨ p ∣ q * (B + uz + 1) - o)
    (hubR : B + ub + 1 < r + 2 * m → ub = uz)
    (hnos : ∀ k : ℕ, B + ℓ < k → k ≤ B + uz → ¬ ttSing p q o (k : ℤ)) :
    ∃ X : SmithJKDatum (altGeom c hc) Fr r p,
      X.price ≤ closedBound m r p (max r (B + ℓ)) (B + ub) (B + ℓ) := by
  have hpm := H.hpm
  rw [hbs] at hpm
  have hp0 : 0 < p := by have := H.hp2; omega
  have hdivL : ∀ x, B ≤ x → x < B + p → x / p = L := by
    intro x h1 h2
    apply Nat.div_eq_of_lt_le
    · rw [← hBL]; exact h1
    · rw [Nat.add_mul, one_mul, ← hBL]; exact h2
  have W : WinC c hc q o r p (r + p) (max r (B + ℓ)) (B + ub) (B + ℓ) m :=
    { hr2 := H.hr2
      hr0 := H.hr0
      hbs := hbs
      hrN := by omega
      hNp := H.hNp
      hpm := hpm
      hp2 := H.hp2
      hq0 := H.hq0
      hqp := H.hqp
      ho0 := T.o_pos
      hop := by have := T.o_lt; have := H.hqp; omega
      hw0 := le_max_right _ _
      ht0r := le_max_left _ _
      ht0b := hok1
      ht0tv := hok2
      htvp := htvp
      htvN := htvp
      hdiv := by
        rw [hdivL (B + ub) (by omega) (by omega), hdivL (max r (B + ℓ)) (by omega) (by omega)]
      hwin := by omega
      hR := hR
      hsepL := by
        intro v hv1 hv2
        refine ⟨B + ℓ, by omega, by omega, hS⟩
      hsepR := by
        intro v hv1 hv2
        have := hubR (by omega)
        refine ⟨B + uz + 1, by omega, by omega, hE⟩ }
  have hsing : NoSingWin (twoTermPoleData T W.hNp.le H.hsq H.hnorm H.hnorm0) (max r (B + ℓ))
      (B + ub - max r (B + ℓ)) := by
    intro k hk1 hk2
    exact hnos k (by omega) (by omega)
  by_cases hext : B + ℓ < r
  · have ht0 : max r (B + ℓ) = r := max_eq_left hext.le
    have hqd : (B + ℓ) / p = r / p := by
      rw [hdivL (B + ℓ) (by omega) (by omega), hdivL r (by omega) (hrB hext)]
    have hwd : NoSingWin (twoTermPoleData T W.hNp.le H.hsq H.hnorm H.hnorm0) (B + ℓ)
        (r - (B + ℓ)) := by
      intro k hk1 hk2
      exact hnos k hk1 (by omega)
    refine ⟨(cellExt T W ht0 hext hqd H.hsq H.hnorm H.hnorm0 hsing hwd).datum, ?_⟩
    rw [← cellExt_bound T W ht0 hext hqd H.hsq H.hnorm H.hnorm0 hsing hwd]
    exact UFCellF.price_le _
  · have hw : B + ℓ = max r (B + ℓ) := (max_eq_right (by omega)).symm
    refine ⟨(cellNo T W hw H.hsq H.hnorm H.hnorm0 hsing).datum, ?_⟩
    rw [← cellNo_bound T W hw H.hsq H.hnorm H.hnorm0 hsing]
    exact Cell3.price_le _


/-- Block start of the candidate (`k = h + κ`). -/
def candB (r p : ℕ) (κ : Bool) : ℕ := if κ then p * (r / p) + p else p * (r / p)
/-- Bit start `ℓ_z`. -/
def candL (ρ : ℕ) (ζ : Bool) : ℕ := if ζ then ρ else 0
/-- Bit end `u_z`. -/
def candU (p ρ : ℕ) (ζ : Bool) : ℕ := if ζ then p - 1 else ρ - 1
/-- Credited end `ū`. -/
def candUb (r p ρ : ℕ) (κ ζ : Bool) : ℕ := if κ then min (candU p ρ ζ) (r % p - 1) else candU p ρ ζ

/-- The candidate's `J` is nonempty (and `s ≥ 1` for `k = h + 1`). -/
def CandOK (m r p ρ : ℕ) (κ ζ : Bool) : Prop :=
  max r (candB r p κ + candL ρ ζ) < r + 2 * m ∧
    max r (candB r p κ + candL ρ ζ) ≤ candB r p κ + candUb r p ρ κ ζ ∧ (κ = true → 1 ≤ r % p)

instance (m r p ρ : ℕ) (κ ζ : Bool) : Decidable (CandOK m r p ρ κ ζ) := by
  unfold CandOK; infer_instance

/-- The price of the candidate `(k, z) = (h + κ, ζ)`. -/
def candPrice (m r p ρ : ℕ) (κ ζ : Bool) : ℕ :=
  if CandOK m r p ρ κ ζ then
    closedBound m r p (max r (candB r p κ + candL ρ ζ)) (candB r p κ + candUb r p ρ κ ζ)
      (candB r p κ + candL ρ ζ)
  else 2 * (r + m)

/-- **The closed UF price**: the best of the four joint-type candidates. -/
def closedPrice (m r p ρ : ℕ) : ℕ :=
  min (min (candPrice m r p ρ false false) (candPrice m r p ρ false true))
    (min (candPrice m r p ρ true false) (candPrice m r p ρ true true))

theorem closedBound_le (m r p t0 tv w0 : ℕ) : closedBound m r p t0 tv w0 ≤ 2 * (r + m) :=
  Nat.sub_le _ _

theorem pole_dvd {p q o B ρ : ℕ} (hB : p ∣ B) (hρ : p ∣ q * ρ - o) (hρ1 : 1 ≤ ρ) (hoq : o < q) :
    p ∣ q * (B + ρ) - o := by
  have h1 : q ≤ q * ρ := Nat.le_mul_of_pos_right q hρ1
  have e : q * (B + ρ) - o = q * B + (q * ρ - o) := by rw [Nat.mul_add]; omega
  rw [e]
  exact Nat.dvd_add (Dvd.dvd.mul_left hB q) hρ

set_option maxHeartbeats 1600000 in
/-- Every OK candidate has a datum of its closed price. -/
theorem exists_datum_cand (T : TwoTermData Fr q o) {r p ρ : ℕ} [Fact p.Prime]
    (H : ClosedHyp c hc Fr q o r p ρ) (κ ζ : Bool)
    (hok : CandOK ((altGeom c hc).borderSize r) r p ρ κ ζ) :
    ∃ X : SmithJKDatum (altGeom c hc) Fr r p,
      X.price ≤ candPrice ((altGeom c hc).borderSize r) r p ρ κ ζ := by
  rw [candPrice, if_pos hok]
  have hpm := H.hpm
  have hp0 : 0 < p := by have := H.hp2; omega
  have hAs : p * (r / p) + r % p = r := Nat.div_add_mod r p
  have hs : r % p < p := Nat.mod_lt r hp0
  have hA : p ∣ p * (r / p) := Dvd.intro _ rfl
  have hAp : p ∣ p * (r / p) + p := Nat.dvd_add hA (dvd_refl p)
  have hoq := T.o_lt
  have hρ := H.hρ
  have hρ1 := H.hρ1
  have hρp := H.hρp
  have hm1 := H.hm1
  obtain ⟨hok1, hok2, hok3⟩ := hok
  cases κ <;> cases ζ <;>
    simp only [candB, candL, candU, candUb, Bool.false_eq_true, eq_self_iff_true, if_true,
      if_false, ↓reduceIte] at hok1 hok2 ⊢
  · -- (h, 0)
    refine exists_datum_gen T H rfl (L := r / p) (uz := ρ - 1) (by rw [Nat.mul_comm])
      (by omega) le_rfl hok1 hok2 (by omega) (by omega) (fun _ => by omega)
      (Or.inl (by simpa using hA)) (Or.inr ?_) (fun _ => rfl)
      (noSing_blk T H.hqp hA (by omega) hρ hρ1 hρp (Or.inr (by omega)))
    have e : p * (r / p) + (ρ - 1) + 1 = p * (r / p) + ρ := by omega
    rw [e]; exact pole_dvd hA hρ hρ1 hoq
  · -- (h, 1)
    refine exists_datum_gen T H rfl (L := r / p) (uz := p - 1) (by rw [Nat.mul_comm])
      (by omega) le_rfl hok1 hok2 (by omega) (by omega) (fun _ => by omega)
      (Or.inr (pole_dvd hA hρ hρ1 hoq)) (Or.inl ?_) (fun _ => rfl)
      (noSing_blk T H.hqp hA (by omega) hρ hρ1 hρp (Or.inl le_rfl))
    have e : p * (r / p) + (p - 1) + 1 = p * (r / p) + p := by omega
    rw [e]; exact hAp
  · -- (h + 1, 0)
    have hs1 := hok3 rfl
    refine exists_datum_gen T H rfl (L := r / p + 1) (uz := ρ - 1) (by ring)
      (by omega) (min_le_left _ _) hok1 hok2 (by omega) (by omega) (fun h => by omega)
      (Or.inl (by simpa using hAp)) (Or.inr ?_) (fun h => by omega)
      (noSing_blk T H.hqp hAp (by omega) hρ hρ1 hρp (Or.inr (by omega)))
    have e : p * (r / p) + p + (ρ - 1) + 1 = p * (r / p) + p + ρ := by omega
    rw [e]; exact pole_dvd hAp hρ hρ1 hoq
  · -- (h + 1, 1)
    have hs1 := hok3 rfl
    refine exists_datum_gen T H rfl (L := r / p + 1) (uz := p - 1) (by ring)
      (by omega) (min_le_left _ _) hok1 hok2 (by omega) (by omega) (fun h => by omega)
      (Or.inr (pole_dvd hAp hρ hρ1 hoq)) (Or.inl ?_) (fun h => by omega)
      (noSing_blk T H.hqp hAp (by omega) hρ hρ1 hρp (Or.inl le_rfl))
    have e : p * (r / p) + p + (p - 1) + 1 = p * (r / p) + p + p := by omega
    rw [e]; exact Nat.dvd_add hAp (dvd_refl p)

/-- The joint type of the first border node `r` is always an OK candidate. -/
theorem candOK_first {r p ρ m : ℕ} (hp0 : 0 < p) (hm1 : 1 ≤ m) (hρ1 : 1 ≤ ρ) (hρp : ρ < p) :
    CandOK m r p ρ false (decide (ρ ≤ r % p)) := by
  have hAs : p * (r / p) + r % p = r := Nat.div_add_mod r p
  have hs : r % p < p := Nat.mod_lt r hp0
  unfold CandOK
  by_cases h : ρ ≤ r % p
  · rw [decide_eq_true h]
    simp only [candB, candL, candUb, candU, Bool.false_eq_true, eq_self_iff_true, if_true,
      if_false, ↓reduceIte]
    exact ⟨by omega, by omega, by simp⟩
  · rw [decide_eq_false h]
    simp only [candB, candL, candUb, candU, Bool.false_eq_true, eq_self_iff_true, if_true,
      if_false, ↓reduceIte]
    exact ⟨by omega, by omega, by simp⟩

set_option maxHeartbeats 1600000 in
/-- **Theorem C.** A UF datum of price at most the closed price exists. -/
theorem exists_datum_closed (T : TwoTermData Fr q o) {r p ρ : ℕ} [Fact p.Prime]
    (H : ClosedHyp c hc Fr q o r p ρ) :
    ∃ X : SmithJKDatum (altGeom c hc) Fr r p,
      X.price ≤ closedPrice ((altGeom c hc).borderSize r) r p ρ := by
  have hp0 : 0 < p := by have := H.hp2; omega
  obtain ⟨X0, hX0⟩ := exists_datum_cand T H false (decide (ρ ≤ r % p))
    (candOK_first hp0 H.hm1 H.hρ1 H.hρp)
  have hX0' : X0.price ≤ 2 * (r + (altGeom c hc).borderSize r) := by
    refine hX0.trans ?_
    unfold candPrice
    split_ifs
    · exact closedBound_le _ _ _ _ _ _
    · exact le_rfl
  have hall : ∀ κ ζ : Bool, ∃ X : SmithJKDatum (altGeom c hc) Fr r p,
      X.price ≤ candPrice ((altGeom c hc).borderSize r) r p ρ κ ζ := by
    intro κ ζ
    by_cases hok : CandOK ((altGeom c hc).borderSize r) r p ρ κ ζ
    · exact exists_datum_cand T H κ ζ hok
    · exact ⟨X0, by rw [candPrice, if_neg hok]; exact hX0'⟩
  unfold closedPrice
  rcases min_choice (min (candPrice ((altGeom c hc).borderSize r) r p ρ false false)
      (candPrice ((altGeom c hc).borderSize r) r p ρ false true))
      (min (candPrice ((altGeom c hc).borderSize r) r p ρ true false)
      (candPrice ((altGeom c hc).borderSize r) r p ρ true true)) with h | h <;> rw [h]
  · rcases min_choice (candPrice ((altGeom c hc).borderSize r) r p ρ false false)
      (candPrice ((altGeom c hc).borderSize r) r p ρ false true) with h' | h' <;> rw [h']
    · exact hall false false
    · exact hall false true
  · rcases min_choice (candPrice ((altGeom c hc).borderSize r) r p ρ true false)
      (candPrice ((altGeom c hc).borderSize r) r p ρ true true) with h' | h' <;> rw [h']
    · exact hall true false
    · exact hall true true

/-- **The uniform UF layer** of any two-term bank: base `closedPrice`, debit 1 (Theorem SD).
The bank supplies only its validity region and the pole residue `ρ p` (`p ∣ q ρ - o`). -/
noncomputable def ufClosedLayer {depth : ℕ} (T : TwoTermData Fr q o) (valid : ℕ → ℕ → Prop)
    (ρ : ℕ → ℕ) (hv : ∀ r p : ℕ, ∀ [Fact p.Prime], valid r p → ClosedHyp c hc Fr q o r p (ρ p)) :
    DebitLayer (altGeom c hc) Fr depth :=
  smithJKLayer valid (fun r p => closedPrice ((altGeom c hc).borderSize r) r p (ρ p))
    (fun r p _ h => Classical.choose (exists_datum_closed T (hv r p h)))
    (fun r p _ h => Classical.choose_spec (exists_datum_closed T (hv r p h)))

theorem ufClosedLayer_base {depth : ℕ} (T : TwoTermData Fr q o) (valid : ℕ → ℕ → Prop)
    (ρ : ℕ → ℕ) (hv : ∀ r p : ℕ, ∀ [Fact p.Prime], valid r p → ClosedHyp c hc Fr q o r p (ρ p)) :
    (ufClosedLayer (depth := depth) T valid ρ hv).base =
      fun r p => closedPrice ((altGeom c hc).borderSize r) r p (ρ p) := rfl

theorem ufClosedLayer_valid {depth : ℕ} (T : TwoTermData Fr q o) (valid : ℕ → ℕ → Prop)
    (ρ : ℕ → ℕ) (hv : ∀ r p : ℕ, ∀ [Fact p.Prime], valid r p → ClosedHyp c hc Fr q o r p (ρ p)) :
    (ufClosedLayer (depth := depth) T valid ρ hv).valid = valid := rfl

end CatalanCore.Uniform.Content.UFSimple
