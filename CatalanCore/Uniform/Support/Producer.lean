module

public import CatalanCore.Uniform.Support.SeqFamily
public import CatalanCore.Uniform.Support.Datum
public import CatalanCore.Uniform.Content.BankShared.CrudeDet
public import CatalanCore.Uniform.Content.BankShared.AltCrude
public import CatalanCore.Uniform.Content.BankShared.KTerm.Content

@[expose] public section
set_option Elab.async false

/-!
# Producers for the Löwner family of two sequences (lane H, wave H2c; ledger S10, N3, N4)

* **S10 (Lemma 4.1, small primes).**  For a support datum every entry of the Löwner matrix of
  `(D.f, D.e)` between nodes `≤ N` is `p ^ (3 ⌊log_p N⌋ + 3 Dc D)`-integral for every prime `p`
  (`datum_lw_gle`), so every member of `seqFamily` at an even scale is `p ^ Ecrude (3 Dc D) r p`-integral
  (`datum_altQ`: the `AltQ` record, i.e. the degree bound and the crude clearing, which the content route
  needs of a family).
* **N4.**  `AltQ` for any two sequences from an entry bound (`seqPoly_gle_Ecrude`, the Blk-level analogue of
  `polynomial_gle_Ecrude`/`altGeom_gle_Ecrude`), and the `PreValidFam` producer `preValid_of_crude_rows`: the
  prefix bound on `p ≤ t0 r` from the crude clearing at the small primes `p² ≤ A r` and a level-free row price
  above them.
* **N3.**  The guard lemma of the plane 2 rows (`sweep_sq_guard`: a branch guard `p ≥ t r` with `p > N0`
  and `(N0 - 2) t ≥ 2 (1 + 2α)` gives `p² > 2 N + 2 p`), and `kcatValid_of_rows`: the `KCatValidFam` statement of
  a catalogue from row theorems (`RowThm`, in the form `GLE p (price + debit · del) (member)` under a guard)
  each realising a branch.
-/

open Polynomial Finset Matrix

namespace CatalanCore.Uniform.Support

open CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Rect CatalanCore.Uniform
  CatalanCore.Uniform.Content.BankShared CatalanCore.Uniform.Content.BankShared.Check
  CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.Shape
  CatalanCore.Uniform.Content.Member

/-! ### Entries of `seqFullN` -/

section Entries

variable {p : ℕ} [Fact p.Prime]
  {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Every entry of `seqFullN f g c xs ys X` is `p ^ e`-integral when every Löwner entry between nodes `≤ N`
is. -/
theorem seqFullN_entry_gle (f g : ℕ → ℚ) (c : ι → ℕ) (xs ys : κ → ℕ) {N e : ℕ}
    (hent : ∀ A B, A ≤ N → B ≤ N → GLE p e (C (lw f g A B)))
    (hc : ∀ a, c a ≤ N) (hx : ∀ i, xs i ≤ N) (hy : ∀ i, ys i ≤ N) (u v : ι ⊕ κ) :
    GLE p e (seqFullN f g c xs ys (X : ℚ[X]) u v) := by
  have hX : GLE p e (X : ℚ[X]) := GLE.X.mono (Nat.zero_le _)
  have hC : ∀ A B, A ≤ N → B ≤ N → GLE p e (algebraMap ℚ ℚ[X] (lw f g A B)) := hent
  rcases u with a | i <;> rcases v with b | j
  · simp only [seqFullN, Blk, Matrix.fromBlocks_apply₁₁, Matrix.add_apply, Matrix.smul_apply,
      Matrix.one_apply, Matrix.of_apply, smul_eq_mul]
    by_cases h : a = b
    · simp only [h, if_true, mul_one]
      exact (hC _ _ (hc b) (hc b)).add hX
    · simp only [h, if_false, mul_zero, add_zero]
      exact hC _ _ (hc a) (hc b)
  · simp only [seqFullN, Blk, Matrix.fromBlocks_apply₁₂, Matrix.of_apply]
    exact hC _ _ (hc a) (hy j)
  · simp only [seqFullN, Blk, Matrix.fromBlocks_apply₂₁, Matrix.of_apply]
    exact hC _ _ (hx i) (hc b)
  · simp only [seqFullN, Blk, Matrix.fromBlocks_apply₂₂, Matrix.of_apply]
    exact hC _ _ (hx i) (hy j)

/-- The determinant of `seqFullN` is `p ^ (size · e)`-integral. -/
theorem seqFullN_det_gle (f g : ℕ → ℚ) (c : ι → ℕ) (xs ys : κ → ℕ) {N e : ℕ}
    (hent : ∀ A B, A ≤ N → B ≤ N → GLE p e (C (lw f g A B)))
    (hc : ∀ a, c a ≤ N) (hx : ∀ i, xs i ≤ N) (hy : ∀ i, ys i ≤ N) :
    GLE p (Fintype.card (ι ⊕ κ) * e) (seqFullN f g c xs ys (X : ℚ[X])).det := by
  have h := det_gle (p := p) (seqFullN f g c xs ys (X : ℚ[X])) (fun _ _ => e)
    (seqFullN_entry_gle f g c xs ys hent hc hx hy)
  rwa [tropVal_const] at h

end Entries

/-- **Crude clearing of the member polynomials of two sequences** (the analogue of
`polynomial_gle_Ecrude`).  `cF` is the entry constant: every Löwner entry between nodes `≤ N` is
`p ^ (3 ⌊log_p N⌋ + cF)`-integral. -/
theorem seqPoly_gle_Ecrude (f g : ℕ → ℚ) (cF : ℕ)
    (hent : ∀ (p : ℕ) [Fact p.Prime] (N A B : ℕ), 0 < N → A ≤ N → B ≤ N →
      GLE p (3 * Nat.log p N + cF) (C (lw f g A B)))
    (G : NodeFamily) (i : G.Index)
    (hN : ∀ a ∈ (G i.1).C ∪ (G i.1).X' ∪ (G i.1).Y', a ≤ 14 * i.1)
    (hcard : i.2.card + (G i.1).k ≤ 2 * i.1) (p : ℕ) [Fact p.Prime] :
    GLE p (Ecrude cF i.1 p) (SeqFamily.poly f g G i) := by
  unfold SeqFamily.poly
  have hsz : Fintype.card (i.2 ⊕ Fin (G i.1).k) = i.2.card + (G i.1).k := by
    simp [Fintype.card_sum, Fintype.card_coe]
  rcases Nat.eq_zero_or_pos i.1 with h0 | hr
  · have hz : Fintype.card (i.2 ⊕ Fin (G i.1).k) = 0 := by omega
    have hE : IsEmpty (i.2 ⊕ Fin (G i.1).k) := Fintype.card_eq_zero_iff.1 hz
    rw [Matrix.det_isEmpty]
    exact (GLE.one (p := p)).mono (Nat.zero_le _)
  · have hNpos : 0 < 14 * i.1 := by omega
    have h := seqFullN_det_gle (p := p) f g (fun a : i.2 => ((a.1 : (G i.1).C) : ℕ))
      (G i.1).xs (G i.1).ys (N := 14 * i.1) (e := 3 * Nat.log p (14 * i.1) + cF)
      (fun A B hA hB => hent p (14 * i.1) A B hNpos hA hB)
      (fun a => hN _ (by
        have := a.1.2
        simp [this]))
      (fun j => hN _ (by
        have := Finset.orderEmbOfFin_mem (G i.1).X' rfl j
        simp [Rect.Geometry.xs, this]))
      (fun j => hN _ (by
        have := Finset.orderEmbOfFin_mem (G i.1).Y' (G i.1).card_eq.symm j
        simp [Rect.Geometry.ys, this]))
    refine h.mono ?_
    rw [hsz]
    unfold Ecrude
    calc (i.2.card + (G i.1).k) * (3 * Nat.log p (14 * i.1) + cF)
        ≤ (2 * i.1) * (3 * Nat.log p (14 * i.1) + cF) := Nat.mul_le_mul hcard le_rfl
      _ = 2 * i.1 * (3 * Nat.log p (14 * i.1) + cF) := rfl

/-- **`AltQ` for the Löwner minors of two sequences on `altGeom c`** from an entry bound. -/
theorem seq_altQ (c : ℚ) (hc : 0 < c) (hc1 : c ≤ 1) (f g : ℕ → ℚ) (cF : ℕ)
    (hent : ∀ (p : ℕ) [Fact p.Prime] (N A B : ℕ), 0 < N → A ≤ N → B ≤ N →
      GLE p (3 * Nat.log p N + cF) (C (lw f g A B))) :
    AltQ c hc cF (SeqFamily.poly f g (altGeom c hc).geometry) := by
  refine ⟨fun i => SeqFamily.poly_natDegree f g _ i, fun i hi p _ => ?_⟩
  have hbs := altGeom_borderSize_le c hc hc1 hi
  have hX := altGeom_X c hc hi
  have hY := altGeom_Y c hc hi
  have hC := altGeom_C c hc i.1
  have hk : ((altGeom c hc).geometry i.1).k = (altGeom c hc).borderSize i.1 :=
    geometry_k_eq_borderSize _ _
  refine seqPoly_gle_Ecrude f g cF hent (altGeom c hc).geometry i ?_ ?_ p
  · intro a ha
    simp only [Finset.mem_union] at ha
    rcases ha with (ha | ha) | ha
    · rw [hC, Finset.mem_range] at ha; omega
    · rw [hX, Finset.mem_image] at ha
      obtain ⟨j, hj, rfl⟩ := ha
      rw [Finset.mem_range] at hj; omega
    · rw [hY, Finset.mem_image] at ha
      obtain ⟨j, hj, rfl⟩ := ha
      rw [Finset.mem_range] at hj; omega
  · have h1 : i.2.card ≤ i.1 := by
      have := Finset.card_le_univ i.2
      have hc : ((altGeom c hc).geometry i.1).C.card = i.1 := by rw [hC, Finset.card_range]
      rw [Fintype.card_coe] at this
      omega
    omega

/-! ### S10: Lemma 4.1 for a datum -/

section DatumEntries

variable {p : ℕ} [hp : Fact p.Prime] (D : Datum)

/-- A positive constant dominating every `Dm (D.s i)`. -/
def Datum.Dc : ℕ := 1 + ∑ i, Dm (D.s i)

theorem Datum.Dc_pos : 0 < D.Dc := by unfold Datum.Dc; omega

theorem Datum.Dm_le_Dc (i : Fin D.n) : Dm (D.s i) ≤ D.Dc := by
  unfold Datum.Dc
  have := Finset.single_le_sum (f := fun j => Dm (D.s j)) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ i)
  omega

/-- `p ^ (⌊log_p N⌋ + Dc) / (k + s_i)` is `p`-integral for `k < N`. -/
theorem Datum.inv_shift_mem (i : Fin D.n) {N k : ℕ} (hN : 0 < N) (hk : k < N) :
    (p : ℚ) ^ (Nat.log p N + D.Dc) * (1 / ((k : ℚ) + D.s i)) ∈ LocRing p := by
  have hμ := (D.hs i).1
  have hk1 : 1 ≤ k + 1 := by omega
  have hn := shift_pos hμ hk1
  have hle : (k + 1 - 1) * (D.s i).den + (D.s i).num.toNat ≤ D.Dc * N :=
    (shift_le (k := k + 1) (N := N) (by omega) hk1).trans
      (Nat.mul_le_mul_right _ (D.Dm_le_Dc i))
  have h := inv_mem_D (p := p) D.Dc_pos hN hn hle
  have hse := shift_eq hμ hk1
  have hkq : (((k + 1 : ℕ) : ℚ) - 1 + D.s i) = (k : ℚ) + D.s i := by push_cast; ring
  rw [hkq] at hse
  rw [hse]
  have e : (p : ℚ) ^ (Nat.log p N + D.Dc) * (1 / ((((k + 1 - 1) * (D.s i).den + (D.s i).num.toNat : ℕ) : ℚ)
      / ((D.s i).den : ℚ))) = (((D.s i).den : ℕ) : ℤ) *
      ((p : ℚ) ^ (Nat.log p N + D.Dc) *
        (1 / ((((k + 1 - 1) * (D.s i).den + (D.s i).num.toNat : ℕ)) : ℚ))) := by
    rw [one_div_div]; push_cast; ring
  rw [e]
  exact (LocRing p).mul_mem (int_mem_locRing _) h

theorem Datum.pow_mem (N : ℕ) : (p : ℚ) ^ (Nat.log p N + D.Dc) ∈ LocRing p :=
  (LocRing p).pow_mem (by exact_mod_cast int_mem_locRing (ℓ := p) (p : ℤ)) _

theorem Datum.delta_mem {N k : ℕ} (hN : 0 < N) (hk : k < N) :
    (p : ℚ) ^ (2 * (Nat.log p N + D.Dc)) * D.delta k ∈ LocRing p := by
  unfold Datum.delta
  rw [Finset.mul_sum]
  refine (LocRing p).sum_mem fun i _ => ?_
  have h := D.inv_shift_mem (p := p) i hN hk
  have hP := D.pow_mem (p := p) N
  have e : (p : ℚ) ^ (2 * (Nat.log p N + D.Dc)) *
      ((D.a i : ℚ) / ((k : ℚ) + D.s i) - (D.b i : ℚ) / ((k : ℚ) + D.s i) ^ 2) =
      (D.a i : ℚ) * ((p : ℚ) ^ (Nat.log p N + D.Dc) *
        ((p : ℚ) ^ (Nat.log p N + D.Dc) * (1 / ((k : ℚ) + D.s i)))) -
      (D.b i : ℚ) * ((p : ℚ) ^ (Nat.log p N + D.Dc) * (1 / ((k : ℚ) + D.s i))) ^ 2 := by
    generalize (k : ℚ) + D.s i = x; ring
  rw [e]
  exact (LocRing p).sub_mem
    ((LocRing p).mul_mem (int_mem_locRing _) ((LocRing p).mul_mem hP h))
    ((LocRing p).mul_mem (int_mem_locRing _) ((LocRing p).pow_mem h 2))

theorem Datum.delta1_mem {N k : ℕ} (hN : 0 < N) (hk : k < N) :
    (p : ℚ) ^ (3 * (Nat.log p N + D.Dc)) * D.delta1 k ∈ LocRing p := by
  unfold Datum.delta1
  rw [Finset.mul_sum]
  refine (LocRing p).sum_mem fun i _ => ?_
  have h := D.inv_shift_mem (p := p) i hN hk
  have hP := D.pow_mem (p := p) N
  have e : (p : ℚ) ^ (3 * (Nat.log p N + D.Dc)) *
      (-(D.a i : ℚ) / ((k : ℚ) + D.s i) ^ 2 + 2 * (D.b i : ℚ) / ((k : ℚ) + D.s i) ^ 3) =
      -((D.a i : ℚ) * ((p : ℚ) ^ (Nat.log p N + D.Dc) *
        ((p : ℚ) ^ (Nat.log p N + D.Dc) * (1 / ((k : ℚ) + D.s i))) ^ 2)) +
      2 * (D.b i : ℚ) * ((p : ℚ) ^ (Nat.log p N + D.Dc) * (1 / ((k : ℚ) + D.s i))) ^ 3 := by
    generalize (k : ℚ) + D.s i = x; ring
  rw [e]
  have h2 : (2 : ℚ) ∈ LocRing p := by exact_mod_cast int_mem_locRing (ℓ := p) (2 : ℤ)
  exact (LocRing p).add_mem
    ((LocRing p).neg_mem ((LocRing p).mul_mem (int_mem_locRing _)
      ((LocRing p).mul_mem hP ((LocRing p).pow_mem h 2))))
    ((LocRing p).mul_mem ((LocRing p).mul_mem h2 (int_mem_locRing _)) ((LocRing p).pow_mem h 3))

/-- `f B - f A` for `A ≤ B ≤ N` is `p ^ (2 (⌊log_p N⌋ + Dc))`-integral. -/
theorem Datum.f_sub_mem {N A B : ℕ} (hN : 0 < N) (hAB : A ≤ B) (hB : B ≤ N) :
    (p : ℚ) ^ (2 * (Nat.log p N + D.Dc)) * (D.f B - D.f A) ∈ LocRing p := by
  have h : D.f B - D.f A = ∑ k ∈ Finset.Ico A B, D.delta k := by
    unfold Datum.f
    rw [Finset.sum_Ico_eq_sub _ hAB]
  rw [h, Finset.mul_sum]
  refine (LocRing p).sum_mem fun k hk => ?_
  rw [Finset.mem_Ico] at hk
  exact D.delta_mem hN (by omega)

/-- **S10 (Lemma 4.1).**  Every Löwner entry of the datum between nodes `≤ N` is
`p ^ (3 ⌊log_p N⌋ + 3 Dc)`-integral, for every prime `p`. -/
theorem datum_lw_gle {N A B : ℕ} (hN : 0 < N) (hA : A ≤ N) (hB : B ≤ N) :
    GLE p (3 * Nat.log p N + 3 * D.Dc) (C (lw D.f D.e A B)) := by
  rw [GLE.C_iff]
  have hoff : ∀ {A B : ℕ}, A < B → B ≤ N →
      (p : ℚ) ^ (3 * Nat.log p N + 3 * D.Dc) * ((D.f B - D.f A) / ((B : ℚ) - A)) ∈ LocRing p := by
    intro A B hAB hB
    have h1 := D.f_sub_mem (p := p) hN hAB.le hB
    have h2 := pow_mul_inv_mem (p := p) (n := B - A) (X := N) (by omega) (by omega)
    have h3 : (1 : ℚ) / (((B - A : ℕ)) : ℚ) = 1 / ((B : ℚ) - A) := by
      rw [Nat.cast_sub hAB.le]
    rw [h3] at h2
    have e : (p : ℚ) ^ (2 * (Nat.log p N + D.Dc) + Nat.log p N) * ((D.f B - D.f A) / ((B : ℚ) - A)) =
        ((p : ℚ) ^ (2 * (Nat.log p N + D.Dc)) * (D.f B - D.f A)) *
          ((p : ℚ) ^ (Nat.log p N) * (1 / ((B : ℚ) - A))) := by
      rw [pow_add]; ring
    refine mem_of_le (L := 2 * (Nat.log p N + D.Dc) + Nat.log p N) (by omega) ?_
    rw [e]
    exact (LocRing p).mul_mem h1 h2
  unfold lw
  split_ifs with hAB
  · subst hAB
    have h1 : -D.e A = ∑ k ∈ Finset.range A, D.delta1 k := by
      unfold Datum.e; ring
    rw [h1]
    refine mem_of_le (L := 3 * (Nat.log p N + D.Dc)) (by omega) ?_
    rw [Finset.mul_sum]
    refine (LocRing p).sum_mem fun k hk => ?_
    rw [Finset.mem_range] at hk
    exact D.delta1_mem hN (by omega)
  · rcases lt_or_gt_of_ne hAB with h | h
    · exact hoff h hB
    · have e : (D.f B - D.f A) / ((B : ℚ) - A) = (D.f A - D.f B) / ((A : ℚ) - B) := by
        have : (A : ℚ) - B ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hAB)
        have : (B : ℚ) - A ≠ 0 := sub_ne_zero.2 (Ne.symm (by exact_mod_cast hAB))
        field_simp
        ring
      rw [e]
      exact hoff h hA

end DatumEntries

/-- **S10/N4 for a datum.**  `AltQ` of the Löwner minors of the datum on `altGeom c`, `c ≤ 1`: the degree
bound and the crude clearing `p ^ Ecrude (3 Dc) r p`. -/
theorem datum_altQ (D : Datum) (c : ℚ) (hc : 0 < c) (hc1 : c ≤ 1) :
    AltQ c hc (3 * D.Dc) (SeqFamily.poly D.f D.e (altGeom c hc).geometry) :=
  seq_altQ c hc hc1 D.f D.e (3 * D.Dc) fun p _ N A B hN hA hB => datum_lw_gle D hN hA hB

/-! ### N4: the prefix bound -/

section Prefix

open CatalanCore.Uniform.Content.SmallPrimes

/-- `Ecrude` against the logarithmic budget of the small primes: for `1 ≤ r` and `2 ≤ p`,
`Ecrude cF r p ≤ C r (⌊log₂ r⌋ + 1)` when `30 + 2 cF ≤ C`. -/
theorem Ecrude_le_budget (cF C r p : ℕ) (hC : 30 + 2 * cF ≤ C) (hr : 1 ≤ r) (hp : 2 ≤ p) :
    Ecrude cF r p ≤ C * r * (Nat.log 2 r + 1) := by
  have h1 : r < 2 ^ (Nat.log 2 r + 1) := Nat.lt_pow_succ_log_self (by norm_num) r
  have h2 : 14 * r < 2 ^ (Nat.log 2 r + 1 + 4) := by
    calc 14 * r < 14 * 2 ^ (Nat.log 2 r + 1) := by omega
      _ ≤ 16 * 2 ^ (Nat.log 2 r + 1) := by omega
      _ = 2 ^ (Nat.log 2 r + 1 + 4) := by rw [pow_add]; ring
  have h3 : Nat.log 2 (14 * r) ≤ Nat.log 2 r + 4 := by
    have := Nat.log_lt_of_lt_pow (by omega) h2
    omega
  have h4 : Nat.log p (14 * r) ≤ Nat.log 2 (14 * r) := Nat.log_anti_left (by norm_num) hp
  unfold Ecrude
  have h5 : 3 * Nat.log p (14 * r) + cF ≤ 3 * (Nat.log 2 r + 4) + cF := by omega
  calc 2 * r * (3 * Nat.log p (14 * r) + cF) ≤ 2 * r * (3 * (Nat.log 2 r + 4) + cF) :=
        Nat.mul_le_mul_left _ h5
    _ = r * (6 * Nat.log 2 r + 24 + 2 * cF) := by ring
    _ ≤ r * (C * (Nat.log 2 r + 1)) := Nat.mul_le_mul_left _ (by nlinarith)
    _ = C * r * (Nat.log 2 r + 1) := by ring

/-- **N4: the `PreValidFam` producer.**  For a family with the crude clearing (`AltQ`), the prefix bound on
`p ≤ t0 r` (`t0 ≤ 1`) follows from the crude clearing at the small primes `p² ≤ A r`, paid by the
logarithmic budget `B`, and a row price `≤ α0b · r` above them (`hrow`: the level-free rows of the family).
The unit classes `¬ p ∣ M` are not used. -/
theorem preValid_of_crude_rows (c : ℚ) (hc : 0 < c) (const : ℝ) (depth : ℕ)
    (Q : NodeFamily.Index (altGeom c hc).geometry → ℚ[X]) {cF : ℕ} (hQ : AltQ c hc cF Q)
    (M : ℕ) (B : SmallBudget) (A C : ℕ) (hC : 30 + 2 * cF ≤ C)
    (hB : ∀ r p : ℕ, p * p ≤ A * r → p ≤ r → (C : ℝ) * r * ((Nat.log 2 r : ℝ) + 1) ≤ B.X r p)
    (t0 α0b : ℚ) (ht0 : t0 ≤ 1) (hα : 0 ≤ α0b)
    (hrow : ∀ i : (AltEvenFam c hc const depth Q).ι, (AltEvenFam c hc const depth Q).Adm i →
      ∀ (p : ℕ) [Fact p.Prime], A * i.1 < p * p → p ≤ i.1 →
        ∃ n, GLE p n ((AltEvenFam c hc const depth Q).Q i) ∧ (n : ℝ) ≤ (α0b : ℝ) * i.1) :
    PreValidFam c hc const depth Q M B t0 α0b := by
  intro i hi p _ _ hpt
  have hpr : p ≤ i.1 := by
    refine hpt.trans ?_
    have h0 : (0 : ℝ) ≤ i.1 := Nat.cast_nonneg _
    have : (t0 : ℝ) * i.1 ≤ i.1 := by
      have : (t0 : ℝ) ≤ 1 := by exact_mod_cast ht0
      nlinarith
    exact Nat.floor_le_of_le this
  have hr1 : 1 ≤ i.1 := by have := (Fact.out : p.Prime).two_le; omega
  have hX0 := B.nonneg i.1 p
  by_cases hsq : p * p ≤ A * i.1
  · refine ⟨Ecrude cF i.1 p, hQ.crude i hi.2 p, ?_⟩
    have h1 := Ecrude_le_budget cF C i.1 p hC hr1 (Fact.out : p.Prime).two_le
    have h2 : (Ecrude cF i.1 p : ℝ) ≤ (C : ℝ) * i.1 * ((Nat.log 2 i.1 : ℝ) + 1) := by
      exact_mod_cast (by simpa [mul_assoc] using h1 : Ecrude cF i.1 p ≤ C * i.1 * (Nat.log 2 i.1 + 1))
    have h3 := hB i.1 p hsq hpr
    have h4 : (0 : ℝ) ≤ (α0b : ℝ) * i.1 := by
      have : (0 : ℝ) ≤ (α0b : ℝ) := by exact_mod_cast hα
      positivity
    linarith
  · push Not at hsq
    obtain ⟨n, hn, hle⟩ := hrow i hi p hsq hpr
    exact ⟨n, hn, by linarith⟩

end Prefix

/-! ### N3: the guard of the row theorems and the catalogue -/

/-- **The guard lemma.**  On a branch with guard `t r ≤ p`, `N0 < p`, at the member of scale `r` with border
`m ≤ α r + 1` and `(N0 - 2) t ≥ 2 (1 + 2α)`, the sweep domain `2 (r + 2m) + 2 p < p²` holds
(`N = r + 2m`). -/
theorem sweep_sq_guard (r m p N0 : ℕ) (t α : ℚ) (hN0 : 2 ≤ N0) (hp5 : 5 ≤ p) (hpN : N0 < p)
    (hm : (m : ℚ) ≤ α * r + 1) (hpt : t * r ≤ p)
    (hcon : 2 * (1 + 2 * α) ≤ ((N0 : ℚ) - 2) * t) :
    2 * (r + 2 * m) + 2 * p < p * p := by
  have h2 : (2 : ℚ) ≤ N0 := by exact_mod_cast hN0
  have hr0 : (0 : ℚ) ≤ r := Nat.cast_nonneg _
  have key : (2 * (r + 2 * m) + 2 * p : ℚ) ≤ N0 * p + 4 := by
    have e1 : (2 * (r + 2 * m) : ℚ) ≤ 2 * (1 + 2 * α) * r + 4 := by nlinarith
    have e2 : 2 * (1 + 2 * α) * (r : ℚ) ≤ ((N0 : ℚ) - 2) * (t * r) := by
      calc 2 * (1 + 2 * α) * (r : ℚ) ≤ (((N0 : ℚ) - 2) * t) * r :=
            mul_le_mul_of_nonneg_right hcon hr0
        _ = _ := by ring
    have e3 : ((N0 : ℚ) - 2) * (t * r) ≤ ((N0 : ℚ) - 2) * p :=
      mul_le_mul_of_nonneg_left hpt (by linarith)
    nlinarith
  have key' : 2 * (r + 2 * m) + 2 * p ≤ N0 * p + 4 := by exact_mod_cast key
  have : N0 * p + 4 < p * p := by nlinarith
  omega

/-- A **row theorem** on the Löwner family `Q` over `altGeom c` (the form of the sweep rows, `Sweep.Rows`): under
the guard `guard r m p` on (scale, border, prime), every member of even scale is
`p ^ (price r m p + debit · del)`-integral, `del` the number of deleted common nodes. -/
structure SeqRow (c : ℚ) (hc : 0 < c) (const : ℝ) (depth : ℕ)
    (Q : NodeFamily.Index (altGeom c hc).geometry → ℚ[X]) where
  guard : ℕ → ℕ → ℕ → Prop
  price : ℕ → ℕ → ℕ → ℕ
  debit : ℕ
  valid : ∀ i : (AltEvenFam c hc const depth Q).ι, (AltEvenFam c hc const depth Q).Adm i → 0 < i.1 →
    ∀ (p : ℕ) [Fact p.Prime], guard i.1 ((altGeom c hc).borderSize i.1) p →
      GLE p (price i.1 ((altGeom c hc).borderSize i.1) p + debit * delCount (altGeom c hc) i)
        ((AltEvenFam c hc const depth Q).Q i)

/-- **N3: the `KCatValidFam` producer.**  Every branch of the catalogue `cat` is realised by a row theorem:
whenever the hypotheses of the branch (`Pbad < p`, `N0 < p`, `Q0 N < p²`, the pole roots, the branch
conditions) hold, the row's guard holds, its price is at most the branch price, and its debit at most the
branch debit.  Then the catalogue is valid for the family. -/
theorem kcatValid_of_rows (c : ℚ) (hc : 0 < c) (const : ℝ) (depth : ℕ)
    (Q : NodeFamily.Index (altGeom c hc).geometry → ℚ[X]) (sh : List Shift) (Q0 Pbad N0 : ℕ)
    (cat : List KBranch) (rows : ∀ b ∈ cat, SeqRow c hc const depth Q)
    (hreal : ∀ b (hb : b ∈ cat), ∀ i : (AltEvenFam c hc const depth Q).ι,
      (AltEvenFam c hc const depth Q).Adm i → 0 < i.1 →
      ∀ (p : ℕ) [Fact p.Prime], Pbad < p → N0 < p →
      Q0 * (i.1 + 2 * (altGeom c hc).borderSize i.1) < p * p →
      ∀ kv : ℕ → ℕ, (∀ n < sh.length, ∃ jn, (shAt sh n).q * kv n = jn * p + (shAt sh n).o ∧ 0 < jn ∧
        jn < (shAt sh n).q ∧ 0 < kv n ∧ kv n < p) →
      (∀ cd ∈ b.conds, cd.Holds i.1 p ((altGeom c hc).borderSize i.1) kv) →
      (rows b hb).guard i.1 ((altGeom c hc).borderSize i.1) p ∧
      (rows b hb).price i.1 ((altGeom c hc).borderSize i.1) p ≤
        b.τ.evalN i.1 p ((altGeom c hc).borderSize i.1) kv ∧
      (rows b hb).debit ≤ b.debit) :
    KCatValidFam c hc const depth Q sh Q0 Pbad N0 cat := by
  intro b hb i hi hr0 p _ hPb hN hqN kv hroots hcond
  obtain ⟨hg, hpr, hdb⟩ := hreal b hb i hi hr0 p hPb hN hqN kv hroots hcond
  refine ⟨_, (rows b hb).valid i hi hr0 p hg, ?_⟩
  exact Nat.add_le_add hpr (Nat.mul_le_mul_right _ hdb)

/-- **The bridge to Theorem S.**  The even-scale family of the content route over the Löwner minors of
`(f, g)` is the even-scale restriction of `seqFamily` at the scale `(altGeom c).scale`, the form
`support_measureLB` asks content for. -/
theorem altEvenFam_seq_eq (c : ℚ) (hc : 0 < c) (f g : ℕ → ℚ) (const : ℝ) (depth : ℕ) :
    AltEvenFam c hc const depth (SeqFamily.poly f g (altGeom c hc).geometry) =
      (seqFamily f g const (altGeom c hc).geometry depth).restrictAdm
        (fun i => (altGeom c hc).scale i % 2 = 0) := rfl

end CatalanCore.Uniform.Support

#print axioms CatalanCore.Uniform.Support.datum_lw_gle
#print axioms CatalanCore.Uniform.Support.datum_altQ
#print axioms CatalanCore.Uniform.Support.seq_altQ
#print axioms CatalanCore.Uniform.Support.preValid_of_crude_rows
#print axioms CatalanCore.Uniform.Support.sweep_sq_guard
#print axioms CatalanCore.Uniform.Support.kcatValid_of_rows
