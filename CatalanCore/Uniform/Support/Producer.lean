module

public import CatalanCore.Uniform.Support.SeqFamily
public import CatalanCore.Uniform.Support.Datum
public import CatalanCore.Uniform.Support.Content
public import CatalanCore.Uniform.Content.Sweep.CellsB
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
theorem seqFullN_entry_gle_uniform (f g : ℕ → ℚ) (c : ι → ℕ) (xs ys : κ → ℕ) {N e : ℕ}
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
    (seqFullN_entry_gle_uniform f g c xs ys hent hc hx hy)
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

/-! ### All-order assignment prices (Q15) -/
namespace IntegerPoleRows
open CatalanCore.Uniform.Content.Sweep

def ur (h p N t : ℕ) : ℕ :=
  (h - 2) + if ((N - 1 - t) % p) % 2 = 0 then 1 else 0

theorem ur_add_one (h p N t : ℕ) : ur h p N t + 1 = (h - 2) + uRow p N t := by
  unfold ur uRow
  split_ifs <;> omega

theorem ur_add_uc (h p N t : ℕ) (hh : 2 ≤ h) : ur h p N t + uCol p N t = h := by
  have hsum := uRow_add_uCol p N t
  have hrow := ur_add_one h p N t
  omega

theorem weight_le_ur_uc (h p N : ℕ) (hh : 2 ≤ h) {s t : ℕ} (hs : s < N) (ht : t < N) :
    hpoleWeight h p s t ≤ ur h p N s + uCol p N t := by
  have hur : h - 2 ≤ ur h p N s := by unfold ur; omega
  have huc : 1 ≤ uCol p N t := by unfold uCol; split_ifs <;> omega
  by_cases he : s = t
  · subst he
    have hsum := ur_add_uc h p N s hh
    unfold hpoleWeight
    split_ifs <;> omega
  by_cases hpq : s / p = t / p
  · simp only [hpoleWeight, he, if_false, hpq, if_true]
    omega
  by_cases hm : s % p = t % p
  · have hrow := uRow_cong hs ht hm
    have hur1 := ur_add_one h p N s
    have hur2 := ur_add_one h p N t
    have hsum := ur_add_uc h p N t hh
    simp only [hpoleWeight, he, hpq, hm, if_false, if_true]
    omega
  · simp only [hpoleWeight, he, hpq, hm, if_false]
    omega

section Rows
variable {p : ℕ} [hp : Fact p.Prime]
  {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def rowDet (h : ℕ) (d : ℕ → ℚ) (cn : ι → ℕ) (r m : ℕ) : ℚ[X] :=
  (seqFullN (hpoleF h d) (hpoleE h d) cn
    (fun i : Fin m => r + 2 * (i : ℕ)) (fun i : Fin m => r + 2 * (i : ℕ) + 1) (X : ℚ[X])).det

theorem row_of_dual (h : ℕ) (hh : 2 ≤ h) (d : ℕ → ℚ)
    (hd : ∀ j ∈ Icc 1 (h - 1), d j ∈ LocRing p)
    (cn : ι → ℕ) {r m : ℕ} (hcr : ∀ a, cn a < r) (hN : r + 2 * m < p * p)
    (ur uc : ℕ → ℕ)
    (he : ∀ s t, s < r + 2 * m → t < r + 2 * m → hpoleWeight h p s t ≤ ur s + uc t) :
    GLE p (∑ a : ι, ur (cn a) + ∑ i : Fin m, ur (r + 2 * (i : ℕ)) +
      (∑ a : ι, uc (cn a) + ∑ i : Fin m, uc (r + 2 * (i : ℕ) + 1))) (rowDet h d cn r m) := by
  let xs := fun i : Fin m => r + 2 * (i : ℕ)
  let ys := fun i : Fin m => r + 2 * (i : ℕ) + 1
  have hr : ∀ a : ι ⊕ Fin m, Sum.elim cn xs a < r + 2 * m := by
    intro a; rcases a with a | i
    · have := hcr a; simp <;> omega
    · have := i.2; simp [xs] <;> omega
  have hc : ∀ a : ι ⊕ Fin m, Sum.elim cn ys a < r + 2 * m := by
    intro a; rcases a with a | i
    · have := hcr a; simp <;> omega
    · have := i.2; simp [ys] <;> omega
  have hv := seqFullN_det_gle_of_dual (hpoleF h d) (hpoleE h d) cn xs ys
    (fun a b => hpoleWeight h p (Sum.elim cn xs a) (Sum.elim cn ys b))
    (fun a b => hpole_weight_table h hh d hd _ _ (lt_trans (hr a) hN) (lt_trans (hc b) hN))
    (fun a => ur (Sum.elim cn xs a)) (fun b => uc (Sum.elim cn ys b))
    (fun a b => he _ _ (hr a) (hc b))
  simpa only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, xs, ys, rowDet] using hv

theorem window_ur_uc (h r m : ℕ) (hh : 2 ≤ h) (hodd : p % 2 = 1) :
    (∑ i : Fin m, ur h p (r + 2 * m) (r + 2 * (i : ℕ))) +
      (∑ i : Fin m, uCol p (r + 2 * m) (r + 2 * (i : ℕ) + 1)) =
        (h - 1) * m + Aphi p (2 * m) := by
  have hold : (∑ i : Fin m, uRow p (r + 2 * m) (r + 2 * (i : ℕ))) +
      (∑ i : Fin m, uCol p (r + 2 * m) (r + 2 * (i : ℕ) + 1)) = 2 * m + Aphi p (2 * m) := by
    rw [← Finset.sum_add_distrib]
    have hv : ∀ i : Fin m, uRow p (r + 2 * m) (r + 2 * (i : ℕ)) +
        uCol p (r + 2 * m) (r + 2 * (i : ℕ) + 1) =
        ((1 + ((2 * (m - 1 - (i : ℕ)) + 1) / p) % 2) +
          (1 + ((2 * (m - 1 - (i : ℕ))) / p) % 2)) := by
      intro i
      rw [uRow_window p _ r m i hodd rfl i.2, uCol_window p _ r m i hodd rfl i.2]
    rw [Finset.sum_congr rfl (fun i _ => hv i),
      Fin.sum_univ_eq_sum_range (fun i => ((1 + ((2 * (m - 1 - i) + 1) / p) % 2) +
        (1 + ((2 * (m - 1 - i)) / p) % 2))) m,
      Finset.sum_range_reflect (fun k => ((1 + ((2 * k + 1) / p) % 2) + (1 + ((2 * k) / p) % 2))) m,
      window_sum]
  have he := congrArg (fun f : Fin m → ℕ => ∑ i, f i)
    (funext fun i : Fin m => ur_add_one h p (r + 2 * m) (r + 2 * (i : ℕ)))
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    mul_one] at he
  have hh2 : h - 2 + 2 = h := by omega
  have hh1 : h - 1 + 1 = h := by omega
  have he2 := congrArg (fun k => k * m) hh2
  have he1 := congrArg (fun k => k * m) hh1
  simp only [Nat.add_mul, Nat.one_mul] at he2 he1
  nlinarith

theorem row_first (h : ℕ) (hh : 2 ≤ h) (d : ℕ → ℚ)
    (hd : ∀ j ∈ Icc 1 (h - 1), d j ∈ LocRing p)
    (cn : ι → ℕ) (hinj : Function.Injective cn) {r m : ℕ} (hcr : ∀ a, cn a < r)
    (hN : r + 2 * m < p * p) (hodd : p % 2 = 1) :
    GLE p (h * (r + m) - min (m % p) (p - m % p)) (rowDet h d cn r m) := by
  have hb := row_of_dual h hh d hd cn hcr hN (ur h p (r + 2 * m)) (uCol p (r + 2 * m))
    (fun s t hs ht => weight_le_ur_uc h p (r + 2 * m) hh hs ht)
  refine hb.mono ?_
  have hcard : Fintype.card ι ≤ r := by
    have hc := Fintype.card_le_of_injective (fun a : ι => (⟨cn a, hcr a⟩ : Fin r))
      (fun a b hab => hinj (by simpa using hab))
    simpa using hc
  have hcom : ∑ a : ι, ur h p (r + 2 * m) (cn a) +
      ∑ a : ι, uCol p (r + 2 * m) (cn a) = h * Fintype.card ι := by
    rw [← Finset.sum_add_distrib]
    simp only [ur_add_uc h p (r + 2 * m) _ hh, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    exact Nat.mul_comm _ _
  have hwin := window_ur_uc h r m hh hodd
  have hmin := Aphi_min p m hodd
  have hc := Nat.mul_le_mul_left h hcard
  have hh1 : h - 1 + 1 = h := by omega
  have he1 := congrArg (fun k => k * m) hh1
  simp only [Nat.add_mul, Nat.one_mul] at he1
  have hdlt : min (m % p) (p - m % p) ≤ m := (min_le_left _ _).trans (Nat.mod_le _ _)
  have hm : m ≤ h * (r + m) := by nlinarith
  have hsub := Nat.sub_add_cancel (hdlt.trans hm)
  nlinarith

theorem row_of_potential (h : ℕ) (hh : 2 ≤ h) (d : ℕ → ℚ)
    (hd : ∀ j ∈ Icc 1 (h - 1), d j ∈ LocRing p)
    (cn : ι → ℕ) (hinj : Function.Injective cn) {r m : ℕ}
    (hcr : ∀ a, cn a < r) (hN : r + 2 * m < p * p)
    (φ : ℕ → ℕ)
    (he : ∀ s t, s < r + 2 * m → t < r + 2 * m → hpoleWeight h p s t ≤ φ s + φ t) :
    GLE p ((∑ t ∈ range r, φ t) + ∑ t ∈ range (r + 2 * m), φ t) (rowDet h d cn r m) := by
  have hb := row_of_dual h hh d hd cn hcr hN φ φ he
  refine hb.mono ?_
  have hcom : ∑ a : ι, φ (cn a) ≤ ∑ t ∈ range r, φ t := by
    rw [← Finset.sum_image (f := φ) (g := cn) (s := Finset.univ) (fun a _ b _ he => hinj he)]
    apply Finset.sum_le_sum_of_subset
    intro t ht
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp ht
    exact Finset.mem_range.mpr (hcr a)
  have hwin := win_sum φ r m
  have hfull := Finset.sum_range_add φ r (2 * m)
  omega

def phiStep (h p t : ℕ) : ℕ := if p ≤ t then h else 0

theorem weight_le_step (h : ℕ) (hh : 2 ≤ h) (s t : ℕ) :
    hpoleWeight h p s t ≤ phiStep h p s + phiStep h p t := by
  have hb : hpoleWeight h p s t ≤ h := by unfold hpoleWeight; split_ifs <;> omega
  by_cases hs : p ≤ s
  · simp only [phiStep, hs, if_true]; omega
  by_cases ht : p ≤ t
  · simp only [phiStep, ht, if_true]; omega
  have hs' : s < p := by omega
  have ht' : t < p := by omega
  have hd1 := Nat.div_eq_of_lt hs'
  have hd2 := Nat.div_eq_of_lt ht'
  simp [hpoleWeight, phiStep, hs, ht, hd1, hd2]

theorem sum_phiStep (h p n : ℕ) : ∑ t ∈ range n, phiStep h p t = h * (n - p) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases hn : p ≤ n
    · rw [phiStep, if_pos hn, show n + 1 - p = n - p + 1 by omega, Nat.mul_add, Nat.mul_one]
    · have hn' : n ≤ p := by omega
      have hn'' : n + 1 ≤ p := by omega
      simp [phiStep, hn, Nat.sub_eq_zero_of_le hn', Nat.sub_eq_zero_of_le hn'']

theorem row_step (h : ℕ) (hh : 2 ≤ h) (d : ℕ → ℚ)
    (hd : ∀ j ∈ Icc 1 (h - 1), d j ∈ LocRing p)
    (cn : ι → ℕ) (hinj : Function.Injective cn) {r m : ℕ}
    (hcr : ∀ a, cn a < r) (hN : r + 2 * m < p * p) :
    GLE p (h * (r - p) + h * (r + 2 * m - p)) (rowDet h d cn r m) := by
  have hb := row_of_potential h hh d hd cn hinj hcr hN (phiStep h p)
    (fun s t _ _ => weight_le_step h hh s t)
  simpa only [sum_phiStep] using hb

theorem row_second (h : ℕ) (hh : 2 ≤ h) (d : ℕ → ℚ)
    (hd : ∀ j ∈ Icc 1 (h - 1), d j ∈ LocRing p)
    (cn : ι → ℕ) (hinj : Function.Injective cn) {r m : ℕ}
    (hcr : ∀ a, cn a < r) (hN : r + 2 * m < p * p) (hpr : p ≤ r) :
    GLE p (2 * h * (r + m - p)) (rowDet h d cn r m) := by
  have hb := row_step h hh d hd cn hinj hcr hN
  have he : h * (r - p) + h * (r + 2 * m - p) = 2 * h * (r + m - p) := by
    have h1 : r - p + p = r := Nat.sub_add_cancel hpr
    have h2 : r + 2 * m - p + p = r + 2 * m := Nat.sub_add_cancel (by omega)
    have h3 : r + m - p + p = r + m := Nat.sub_add_cancel (by omega)
    nlinarith
  rwa [he] at hb

theorem row_fourth (h : ℕ) (hh : 2 ≤ h) (d : ℕ → ℚ)
    (hd : ∀ j ∈ Icc 1 (h - 1), d j ∈ LocRing p)
    (cn : ι → ℕ) (hinj : Function.Injective cn) {r m : ℕ}
    (hcr : ∀ a, cn a < r) (hN : r + 2 * m < p * p) (hpr : r ≤ p) :
    GLE p (h * (r + 2 * m - p)) (rowDet h d cn r m) := by
  simpa only [Nat.sub_eq_zero_of_le hpr, mul_zero, zero_add] using
    row_step h hh d hd cn hinj hcr hN

def phiThird (h p r t : ℕ) : ℕ :=
  if t < r - p then 1 else if t < p then 0 else if t < r then h - 1
    else if t < 2 * p then h else h - 1

set_option maxHeartbeats 2000000 in
theorem weight_le_third (h : ℕ) (hh : 2 ≤ h) {r m s t : ℕ}
    (hpr : p ≤ r) (hrp : r ≤ 2 * p) (hmp : 2 * m ≤ p)
    (hN : r + 2 * m ≤ 3 * p) (hs : s < r + 2 * m) (ht : t < r + 2 * m) :
    hpoleWeight h p s t ≤ phiThird h p r s + phiThird h p r t := by
  have hp0 := hp.out.pos
  have hsd : s / p < 3 := (Nat.div_lt_iff_lt_mul hp0).mpr (by omega)
  have htd : t / p < 3 := (Nat.div_lt_iff_lt_mul hp0).mpr (by omega)
  have hse := Nat.div_add_mod s p
  have hte := Nat.div_add_mod t p
  have hsm := Nat.mod_lt s hp0
  have htm := Nat.mod_lt t hp0
  interval_cases hs' : s / p <;> interval_cases ht' : t / p <;>
    (try simp only [hs', ht', Nat.mul_zero, Nat.mul_one] at hse hte) <;>
    unfold hpoleWeight phiThird <;> split_ifs <;> omega

theorem sum_prefix_const (f : ℕ → ℕ) {a b v : ℕ} (hab : a ≤ b)
    (hf : ∀ t, a ≤ t → t < b → f t = v) :
    ∑ t ∈ range b, f t = (∑ t ∈ range a, f t) + (b - a) * v := by
  have hb : b = a + (b - a) := by omega
  conv_lhs => rw [hb, Finset.sum_range_add]
  congr 1
  calc
    ∑ t ∈ range (b - a), f (a + t) = ∑ _ ∈ range (b - a), v := by
      apply Finset.sum_congr rfl
      intro t ht
      exact hf _ (by omega) (by have := Finset.mem_range.mp ht; omega)
    _ = _ := by simp

theorem third_sums (h : ℕ) (hh : 2 ≤ h) {r m : ℕ}
    (hpr : p ≤ r) (hrp : r ≤ 2 * p) (hN : 2 * p ≤ r + 2 * m) :
    (∑ t ∈ range r, phiThird h p r t) + (∑ t ∈ range (r + 2 * m), phiThird h p r t) =
      (2 * h - 1) * r + 2 * (h - 1) * m - 2 * (h - 1) * p := by
  have e0 := sum_prefix_const (phiThird h p r) (a := 0) (b := r - p) (v := 1)
    (by omega) (fun t ht0 ht => by simp only [phiThird, ht, if_true])
  have e1 := sum_prefix_const (phiThird h p r) (a := r - p) (b := p) (v := 0)
    (by omega) (fun t ht0 ht => by simp only [phiThird, show ¬t < r - p by omega, ht, if_false, if_true])
  have e2 := sum_prefix_const (phiThird h p r) (a := p) (b := r) (v := h - 1)
    hpr (fun t ht0 ht => by
      simp only [phiThird, show ¬t < r - p by omega, show ¬t < p by omega, ht, if_false, if_true])
  have e3 := sum_prefix_const (phiThird h p r) (a := r) (b := 2 * p) (v := h)
    hrp (fun t ht0 ht => by
      simp only [phiThird, show ¬t < r - p by omega, show ¬t < p by omega,
        show ¬t < r by omega, ht, if_false, if_true])
  have e4 := sum_prefix_const (phiThird h p r) (a := 2 * p) (b := r + 2 * m) (v := h - 1)
    hN (fun t ht0 ht => by
      simp only [phiThird, show ¬t < r - p by omega, show ¬t < p by omega,
        show ¬t < r by omega, show ¬t < 2 * p by omega, if_false])
  simp only [Finset.sum_range_zero, zero_add, Nat.sub_zero, mul_one, mul_zero, add_zero] at e0 e1
  have er : r - p + p = r := Nat.sub_add_cancel hpr
  have er' : 2 * p - r + r = 2 * p := Nat.sub_add_cancel hrp
  have en : r + 2 * m - 2 * p + 2 * p = r + 2 * m := Nat.sub_add_cancel hN
  have hh1 : h - 1 + 1 = h := by omega
  have hh2 : 2 * h - 1 + 1 = 2 * h := by omega
  have heprod := Nat.mul_le_mul_left (2 * (h - 1)) hpr
  have hprice : 2 * (h - 1) * p ≤ (2 * h - 1) * r + 2 * (h - 1) * m := by nlinarith
  have hprice_eq := Nat.sub_add_cancel hprice
  nlinarith

theorem row_third (h : ℕ) (hh : 2 ≤ h) (d : ℕ → ℚ)
    (hd : ∀ j ∈ Icc 1 (h - 1), d j ∈ LocRing p)
    (cn : ι → ℕ) (hinj : Function.Injective cn) {r m : ℕ}
    (hcr : ∀ a, cn a < r) (hN : r + 2 * m < p * p)
    (hpr : p ≤ r) (hrp : r ≤ 2 * p) (hmp : 2 * m ≤ p)
    (hlo : 2 * p ≤ r + 2 * m) (hhi : r + 2 * m ≤ 3 * p) :
    GLE p ((2 * h - 1) * r + 2 * (h - 1) * m - 2 * (h - 1) * p) (rowDet h d cn r m) := by
  have hb := row_of_potential h hh d hd cn hinj hcr hN (phiThird h p r)
    (fun s t hs ht => weight_le_third h hh hpr hrp hmp hhi hs ht)
  simpa only [third_sums h hh hpr hrp hlo] using hb

end Rows

def delta (m p : ℕ) : ℕ := min (m % p) (p - m % p)
def lowPrice (h r m p : ℕ) : ℕ := h * (r + m) - delta m p

theorem delta_add_period (m n a p : ℕ) : delta (m + n * a * p) p = delta m p := by
  simp only [delta, Nat.add_mul_mod_self_right]

theorem lowPrice_cov (h : ℕ) (hh : 2 ≤ h) (r m n a b p : ℕ) :
    lowPrice h (r + n * b * p) (m + n * a * p) p =
      lowPrice h r m p + n * (h * (a + b)) * p := by
  have hd : delta m p ≤ m := (min_le_left _ _).trans (Nat.mod_le _ _)
  have hm : m ≤ h * (r + m) := by nlinarith
  have he : h * (r + n * b * p + (m + n * a * p)) =
      h * (r + m) + n * (h * (a + b)) * p := by ring
  simp only [lowPrice, delta_add_period]
  omega

end IntegerPoleRows

/-! ### Q07: arbitrary fixed multiplicative crude factor -/

theorem altContentControl_of_scaled_crude (c : ℚ) (hc : 0 < c)
    (const : ℝ) (depth : ℕ) (Q : NodeFamily.Index (altGeom c hc).geometry → ℚ[X])
    (M : ℕ) [NeZero M] (K cF : ℕ)
    (hdeg : ∀ i, (Q i).natDegree ≤ i.2.card)
    (hclear : ∀ i, (AltEvenFam c hc const depth Q).Adm i →
      ∀ (p : ℕ) [Fact p.Prime], GLE p (K * Ecrude cF i.1 p) (Q i)) :
    AltContentControl c hc const depth M Q where
  deg := hdeg
  clear := fun i hi p _ => ⟨_, hclear i hi p⟩
  exc := by
    intro ε hε
    have hK : (0 : ℝ) < (K : ℝ) + 1 := by positivity
    have hε' : 0 < ε / ((K : ℝ) + 1) := div_pos hε hK
    have hF : ∀ p ∈ M.primeFactors, 2 ≤ p := fun p hp =>
      (Nat.prime_of_mem_primeFactors hp).two_le
    obtain ⟨R0, hR0⟩ := Filter.eventually_atTop.mp
      (fixed_exception_E_crude_small M.primeFactors hF cF (ε / ((K : ℝ) + 1)) hε')
    refine ⟨R0, fun i hi hR => ?_⟩
    have hsum : ∑ p ∈ M.primeFactors,
        (lpOptA c hc const depth Q i p : ℝ) * Real.log p ≤
        (K : ℝ) * ∑ p ∈ M.primeFactors, (Ecrude cF i.1 p : ℝ) * Real.log p := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro p hp
      haveI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
      have hb := lpOptA_le c hc const depth Q i p (hclear i hi p)
      have hb' : (lpOptA c hc const depth Q i p : ℝ) ≤ (K : ℝ) * Ecrude cF i.1 p := by
        exact_mod_cast hb
      exact (mul_le_mul_of_nonneg_right hb' (Real.log_natCast_nonneg p)).trans_eq (by ring)
    have hbound := mul_le_mul_of_nonneg_left (hR0 i.1 hR) (Nat.cast_nonneg K : (0 : ℝ) ≤ K)
    have hcoef : (K : ℝ) * (ε / ((K : ℝ) + 1)) ≤ ε := by
      rw [mul_div_assoc', div_le_iff₀ hK]
      nlinarith
    calc
      _ ≤ (K : ℝ) * ∑ p ∈ M.primeFactors, (Ecrude cF i.1 p : ℝ) * Real.log p := hsum
      _ ≤ (K : ℝ) * (ε / ((K : ℝ) + 1) * (i.1 : ℝ)^2) := hbound
      _ ≤ ε * (i.1 : ℝ)^2 := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)

/-! ### Finite-order crude arithmetic, including coefficient denominator primes -/
namespace IntegerPoleRows

section Crude
variable {p : ℕ} [hp : Fact p.Prime]

theorem rat_scaled_mem (q : ℚ) : (p : ℚ) ^ q.den * q ∈ LocRing p := by
  have hi := pow_mul_inv_mem (p := p) (n := q.den) (X := q.den) q.den_pos le_rfl
  have hn : (q.num : ℚ) ∈ LocRing p := int_mem_locRing _
  have hm := (LocRing p).mul_mem hn hi
  have he : (q.num : ℚ) * ((p : ℚ) ^ Nat.log p q.den * (1 / (q.den : ℚ))) =
      (p : ℚ) ^ Nat.log p q.den * q := by
    calc
      _ = (p : ℚ) ^ Nat.log p q.den * ((q.num : ℚ) / (q.den : ℚ)) := by ring
      _ = _ := by rw [Rat.num_div_den]
  rw [he] at hm
  exact mem_of_le (Nat.log_le_self p q.den) hm

def coeffCrude (h : ℕ) (d : ℕ → ℚ) : ℕ := ∑ j ∈ Icc 1 (h - 1), (d j).den

theorem coeff_scaled_mem (h : ℕ) (d : ℕ → ℚ) {j : ℕ} (hj : j ∈ Icc 1 (h - 1)) :
    (p : ℚ) ^ coeffCrude h d * d j ∈ LocRing p := by
  have hle : (d j).den ≤ coeffCrude h d := by
    simpa only [coeffCrude] using
      Finset.single_le_sum (f := fun j => (d j).den) (fun _ _ => Nat.zero_le _) hj
  exact mem_of_le hle (rat_scaled_mem (d j))

theorem power_term_scaled_mem {N k C H j : ℕ} (hN : 0 < N) (hk : 0 < k) (hkN : k ≤ N)
    (hj : j ≤ H) (q : ℚ) (hq : (p : ℚ) ^ C * q ∈ LocRing p) :
    (p : ℚ) ^ (C + H * Nat.log p N) * (q / (k : ℚ) ^ j) ∈ LocRing p := by
  have hinv := pow_mul_inv_mem (p := p) (n := k) (X := N) hk hkN
  have hm := (LocRing p).mul_mem hq ((LocRing p).pow_mem hinv j)
  have he : ((p : ℚ) ^ C * q) * ((p : ℚ) ^ Nat.log p N * (1 / (k : ℚ))) ^ j =
      (p : ℚ) ^ (C + j * Nat.log p N) * (q / (k : ℚ) ^ j) := by
    rw [mul_pow, _root_.one_div_pow, pow_add, ← pow_mul, Nat.mul_comm j (Nat.log p N)]
    ring
  rw [he] at hm
  exact mem_of_le (Nat.add_le_add_left (Nat.mul_le_mul_right _ hj) C) hm

theorem f_sub_scaled_mem (h : ℕ) (hh : 2 ≤ h) (d : ℕ → ℚ) (C : ℕ)
    (hd : ∀ j ∈ Icc 1 (h - 1), (p : ℚ) ^ C * d j ∈ LocRing p)
    {N s t : ℕ} (hN : 0 < N) (hst : s ≤ t) (ht : t ≤ N) :
    (p : ℚ) ^ (C + (h - 1) * Nat.log p N) * (hpoleF h d t - hpoleF h d s) ∈ LocRing p := by
  have he : hpoleF h d t - hpoleF h d s =
      ∑ k ∈ Ico s t, ∑ j ∈ Icc 1 (h - 1), d j / ((k : ℚ) + 1) ^ j := by
    rw [hpoleF, hpoleF, Finset.sum_Ico_eq_sub _ hst]
  rw [he, Finset.mul_sum]
  apply (LocRing p).sum_mem
  intro k hk
  rw [Finset.mul_sum]
  apply (LocRing p).sum_mem
  intro j hj
  have hkn := (Finset.mem_Ico.mp hk).2
  have hb := power_term_scaled_mem hN (by omega : 0 < k + 1) (by omega : k + 1 ≤ N)
    (Finset.mem_Icc.mp hj).2 (d j) (hd j hj)
  simpa only [Nat.cast_add, Nat.cast_one] using hb

theorem e_scaled_mem (h : ℕ) (hh : 2 ≤ h) (d : ℕ → ℚ) (C : ℕ)
    (hd : ∀ j ∈ Icc 1 (h - 1), (p : ℚ) ^ C * d j ∈ LocRing p)
    {N t : ℕ} (hN : 0 < N) (ht : t ≤ N) :
    (p : ℚ) ^ (C + h * Nat.log p N) * hpoleE h d t ∈ LocRing p := by
  rw [hpoleE, Finset.mul_sum]
  apply (LocRing p).sum_mem
  intro k hk
  rw [Finset.mul_sum]
  apply (LocRing p).sum_mem
  intro j hj
  have hkn := Finset.mem_range.mp hk
  have hb := power_term_scaled_mem (H := h) (j := j + 1) hN (by omega : 0 < k + 1)
    (by omega : k + 1 ≤ N) (by have := (Finset.mem_Icc.mp hj).2; omega) (d j) (hd j hj)
  have hm := (LocRing p).mul_mem (show (j : ℚ) ∈ LocRing p by
    exact_mod_cast int_mem_locRing (ℓ := p) (j : ℤ)) hb
  convert hm using 1 <;> push_cast <;> ring

theorem hpole_lw_gle_crude (h : ℕ) (hh : 2 ≤ h) (d : ℕ → ℚ) (C : ℕ)
    (hd : ∀ j ∈ Icc 1 (h - 1), (p : ℚ) ^ C * d j ∈ LocRing p)
    {N s t : ℕ} (hN : 0 < N) (hs : s ≤ N) (ht : t ≤ N) :
    GLE p (C + h * Nat.log p N) (Polynomial.C (lw (hpoleF h d) (hpoleE h d) s t)) := by
  rw [GLE.C_iff]
  have hoff : ∀ s t : ℕ, s < t → t ≤ N →
      (p : ℚ) ^ (C + h * Nat.log p N) *
        ((hpoleF h d t - hpoleF h d s) / ((t : ℚ) - s)) ∈ LocRing p := by
    intro s t hst ht
    have hf := f_sub_scaled_mem h hh d C hd hN hst.le ht
    have hi := pow_mul_inv_mem (p := p) (n := t - s) (X := N) (by omega) (by omega)
    have hm := (LocRing p).mul_mem hf hi
    have he : C + (h - 1) * Nat.log p N + Nat.log p N = C + h * Nat.log p N := by
      have hh1 : h - 1 + 1 = h := by omega
      calc
        _ = C + (h - 1 + 1) * Nat.log p N := by ring
        _ = _ := by rw [hh1]
    have hpow : (p : ℚ) ^ (C + h * Nat.log p N) =
        (p : ℚ) ^ (C + (h - 1) * Nat.log p N) * (p : ℚ) ^ Nat.log p N := by
      rw [← pow_add, he]
    convert hm using 1
    rw [Nat.cast_sub hst.le, hpow]
    ring
  by_cases he : s = t
  · subst he
    simp only [lw, if_true, mul_neg]
    exact (LocRing p).neg_mem (e_scaled_mem h hh d C hd hN hs)
  rcases lt_or_gt_of_ne he with hst | hts
  · simpa only [lw, if_neg he] using hoff s t hst ht
  · rw [lw_symm (hpoleF h d) (hpoleE h d) s t]
    simpa only [lw, if_neg (Ne.symm he)] using hoff t s hts hs

end Crude
end IntegerPoleRows

theorem seqPoly_gle_scaled_Ecrude (f g : ℕ → ℚ) (K cF : ℕ)
    (hent : ∀ (p : ℕ) [Fact p.Prime] (N A B : ℕ), 0 < N → A ≤ N → B ≤ N →
      GLE p (K * (3 * Nat.log p N + cF)) (C (lw f g A B)))
    (G : NodeFamily) (i : G.Index)
    (hN : ∀ a ∈ (G i.1).C ∪ (G i.1).X' ∪ (G i.1).Y', a ≤ 14 * i.1)
    (hcard : i.2.card + (G i.1).k ≤ 2 * i.1) (p : ℕ) [Fact p.Prime] :
    GLE p (K * Ecrude cF i.1 p) (SeqFamily.poly f g G i) := by
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
      (G i.1).xs (G i.1).ys (N := 14 * i.1) (e := K * (3 * Nat.log p (14 * i.1) + cF))
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
    calc (i.2.card + (G i.1).k) * (K * (3 * Nat.log p (14 * i.1) + cF))
        ≤ (2 * i.1) * (K * (3 * Nat.log p (14 * i.1) + cF)) := Nat.mul_le_mul hcard le_rfl
      _ = K * (2 * i.1 * (3 * Nat.log p (14 * i.1) + cF)) := by ring

/-- **`AltQ` for the Löwner minors of two sequences on `altGeom c`** from an entry bound. -/
theorem seq_alt_scaled_crude (c : ℚ) (hc : 0 < c) (hc1 : c ≤ 1) (f g : ℕ → ℚ) (K cF : ℕ)
    (hent : ∀ (p : ℕ) [Fact p.Prime] (N A B : ℕ), 0 < N → A ≤ N → B ≤ N →
      GLE p (K * (3 * Nat.log p N + cF)) (C (lw f g A B))) :
    ∀ i : NodeFamily.Index (altGeom c hc).geometry, i.1 % 2 = 0 →
      ∀ (p : ℕ) [Fact p.Prime], GLE p (K * Ecrude cF i.1 p)
        (SeqFamily.poly f g (altGeom c hc).geometry i) := by
  intro i hi p _
  have hbs := altGeom_borderSize_le c hc hc1 hi
  have hX := altGeom_X c hc hi
  have hY := altGeom_Y c hc hi
  have hC := altGeom_C c hc i.1
  have hk : ((altGeom c hc).geometry i.1).k = (altGeom c hc).borderSize i.1 :=
    geometry_k_eq_borderSize _ _
  refine seqPoly_gle_scaled_Ecrude f g K cF hent (altGeom c hc).geometry i ?_ ?_ p
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


open CatalanCore.Uniform.Content.SmallPrimes
theorem preValid_of_scaled_crude_rows (c : ℚ) (hc : 0 < c) (const : ℝ) (depth : ℕ)
    (Q : NodeFamily.Index (altGeom c hc).geometry → ℚ[X]) {K cF : ℕ}
    (hclear : ∀ i, (AltEvenFam c hc const depth Q).Adm i →
      ∀ (p : ℕ) [Fact p.Prime], GLE p (K * Ecrude cF i.1 p) (Q i))
    (M : ℕ) (B : SmallBudget) (A C : ℕ) (hC : K * (30 + 2 * cF) ≤ C)
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
  · refine ⟨K * Ecrude cF i.1 p, hclear i hi p, ?_⟩
    have h0 := Ecrude_le_budget cF (30 + 2 * cF) i.1 p le_rfl hr1 (Fact.out : p.Prime).two_le
    have h1 : K * Ecrude cF i.1 p ≤ C * i.1 * (Nat.log 2 i.1 + 1) := by
      calc
        _ ≤ K * ((30 + 2 * cF) * i.1 * (Nat.log 2 i.1 + 1)) := Nat.mul_le_mul_left K h0
        _ = (K * (30 + 2 * cF)) * i.1 * (Nat.log 2 i.1 + 1) := by ring
        _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hC)
    have h2 : (K * Ecrude cF i.1 p : ℝ) ≤ (C : ℝ) * i.1 * ((Nat.log 2 i.1 : ℝ) + 1) := by
      exact_mod_cast (by simpa [mul_assoc] using h1 : K * Ecrude cF i.1 p ≤ C * i.1 * (Nat.log 2 i.1 + 1))
    have h3 := hB i.1 p hsq hpr
    have h4 : (0 : ℝ) ≤ (α0b : ℝ) * i.1 := by
      have : (0 : ℝ) ≤ (α0b : ℝ) := by exact_mod_cast hα
      positivity
    push_cast
    linarith
  · push Not at hsq
    obtain ⟨n, hn, hle⟩ := hrow i hi p hsq hpr
    exact ⟨n, hn, by linarith⟩



theorem seq_alt_control_of_scaled_entries (c : ℚ) (hc : 0 < c) (hc1 : c ≤ 1)
    (f g : ℕ → ℚ) (const : ℝ) (depth M K cF : ℕ) [NeZero M]
    (hent : ∀ (p : ℕ) [Fact p.Prime] (N A B : ℕ), 0 < N → A ≤ N → B ≤ N →
      GLE p (K * (3 * Nat.log p N + cF)) (C (lw f g A B))) :
    AltContentControl c hc const depth M (SeqFamily.poly f g (altGeom c hc).geometry) :=
  altContentControl_of_scaled_crude c hc const depth _ M K cF
    (fun i => SeqFamily.poly_natDegree f g _ i)
    (fun i hi p _ => seq_alt_scaled_crude c hc hc1 f g K cF hent i hi.2 p)

theorem hpole_alt_control (h : ℕ) (hh : 2 ≤ h) (d : ℕ → ℚ)
    (c : ℚ) (hc : 0 < c) (hc1 : c ≤ 1) (const : ℝ) (depth M : ℕ) [NeZero M] :
    AltContentControl c hc const depth M
      (SeqFamily.poly (hpoleF h d) (hpoleE h d) (altGeom c hc).geometry) := by
  let C0 := IntegerPoleRows.coeffCrude h d
  let K := C0 + h + 1
  apply seq_alt_control_of_scaled_entries c hc hc1 (hpoleF h d) (hpoleE h d) const depth M K 1
  intro p _ N A B hN hA hB
  have hb := IntegerPoleRows.hpole_lw_gle_crude (p := p) h hh d C0
    (fun j hj => IntegerPoleRows.coeff_scaled_mem (p := p) h d hj) hN hA hB
  refine hb.mono ?_
  have hC : C0 ≤ K := by dsimp [K]; omega
  have hhK : h ≤ 3 * K := by dsimp [K]; omega
  have hm := Nat.mul_le_mul_right (Nat.log p N) hhK
  nlinarith

/-! ### The four prices on actual family members, at arbitrary hybrid geometry -/
namespace IntegerPoleRows
open CatalanCore.Uniform.Content.Wire

theorem seqPoly_window_eq (h : ℕ) (d : ℕ → ℚ) {G : BlockGeom} {r : ℕ}
    (hs : HybShape G r) (S : Finset (G.geometry r).C) :
    SeqFamily.poly (hpoleF h d) (hpoleE h d) G.geometry ⟨r, S⟩ =
      rowDet h d (fun a : S => ((a.1 : (G.geometry r).C) : ℕ)) r (G.geometry r).k := by
  have hx : (G.geometry r).xs = fun i : Fin (G.geometry r).k => r + 2 * (i : ℕ) := funext hs.xs_eq
  have hy : (G.geometry r).ys = fun i : Fin (G.geometry r).k => r + 2 * (i : ℕ) + 1 := funext hs.ys_eq
  unfold SeqFamily.poly rowDet
  rw [hx, hy]

theorem family_of_window (h : ℕ) (d : ℕ → ℚ) {p : ℕ} [Fact p.Prime]
    {G : BlockGeom} {r : ℕ} (hs : HybShape G r) (S : Finset (G.geometry r).C) (E : ℕ)
    (hrow : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (cn : ι → ℕ),
      Function.Injective cn → (∀ a, cn a < r) → GLE p E (rowDet h d cn r (G.geometry r).k)) :
    GLE p E (SeqFamily.poly (hpoleF h d) (hpoleE h d) G.geometry ⟨r, S⟩) := by
  rw [seqPoly_window_eq h d hs S]
  exact hrow _ (fun a b he => Subtype.ext (Subtype.ext he)) (fun a => hybShape_lt_scale hs a.1)

section Family
variable {p : ℕ} [Fact p.Prime] (h : ℕ) (hh : 2 ≤ h) (d : ℕ → ℚ)
  (hd : ∀ j ∈ Icc 1 (h - 1), d j ∈ LocRing p)
  {G : BlockGeom} {r : ℕ} (hs : HybShape G r) (S : Finset (G.geometry r).C)
  (hN : r + 2 * (G.geometry r).k < p * p)

include hh hd hN hs

theorem family_first (hodd : p % 2 = 1) :
    GLE p (h * (r + (G.geometry r).k) - delta (G.geometry r).k p)
      (SeqFamily.poly (hpoleF h d) (hpoleE h d) G.geometry ⟨r, S⟩) := by
  apply family_of_window h d hs S
  intro ι _ _ cn hinj hcr
  exact row_first h hh d hd cn hinj hcr hN hodd

theorem family_second (hpr : p ≤ r) :
    GLE p (2 * h * (r + (G.geometry r).k - p))
      (SeqFamily.poly (hpoleF h d) (hpoleE h d) G.geometry ⟨r, S⟩) := by
  apply family_of_window h d hs S
  intro ι _ _ cn hinj hcr
  exact row_second h hh d hd cn hinj hcr hN hpr

theorem family_third (hpr : p ≤ r) (hrp : r ≤ 2 * p) (hmp : 2 * (G.geometry r).k ≤ p)
    (hlo : 2 * p ≤ r + 2 * (G.geometry r).k) (hhi : r + 2 * (G.geometry r).k ≤ 3 * p) :
    GLE p ((2 * h - 1) * r + 2 * (h - 1) * (G.geometry r).k - 2 * (h - 1) * p)
      (SeqFamily.poly (hpoleF h d) (hpoleE h d) G.geometry ⟨r, S⟩) := by
  apply family_of_window h d hs S
  intro ι _ _ cn hinj hcr
  exact row_third h hh d hd cn hinj hcr hN hpr hrp hmp hlo hhi

theorem family_fourth (hpr : r ≤ p) :
    GLE p (h * (r + 2 * (G.geometry r).k - p))
      (SeqFamily.poly (hpoleF h d) (hpoleE h d) G.geometry ⟨r, S⟩) := by
  apply family_of_window h d hs S
  intro ι _ _ cn hinj hcr
  exact row_fourth h hh d hd cn hinj hcr hN hpr
end Family
end IntegerPoleRows

end CatalanCore.Uniform.Support

#print axioms CatalanCore.Uniform.Support.datum_lw_gle
#print axioms CatalanCore.Uniform.Support.datum_altQ
#print axioms CatalanCore.Uniform.Support.seq_altQ
#print axioms CatalanCore.Uniform.Support.preValid_of_crude_rows
#print axioms CatalanCore.Uniform.Support.sweep_sq_guard
#print axioms CatalanCore.Uniform.Support.kcatValid_of_rows

#print axioms CatalanCore.Uniform.Support.IntegerPoleRows.row_first
#print axioms CatalanCore.Uniform.Support.IntegerPoleRows.row_second
#print axioms CatalanCore.Uniform.Support.IntegerPoleRows.row_third
#print axioms CatalanCore.Uniform.Support.IntegerPoleRows.row_fourth
#print axioms CatalanCore.Uniform.Support.IntegerPoleRows.lowPrice_cov

#print axioms CatalanCore.Uniform.Support.hpole_alt_control
#print axioms CatalanCore.Uniform.Support.IntegerPoleRows.family_third
