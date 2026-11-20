module

public import CatalanCore.Measure.TiedNV
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# The prime-tied families of Lai's plane and ratio (ledger LR04, LR05, LR06)

Instance data for `CatalanCore.Measure.TiedNV` and `CatalanCore.NT.TiedWindow`.  The three families
of primes are `ℓ ≡ 1 (mod 18)` (Lai, slope `9/2`) and `ℓ ≡ 5, 3 (mod 7)` (NV7, slope `7/3`), all as
unit classes modulo `126`.

* `tied_mass`: the union window mass of these three families (tolerance `e` for all) in closed form;
* `plane_unionWindowOK`: `β = 1637/10000`, `e = 4`, mass `18007/18000 > 1`;
* `ratio_unionWindowOK`: `β = 661/1000`, `e = 1`, windows overlapping, mass `> 1`;
* `plane_threshold`, `ratio_threshold`: `ρ (3/η + β) < 34.14, 55.50` for `μ`;
* `tiedOfClass`: a line `TiedNV` (slope interval `[c, c]`) over modulus `126` from residue-class
  statements `ℓ % m' = r0`.

Criterion W2B (ledger LB13): the four families band `[8/3, 3]` over all unit classes, Lai, NV7a, NV7b.
* `tied_mass4`: the union window mass in closed form (15 subsets);
* `plane_unionWindowOK4`: `β = 875/100000`, `e = 4`, mass `> 1`; `ratio_unionWindowOK4`:
  `β = 19186/100000`, `e = 1`, mass `> 1`;
* `plane_threshold4`, `ratio_threshold4`: `ρ (3/η + β) < 27.49` and `< 35.3495` (`< 35.35`);
* `windowOK_of_fields4`: transfer to four `TiedNV` families (the band instance plugs in here);
* `band_exists_n`: the member choice `8n/3 < ℓ < 3n - 1`, `x - 2 ≤ n ≤ y + 2` of the band.
-/

open Finset CatalanCore.NT CatalanCore.Measure

namespace CatalanCore.Lai

/-- Unit classes modulo `M` with residue `r0` modulo `m'`. -/
def classSet (M m' r0 : ℕ) [NeZero M] : Finset (ZMod M) :=
  Finset.univ.filter fun r => r.val.Coprime M ∧ r.val % m' = r0

theorem classSet_unit {M m' r0 : ℕ} [NeZero M] : ∀ s ∈ classSet M m' r0, IsUnit s := by
  intro s hs
  simp only [classSet, Finset.mem_filter, Finset.mem_univ, true_and] at hs
  have := (ZMod.isUnit_iff_coprime s.val M).mpr hs.1
  rwa [ZMod.natCast_zmod_val] at this

/-- For a prime `ℓ ≥ 11` and `m' ∣ M = 126`, membership in `classSet 126 m' r0` is the residue
condition `ℓ % m' = r0`. -/
theorem mem_classSet_iff {ℓ m' r0 : ℕ} (hp : ℓ.Prime) (h11 : 11 ≤ ℓ) (hm' : m' ∣ 126) :
    (ℓ : ZMod 126) ∈ classSet 126 m' r0 ↔ ℓ % m' = r0 := by
  have hcop : Nat.Coprime ℓ 126 := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hd
    have h126 : (126 : ℕ) = 2 * 3 * 3 * 7 := by norm_num
    rw [h126] at hd
    rcases (Nat.Prime.dvd_mul hp).mp hd with h | h
    · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
      · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
        · have := Nat.le_of_dvd (by norm_num) h; omega
        · have := Nat.le_of_dvd (by norm_num) h; omega
      · have := Nat.le_of_dvd (by norm_num) h; omega
    · have := Nat.le_of_dvd (by norm_num) h; omega
  have hval : (ℓ : ZMod 126).val = ℓ % 126 := ZMod.val_natCast 126 ℓ
  have hcop' : Nat.Coprime (ℓ % 126) 126 := by
    have := Nat.gcd_rec 126 ℓ
    unfold Nat.Coprime at hcop ⊢
    rw [Nat.gcd_comm] at hcop
    rw [← this]; exact hcop
  simp only [classSet, Finset.mem_filter, Finset.mem_univ, true_and, hval]
  rw [Nat.mod_mod_of_dvd _ hm']
  exact ⟨fun h => h.2, fun h => ⟨hcop', h⟩⟩

/-- The three class sets: Lai `ℓ ≡ 1 (18)`, NV7a `ℓ ≡ 5 (7)`, NV7b `ℓ ≡ 3 (7)`, modulo `126`. -/
def tiedS : Fin 3 → Finset (ZMod 126) := ![classSet 126 18 1, classSet 126 7 5, classSet 126 7 3]

/-- The slopes `ℓ ≈ c n`: `9/2` for Lai, `7/3` for NV7. -/
noncomputable def tiedC : Fin 3 → ℝ := ![9 / 2, 7 / 3, 7 / 3]

/-- The tolerance, equal for the three families. -/
def tiedE (e : ℕ) : Fin 3 → ℕ := fun _ => e

/-- **The window mass of the three Lai/NV7 families** in closed form. -/
theorem tied_mass (e : ℕ) (a b : ℝ) :
    unionMass tiedS tiedC tiedC (tiedE e) a b =
      e * ((9 / 2 : ℝ) * (1 / 6) * max 0 (b - a) + 2 * ((7 / 3 : ℝ) * (1 / 6)) * max 0 (b - a) -
        2 * (1 / 36) * max 0 ((7 / 3 : ℝ) * b - (9 / 2) * a)) := by
  have h1 : NESub (Fin 3) = {{0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} := by decide
  have o1 : (overlap tiedS {0}).card = 6 := by decide
  have o2 : (overlap tiedS {1}).card = 6 := by decide
  have o3 : (overlap tiedS {2}).card = 6 := by decide
  have o4 : (overlap tiedS {0, 1}).card = 1 := by decide
  have o5 : (overlap tiedS {0, 2}).card = 1 := by decide
  have o6 : (overlap tiedS {1, 2}).card = 0 := by decide
  have o7 : (overlap tiedS {0, 1, 2}).card = 0 := by decide
  have ht : Nat.totient 126 = 36 := by decide
  unfold unionMass
  rw [h1, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [minTol, winLen, Finset.insert_nonempty, Finset.singleton_nonempty, dite_true,
    Finset.inf'_insert, Finset.inf'_singleton, Finset.sup'_insert, Finset.sup'_singleton,
    o1, o2, o3, o4, o5, o6, o7, ht, tiedE, tiedC]
  have c1 : (#({0} : Finset (Fin 3))) = 1 := by decide
  have c2 : (#({1} : Finset (Fin 3))) = 1 := by decide
  have c3 : (#({2} : Finset (Fin 3))) = 1 := by decide
  have c4 : (#({0, 1} : Finset (Fin 3))) = 2 := by decide
  have c5 : (#({0, 2} : Finset (Fin 3))) = 2 := by decide
  have c6 : (#({1, 2} : Finset (Fin 3))) = 2 := by decide
  have c7 : (#({0, 1, 2} : Finset (Fin 3))) = 3 := by decide
  simp only [c1, c2, c3, c4, c5, c6, c7, min_self, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  have m1 : min (9 / 2 : ℝ) (7 / 3) = 7 / 3 := by norm_num
  have m2 : max (9 / 2 : ℝ) (7 / 3) = 9 / 2 := by norm_num
  have m3 : min (7 / 3 : ℝ) (7 / 3) = 7 / 3 := min_self _
  have m4 : max (7 / 3 : ℝ) (7 / 3) = 7 / 3 := max_self _
  simp only [m1, m2, m3, m4, min_self, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
  have r1 : b * (9 / 2 : ℝ) - a * (9 / 2) = (9 / 2) * (b - a) := by ring
  have r2 : b * (7 / 3 : ℝ) - a * (7 / 3) = (7 / 3) * (b - a) := by ring
  have r3 : b * (7 / 3 : ℝ) - a * (9 / 2) = 7 / 3 * b - 9 / 2 * a := by ring
  rw [r1, r2, r3]
  have x1 : max 0 ((9 / 2 : ℝ) * (b - a)) = (9 / 2) * max 0 (b - a) := by
    rw [mul_max_of_nonneg _ _ (by norm_num), mul_zero]
  have x2 : max 0 ((7 / 3 : ℝ) * (b - a)) = (7 / 3) * max 0 (b - a) := by
    rw [mul_max_of_nonneg _ _ (by norm_num), mul_zero]
  rw [x1, x2]
  norm_num
  ring

/-- `η = D - Λ` of the Lai roots: `D = 33.4401`, `Λ = 28.68723663`. -/
noncomputable def laiEta : ℝ := 3344010000 / 10 ^ 8 - 2868723663 / 10 ^ 8

theorem laiEta_pos : 0 < laiEta := by unfold laiEta; norm_num

/-- **LR05, plane**: `β = 1637/10000`, tolerance `4`; the windows are disjoint and the mass is
`18007/18000 > 1`. -/
theorem plane_unionWindowOK :
    UnionWindowOK tiedS tiedC tiedC (tiedE 4) (3 / laiEta) (3 / laiEta + 1637 / 10000) := by
  unfold UnionWindowOK
  rw [tied_mass]
  have h1 : max 0 (3 / laiEta + 1637 / 10000 - 3 / laiEta) = 1637 / 10000 := by
    rw [add_sub_cancel_left]; exact max_eq_right (by norm_num)
  have h2 : max 0 ((7 / 3 : ℝ) * (3 / laiEta + 1637 / 10000) - (9 / 2) * (3 / laiEta)) = 0 := by
    apply max_eq_left
    unfold laiEta
    norm_num
  rw [h1, h2]
  norm_num

/-- **LR05, ratio**: `β = 661/1000`, tolerance `1`; the Lai and NV7 windows overlap
(`N/n₀ = 2.047 > 27/14`) and the overlap is counted once. -/
theorem ratio_unionWindowOK :
    UnionWindowOK tiedS tiedC tiedC (tiedE 1) (3 / laiEta) (3 / laiEta + 661 / 1000) := by
  unfold UnionWindowOK
  rw [tied_mass]
  have h1 : max 0 (3 / laiEta + 661 / 1000 - 3 / laiEta) = 661 / 1000 := by
    rw [add_sub_cancel_left]; exact max_eq_right (by norm_num)
  have h2 : max 0 ((7 / 3 : ℝ) * (3 / laiEta + 661 / 1000) - (9 / 2) * (3 / laiEta)) =
      (7 / 3 : ℝ) * (3 / laiEta + 661 / 1000) - (9 / 2) * (3 / laiEta) := by
    apply max_eq_right
    unfold laiEta
    norm_num
  rw [h1, h2]
  unfold laiEta
  norm_num

/-- **LR06, plane**: `ρ (3/η + β) < 34.14`. -/
theorem plane_threshold :
    (4294856306 / 10 ^ 8 : ℝ) * (3 / laiEta + 1637 / 10000) < 34.14 := by
  unfold laiEta; norm_num

/-- **LR06, ratio**: `ρ (3/η + β) < 55.50`. -/
theorem ratio_threshold :
    (4294856306 / 10 ^ 8 : ℝ) * (3 / laiEta + 661 / 1000) < 55.50 := by
  unfold laiEta; norm_num

/-- Transfer of `UnionWindowOK` to three `TiedNV` families whose data are those of `tiedS`,
`tiedC` (both slope ends), `tiedE e`. -/
theorem windowOK_of_fields {Fam : PolyFamily} {scale : Fam.ι → ℕ} {W : ℤ → ℕ → ℕ} {e : ℕ} {a b : ℝ}
    (F : Fin 3 → TiedNV Fam scale 126 W) (hS : ∀ i, (F i).S = tiedS i)
    (hc₁ : ∀ i, (F i).c₁ = tiedC i) (hc₂ : ∀ i, (F i).c₂ = tiedC i)
    (he : ∀ i, (F i).e = tiedE e i)
    (h : UnionWindowOK tiedS tiedC tiedC (tiedE e) a b) :
    UnionWindowOK (fun i => (F i).S) (fun i => (F i).c₁) (fun i => (F i).c₂) (fun i => (F i).e)
      a b := by
  have e1 : (fun i => (F i).S) = tiedS := funext hS
  have e2 : (fun i => (F i).c₁) = tiedC := funext hc₁
  have e2' : (fun i => (F i).c₂) = tiedC := funext hc₂
  have e3 : (fun i => (F i).e) = tiedE e := funext he
  rw [e1, e2, e2', e3]; exact h


/-! ### The four families of the band criterion (Criterion W2B, ledger LB13) -/

/-- The four class sets: the band `8n/3 < ℓ < 3n - 1` over all unit classes (modulus `126`), Lai
`ℓ ≡ 1 (18)`, NV7a `ℓ ≡ 5 (7)`, NV7b `ℓ ≡ 3 (7)`. -/
def tiedS4 : Fin 4 → Finset (ZMod 126) :=
  ![classSet 126 1 0, classSet 126 18 1, classSet 126 7 5, classSet 126 7 3]

/-- Lower slopes: band `8/3`, Lai `9/2`, NV7 `7/3`. -/
noncomputable def tiedC1 : Fin 4 → ℝ := ![8 / 3, 9 / 2, 7 / 3, 7 / 3]

/-- Upper slopes: band `3`, Lai `9/2`, NV7 `7/3`. -/
noncomputable def tiedC2 : Fin 4 → ℝ := ![3, 9 / 2, 7 / 3, 7 / 3]

/-- The tolerance, equal for the four families. -/
def tiedE4 (e : ℕ) : Fin 4 → ℕ := fun _ => e

theorem minTol_tiedE4 (e : ℕ) {T : Finset (Fin 4)} (hT : T.Nonempty) : minTol (tiedE4 e) T = e := by
  unfold minTol; rw [dif_pos hT]; exact Finset.inf'_const hT e

theorem tied_winLen_0 (a b : ℝ) :
    winLen tiedC1 tiedC2 a b {0} = max 0 (3 * b - 8 / 3 * a) := by
  norm_num [winLen, tiedC1, tiedC2]; congr 1; ring

theorem tied_winLen_1 (a b : ℝ) :
    winLen tiedC1 tiedC2 a b {1} = max 0 (9 / 2 * (b - a)) := by
  norm_num [winLen, tiedC1, tiedC2]; congr 1; ring

theorem tied_winLen_2 (a b : ℝ) :
    winLen tiedC1 tiedC2 a b {2} = max 0 (7 / 3 * (b - a)) := by
  norm_num [winLen, tiedC1, tiedC2]; congr 1; ring

theorem tied_winLen_3 (a b : ℝ) :
    winLen tiedC1 tiedC2 a b {3} = max 0 (7 / 3 * (b - a)) := by
  norm_num [winLen, tiedC1, tiedC2]; congr 1; ring

theorem tied_winLen_01 (a b : ℝ) :
    winLen tiedC1 tiedC2 a b {0, 1} = max 0 (3 * b - 9 / 2 * a) := by
  norm_num [winLen, tiedC1, tiedC2, min_eq_left, min_eq_right, max_eq_left, max_eq_right]
  congr 1; ring

theorem tied_winLen_02 (a b : ℝ) :
    winLen tiedC1 tiedC2 a b {0, 2} = max 0 (7 / 3 * b - 8 / 3 * a) := by
  norm_num [winLen, tiedC1, tiedC2, min_eq_left, min_eq_right, max_eq_left, max_eq_right]
  congr 1; ring

theorem tied_winLen_03 (a b : ℝ) :
    winLen tiedC1 tiedC2 a b {0, 3} = max 0 (7 / 3 * b - 8 / 3 * a) := by
  norm_num [winLen, tiedC1, tiedC2, min_eq_left, min_eq_right, max_eq_left, max_eq_right]
  congr 1; ring

theorem tied_winLen_12 (a b : ℝ) :
    winLen tiedC1 tiedC2 a b {1, 2} = max 0 (7 / 3 * b - 9 / 2 * a) := by
  norm_num [winLen, tiedC1, tiedC2, min_eq_left, min_eq_right, max_eq_left, max_eq_right]
  congr 1; ring

theorem tied_winLen_13 (a b : ℝ) :
    winLen tiedC1 tiedC2 a b {1, 3} = max 0 (7 / 3 * b - 9 / 2 * a) := by
  norm_num [winLen, tiedC1, tiedC2, min_eq_left, min_eq_right, max_eq_left, max_eq_right]
  congr 1; ring

theorem tied_winLen_012 (a b : ℝ) :
    winLen tiedC1 tiedC2 a b {0, 1, 2} = max 0 (7 / 3 * b - 9 / 2 * a) := by
  norm_num [winLen, tiedC1, tiedC2, min_eq_left, min_eq_right, max_eq_left, max_eq_right]
  congr 1; ring

theorem tied_winLen_013 (a b : ℝ) :
    winLen tiedC1 tiedC2 a b {0, 1, 3} = max 0 (7 / 3 * b - 9 / 2 * a) := by
  norm_num [winLen, tiedC1, tiedC2, min_eq_left, min_eq_right, max_eq_left, max_eq_right]
  congr 1; ring

/-- **The window mass of the four families** (band, Lai, NV7a, NV7b; tolerance `e` for all) in closed
form.  The 15 subsets are summed by inclusion-exclusion; the class overlaps are
`|band ∩ X| = |X|`, `|Lai ∩ NV7| = 1` (one class each), `|NV7a ∩ NV7b| = 0`, and the windows are
`(8a/3, 3b]` (band), `(9a/2, 9b/2]`, `(7a/3, 7b/3]`, with band `∩` Lai `= (9a/2, 3b]` and band `∩` NV7
`= (8a/3, 7b/3]`.  The Lai/NV7 overlap terms cancel against the triple overlaps. -/
theorem tied_mass4 (e : ℕ) (a b : ℝ) :
    unionMass tiedS4 tiedC1 tiedC2 (tiedE4 e) a b =
      e * (max 0 (3 * b - 8 / 3 * a) +
        ((9 / 2 : ℝ) * (1 / 6) + 2 * ((7 / 3 : ℝ) * (1 / 6))) * max 0 (b - a) -
        (1 / 6) * max 0 (3 * b - 9 / 2 * a) - 2 * (1 / 6) * max 0 (7 / 3 * b - 8 / 3 * a)) := by
  have h1 : NESub (Fin 4) = {{0}, {1}, {2}, {3}, {0, 1}, {0, 2}, {0, 3}, {1, 2}, {1, 3}, {2, 3},
      {0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {1, 2, 3}, {0, 1, 2, 3}} := by decide
  have o0 : (overlap tiedS4 {0}).card = 36 := by decide
  have o1 : (overlap tiedS4 {1}).card = 6 := by decide
  have o2 : (overlap tiedS4 {2}).card = 6 := by decide
  have o3 : (overlap tiedS4 {3}).card = 6 := by decide
  have o01 : (overlap tiedS4 {0, 1}).card = 6 := by decide
  have o02 : (overlap tiedS4 {0, 2}).card = 6 := by decide
  have o03 : (overlap tiedS4 {0, 3}).card = 6 := by decide
  have o12 : (overlap tiedS4 {1, 2}).card = 1 := by decide
  have o13 : (overlap tiedS4 {1, 3}).card = 1 := by decide
  have o23 : (overlap tiedS4 {2, 3}).card = 0 := by decide
  have o012 : (overlap tiedS4 {0, 1, 2}).card = 1 := by decide
  have o013 : (overlap tiedS4 {0, 1, 3}).card = 1 := by decide
  have o023 : (overlap tiedS4 {0, 2, 3}).card = 0 := by decide
  have o123 : (overlap tiedS4 {1, 2, 3}).card = 0 := by decide
  have o0123 : (overlap tiedS4 {0, 1, 2, 3}).card = 0 := by decide
  have ht : Nat.totient 126 = 36 := by decide
  have c1 : (#({0} : Finset (Fin 4))) = 1 := by decide
  have c2 : (#({0, 1} : Finset (Fin 4))) = 2 := by decide
  have c3 : (#({0, 1, 2} : Finset (Fin 4))) = 3 := by decide
  have c4 : (#({0, 1, 2, 3} : Finset (Fin 4))) = 4 := by decide
  have cs2' : (#({1, 2} : Finset (Fin 4))) = 2 ∧ (#({1, 3} : Finset (Fin 4))) = 2 ∧
      (#({0, 2} : Finset (Fin 4))) = 2 ∧ (#({0, 3} : Finset (Fin 4))) = 2 ∧
      (#({2, 3} : Finset (Fin 4))) = 2 ∧ (#({0, 1, 3} : Finset (Fin 4))) = 3 ∧
      (#({0, 2, 3} : Finset (Fin 4))) = 3 ∧ (#({1, 2, 3} : Finset (Fin 4))) = 3 := by decide
  obtain ⟨c5, c6, c7, c8, c9, c10, c11, c12⟩ := cs2'
  unfold unionMass
  rw [h1, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  rw [minTol_tiedE4 e (by decide), minTol_tiedE4 e (by decide), minTol_tiedE4 e (by decide),
    minTol_tiedE4 e (by decide), minTol_tiedE4 e (by decide), minTol_tiedE4 e (by decide),
    minTol_tiedE4 e (by decide), minTol_tiedE4 e (by decide), minTol_tiedE4 e (by decide),
    minTol_tiedE4 e (by decide), minTol_tiedE4 e (by decide), minTol_tiedE4 e (by decide),
    minTol_tiedE4 e (by decide), minTol_tiedE4 e (by decide), minTol_tiedE4 e (by decide)]
  simp only [o0, o1, o2, o3, o01, o02, o03, o12, o13, o23, o012, o013, o023, o123, o0123, ht,
    tied_winLen_0, tied_winLen_1, tied_winLen_2, tied_winLen_3, tied_winLen_01, tied_winLen_02,
    tied_winLen_03, tied_winLen_12, tied_winLen_13, tied_winLen_012, tied_winLen_013,
    c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, Finset.card_singleton, Nat.cast_zero, zero_div, mul_zero,
    zero_mul, add_zero]
  have x1 : max 0 ((9 / 2 : ℝ) * (b - a)) = (9 / 2) * max 0 (b - a) := by
    rw [mul_max_of_nonneg _ _ (by norm_num), mul_zero]
  have x2 : max 0 ((7 / 3 : ℝ) * (b - a)) = (7 / 3) * max 0 (b - a) := by
    rw [mul_max_of_nonneg _ _ (by norm_num), mul_zero]
  rw [x1, x2]
  push_cast
  norm_num
  ring

/-- **LB13, plane (`e = 4`)**: `β = 875/100000`; the band, Lai and NV7 windows give the mass
`1.0000702 > 1`. -/
theorem plane_unionWindowOK4 :
    UnionWindowOK tiedS4 tiedC1 tiedC2 (tiedE4 4) (3 / laiEta) (3 / laiEta + 875 / 100000) := by
  unfold UnionWindowOK
  rw [tied_mass4]
  have h1 : max 0 (3 * (3 / laiEta + 875 / 100000) - 8 / 3 * (3 / laiEta)) =
      3 * (3 / laiEta + 875 / 100000) - 8 / 3 * (3 / laiEta) :=
    max_eq_right (by unfold laiEta; norm_num)
  have h2 : max 0 (3 / laiEta + 875 / 100000 - 3 / laiEta) = 875 / 100000 := by
    rw [add_sub_cancel_left]; exact max_eq_right (by norm_num)
  have h3 : max 0 (3 * (3 / laiEta + 875 / 100000) - 9 / 2 * (3 / laiEta)) = 0 :=
    max_eq_left (by unfold laiEta; norm_num)
  have h4 : max 0 (7 / 3 * (3 / laiEta + 875 / 100000) - 8 / 3 * (3 / laiEta)) = 0 :=
    max_eq_left (by unfold laiEta; norm_num)
  rw [h1, h2, h3, h4]
  unfold laiEta
  norm_num

/-- **LB13, ratio (`e = 1`)**: `β = 19186/100000`; the band and NV7 windows overlap and the overlap is
counted once; the mass is `1.0000076 > 1`. -/
theorem ratio_unionWindowOK4 :
    UnionWindowOK tiedS4 tiedC1 tiedC2 (tiedE4 1) (3 / laiEta) (3 / laiEta + 19186 / 100000) := by
  unfold UnionWindowOK
  rw [tied_mass4]
  have h1 : max 0 (3 * (3 / laiEta + 19186 / 100000) - 8 / 3 * (3 / laiEta)) =
      3 * (3 / laiEta + 19186 / 100000) - 8 / 3 * (3 / laiEta) :=
    max_eq_right (by unfold laiEta; norm_num)
  have h2 : max 0 (3 / laiEta + 19186 / 100000 - 3 / laiEta) = 19186 / 100000 := by
    rw [add_sub_cancel_left]; exact max_eq_right (by norm_num)
  have h3 : max 0 (3 * (3 / laiEta + 19186 / 100000) - 9 / 2 * (3 / laiEta)) = 0 :=
    max_eq_left (by unfold laiEta; norm_num)
  have h4 : max 0 (7 / 3 * (3 / laiEta + 19186 / 100000) - 8 / 3 * (3 / laiEta)) =
      7 / 3 * (3 / laiEta + 19186 / 100000) - 8 / 3 * (3 / laiEta) :=
    max_eq_right (by unfold laiEta; norm_num)
  rw [h1, h2, h3, h4]
  unfold laiEta
  norm_num

/-- **LB13, plane**: `ρ (3/η + β) < 27.49`. -/
theorem plane_threshold4 :
    (4294856306 / 10 ^ 8 : ℝ) * (3 / laiEta + 875 / 100000) < 27.49 := by
  unfold laiEta; norm_num

/-- **LB13, ratio**: `ρ (3/η + β) < 35.3495 < 35.35` (the root passes to `35.35` by
`plain_measure_smul`). -/
theorem ratio_threshold4 :
    (4294856306 / 10 ^ 8 : ℝ) * (3 / laiEta + 19186 / 100000) < 35.3495 := by
  unfold laiEta; norm_num

/-- Transfer of `UnionWindowOK` to four `TiedNV` families whose data are those of `tiedS4`,
`tiedC1`, `tiedC2`, `tiedE4 e` (the band instance of Agent W2 plugs in here). -/
theorem windowOK_of_fields4 {Fam : PolyFamily} {scale : Fam.ι → ℕ} {W : ℤ → ℕ → ℕ} {e : ℕ}
    {a b : ℝ} (F : Fin 4 → TiedNV Fam scale 126 W) (hS : ∀ i, (F i).S = tiedS4 i)
    (hc₁ : ∀ i, (F i).c₁ = tiedC1 i) (hc₂ : ∀ i, (F i).c₂ = tiedC2 i)
    (he : ∀ i, (F i).e = tiedE4 e i)
    (h : UnionWindowOK tiedS4 tiedC1 tiedC2 (tiedE4 e) a b) :
    UnionWindowOK (fun i => (F i).S) (fun i => (F i).c₁) (fun i => (F i).c₂) (fun i => (F i).e)
      a b := by
  have e1 : (fun i => (F i).S) = tiedS4 := funext hS
  have e2 : (fun i => (F i).c₁) = tiedC1 := funext hc₁
  have e2' : (fun i => (F i).c₂) = tiedC2 := funext hc₂
  have e3 : (fun i => (F i).e) = tiedE4 e := funext he
  rw [e1, e2, e2', e3]; exact h

/-- **The member choice of the band**: for a prime `ℓ ≥ 100` with `8 x / 3 < ℓ ≤ 3 y` (`x ≤ y`) there is
a member `n` with `8 n < 3 ℓ`, `ℓ + 1 < 3 n` (that is `8n/3 < ℓ < 3n - 1`) and `x - 2 ≤ n ≤ y + 2`.
This is the `exists_mem` field of the band `TiedNV` with `c₁ = 8/3`, `c₂ = 3`, `D' = 2`. -/
theorem band_exists_n {ℓ : ℕ} (hℓ : 100 ≤ ℓ) {x y : ℝ} (hxy : x ≤ y) (hx : (8 / 3 : ℝ) * x < ℓ)
    (hy : (ℓ : ℝ) ≤ 3 * y) :
    ∃ n : ℕ, 8 * n < 3 * ℓ ∧ ℓ + 1 < 3 * n ∧ x - 2 ≤ (n : ℝ) ∧ (n : ℝ) ≤ y + 2 := by
  have hℓR : (100 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  set m : ℝ := max (((ℓ : ℝ) + 1) / 3) (x - 2) with hm
  have hm1 : ((ℓ : ℝ) + 1) / 3 ≤ m := le_max_left _ _
  have hm2 : x - 2 ≤ m := le_max_right _ _
  have hm0 : 0 ≤ m := le_trans (by positivity) hm1
  have hm3 : m + 1 < 3 * (ℓ : ℝ) / 8 := by
    have : m < 3 * (ℓ : ℝ) / 8 - 1 := by
      rw [hm]; apply max_lt <;> linarith
    linarith
  have hm4 : m + 1 ≤ y + 2 := by
    have : m ≤ y + 1 := by
      rw [hm]; apply max_le <;> linarith
    linarith
  have hf1 : m < (⌊m⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one m
  have hf2 : (⌊m⌋₊ : ℝ) ≤ m := Nat.floor_le hm0
  refine ⟨⌊m⌋₊ + 1, ?_, ?_, ?_, ?_⟩
  · have : (8 : ℝ) * ((⌊m⌋₊ : ℝ) + 1) < 3 * ℓ := by linarith
    exact_mod_cast this
  · have : (ℓ : ℝ) + 1 < 3 * ((⌊m⌋₊ : ℝ) + 1) := by linarith
    exact_mod_cast this
  · push_cast; linarith
  · push_cast; linarith

/-- A line family: a `TiedNV` over modulus `126` from residue-class statements.  The class set is
`classSet 126 m' r0`, the exceptions contain every prime below `11`, the tied member of the prime `ℓ`
is `mem ℓ` with `ℓ = c * scale (mem ℓ) + d`, and the class-dependent fields are given in the form
`ℓ % m' = r0`.  The slope interval is `[c, c]`, the offset tolerance is `|d| / c`. -/
noncomputable def tiedOfClass {Fam : PolyFamily} {scale : Fam.ι → ℕ} {W : ℤ → ℕ → ℕ}
    (m' r0 : ℕ) (hm' : m' ∣ 126) (c d : ℝ) (hc : 0 < c) (e : ℕ) (exc : Finset ℕ)
    (hexc : ∀ ℓ : ℕ, ℓ.Prime → ℓ < 11 → ℓ ∈ exc) (mem : ℕ → Fam.ι)
    (adm : ∀ ℓ : ℕ, ℓ.Prime → ℓ % m' = r0 → ℓ ∉ exc → Fam.Adm (mem ℓ))
    (size_eq : ∀ ℓ : ℕ, ℓ.Prime → ℓ % m' = r0 → ℓ ∉ exc →
      (ℓ : ℝ) = c * (scale (mem ℓ) : ℝ) + d)
    (Bad : ℕ → ℤ → ℕ → Prop) (bad_dvd : ∀ (ℓ : ℕ) (p : ℤ) (q : ℕ), Bad ℓ p q → ℓ ^ e ∣ W p q)
    (nv : ∀ ℓ : ℕ, ℓ.Prime → ℓ % m' = r0 → ℓ ∉ exc → ∀ (p : ℤ) (q : ℕ), 0 < q →
      ¬ Bad ℓ p q → Fam.evalQ (mem ℓ) ((p : ℚ) / (q : ℚ)) ≠ 0) :
    TiedNV Fam scale 126 W where
  S := classSet 126 m' r0
  S_unit := classSet_unit
  c₁ := c
  c₂ := c
  c₁_pos := hc
  c₁_le := le_rfl
  D' := |d| / c
  D'_nonneg := div_nonneg (abs_nonneg _) hc.le
  e := e
  exc := exc
  rel := fun ℓ n => n = mem ℓ
  exists_mem := fun ℓ hp hcl hex x y _ hx hy => by
    have hs := size_eq ℓ hp
      ((mem_classSet_iff hp (by by_contra h; exact hex (hexc ℓ hp (by omega))) hm').mp hcl) hex
    refine ⟨mem ℓ, rfl, ?_, ?_⟩
    · by_contra hlt
      push Not at hlt
      have key : c * (x - |d| / c) = c * x - |d| := by field_simp
      have := mul_lt_mul_of_pos_left hlt hc
      rw [key] at this
      linarith [le_abs_self d]
    · by_contra hlt
      push Not at hlt
      have key : c * (y + |d| / c) = c * y + |d| := by field_simp
      have := mul_lt_mul_of_pos_left hlt hc
      rw [key] at this
      linarith [neg_abs_le d]
  adm := fun ℓ hp hcl hex n hn => by
    subst hn
    exact adm ℓ hp
      ((mem_classSet_iff hp (by by_contra h; exact hex (hexc ℓ hp (by omega))) hm').mp hcl) hex
  Bad := Bad
  bad_dvd := bad_dvd
  nv := fun ℓ hp hcl hex n hn => by
    subst hn
    exact nv ℓ hp
      ((mem_classSet_iff hp (by by_contra h; exact hex (hexc ℓ hp (by omega))) hm').mp hcl) hex

end CatalanCore.Lai
