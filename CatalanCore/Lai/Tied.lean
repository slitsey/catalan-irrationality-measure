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
* `tiedOfClass`: a `TiedNV` over modulus `126` from residue-class statements `ℓ % m' = r0`.
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
    unionMass tiedS tiedC (tiedE e) a b =
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

/-- `η = D - Λ` of the Lai roots: `D = 33.44019129`, `Λ = 28.68723663`. -/
noncomputable def laiEta : ℝ := 3344019129 / 10 ^ 8 - 2868723663 / 10 ^ 8

theorem laiEta_pos : 0 < laiEta := by unfold laiEta; norm_num

/-- **LR05, plane**: `β = 1637/10000`, tolerance `4`; the windows are disjoint and the mass is
`18007/18000 > 1`. -/
theorem plane_unionWindowOK :
    UnionWindowOK tiedS tiedC (tiedE 4) (3 / laiEta) (3 / laiEta + 1637 / 10000) := by
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
    UnionWindowOK tiedS tiedC (tiedE 1) (3 / laiEta) (3 / laiEta + 661 / 1000) := by
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
`tiedC`, `tiedE e`. -/
theorem windowOK_of_fields {Fam : PolyFamily} {scale : Fam.ι → ℕ} {W : ℤ → ℕ → ℕ} {e : ℕ} {a b : ℝ}
    (F : Fin 3 → TiedNV Fam scale 126 W) (hS : ∀ i, (F i).S = tiedS i)
    (hc : ∀ i, (F i).c = tiedC i) (he : ∀ i, (F i).e = tiedE e i)
    (h : UnionWindowOK tiedS tiedC (tiedE e) a b) :
    UnionWindowOK (fun i => (F i).S) (fun i => (F i).c) (fun i => (F i).e) a b := by
  have e1 : (fun i => (F i).S) = tiedS := funext hS
  have e2 : (fun i => (F i).c) = tiedC := funext hc
  have e3 : (fun i => (F i).e) = tiedE e := funext he
  rw [e1, e2, e3]; exact h


/-- A `TiedNV` over modulus `126` from residue-class statements: the class set is
`classSet 126 m' r0`, the exceptions contain every prime below `11`, and the class-dependent
fields are given in the form `ℓ % m' = r0`. -/
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
  c := c
  c_pos := hc
  d := d
  e := e
  exc := exc
  mem := mem
  adm := fun ℓ hp hcl hex => adm ℓ hp
    ((mem_classSet_iff hp (by by_contra h; exact hex (hexc ℓ hp (by omega))) hm').mp hcl) hex
  size_eq := fun ℓ hp hcl hex => size_eq ℓ hp
    ((mem_classSet_iff hp (by by_contra h; exact hex (hexc ℓ hp (by omega))) hm').mp hcl) hex
  Bad := Bad
  bad_dvd := bad_dvd
  nv := fun ℓ hp hcl hex => nv ℓ hp
    ((mem_classSet_iff hp (by by_contra h; exact hex (hexc ℓ hp (by omega))) hm').mp hcl) hex

end CatalanCore.Lai
