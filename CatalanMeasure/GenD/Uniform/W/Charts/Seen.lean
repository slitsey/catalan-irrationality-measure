module
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Data.Int.Init
public import Mathlib.Data.List.Range
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
@[expose] public section
set_option Elab.async false

/-!
# Seen positions and their group keys

A raw response at an active column `j ∈ [b, L)` sees the slot-polynomial coefficient at position
`e` through the covector `ψ(J, S)` exactly when `H - 1 - (j mod p) - e = S p`, `J = j / p`.
For a position `e` this determines everything:

* `ℓ_e = (H - 1 - e) mod p`, `S_e = (H - 1 - e) / p` (floor);
* the active `J` are those with `b ≤ J p + ℓ_e < L`, i.e. `jlo ≤ J < jlo + cnt`.

`seenKey H b L p e = (S_e, jlo, cnt)` is the **group key** of the position (`cnt = 0`: not seen).
The chart of the group is the stack of the covectors `ψ(jlo + i, S_e)`, `i < cnt`
(`Charts.Chart`); the weight of the group is the number of positions with that key.
-/

namespace CatalanMeasure.GenD.Uniform.W.Charts

/-- Group key `(S, jlo, cnt)` of a position. -/
abbrev Key := ℤ × ℕ × ℕ

/-- The group key of position `e`. -/
def seenKey (H b L p e : ℕ) : Key :=
  ((H - 1 - e : ℤ) / p,
    (max 0 (((b : ℤ) - ((H - 1 - e : ℤ) % p) + p - 1) / p)).toNat,
    ((((L : ℤ) - ((H - 1 - e : ℤ) % p) + p - 1) / p) -
      max 0 (((b : ℤ) - ((H - 1 - e : ℤ) % p) + p - 1) / p)).toNat)

/-- The positions of a group, in increasing order. -/
def posList (H b L p emax : ℕ) (κ : Key) : List ℕ :=
  (List.range emax).filter (fun e => seenKey H b L p e == κ)

theorem mem_posList {H b L p emax : ℕ} {κ : Key} {e : ℕ} :
    e ∈ posList H b L p emax κ ↔ e < emax ∧ seenKey H b L p e = κ := by
  simp [posList]

/-- **Coverage.**  An active column that sees position `e` through `(S, J)` has `S = S_e` and `J`
in the key range of `e`. -/
theorem seenKey_cover {H b L p e j : ℕ} {a : ℤ} (hp : 0 < p) (h1 : b ≤ j) (h2 : j < L)
    (ha : (H : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e = a * p) :
    (seenKey H b L p e).1 = a ∧ (seenKey H b L p e).2.1 ≤ j / p ∧
      j / p < (seenKey H b L p e).2.1 + (seenKey H b L p e).2.2 := by
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp
  have hjm : j = p * (j / p) + j % p := (Nat.div_add_mod j p).symm
  have hlt : j % p < p := Nat.mod_lt _ hp
  set J := j / p with hJ
  set l := j % p with hl
  have ht : ((H : ℤ) - 1 - e) = (l : ℤ) + p * a := by linarith
  have huniq := (Int.ediv_emod_unique hpz (a := (H : ℤ) - 1 - e) (q := a) (r := (l : ℤ))).mpr
    ⟨by linarith, by positivity, by exact_mod_cast hlt⟩
  obtain ⟨hdiv, hmod⟩ := huniq
  unfold seenKey
  simp only [hdiv, hmod, true_and]
  have h3 : ((b : ℤ) - l + p - 1) / p < (J : ℤ) + 1 := by
    rw [Int.ediv_lt_iff_lt_mul hpz]
    have : (b : ℤ) ≤ (p : ℤ) * J + l := by exact_mod_cast (hjm ▸ h1)
    nlinarith
  have h4 : ((J : ℤ) + 1) ≤ ((L : ℤ) - l + p - 1) / p := by
    rw [Int.le_ediv_iff_mul_le hpz]
    have : (p : ℤ) * J + l + 1 ≤ L := by exact_mod_cast (hjm ▸ h2)
    nlinarith
  clear_value J l
  generalize ((b : ℤ) - l + p - 1) / p = A at h3 ⊢
  generalize ((L : ℤ) - l + p - 1) / p = B at h4 ⊢
  omega

/-- The finite list of group keys of a cell: `S ∈ [Slo, Shi]`, `jlo ∈ {c, c+1}`,
upper end `jhi1 ∈ {c', c'+1}` (`cnt = jhi1 - jlo`), where `c = ⌊b/p⌋`, `c' = ⌊L/p⌋`. -/
def typesOf (c c' : ℕ) (Slo Shi : ℤ) : List Key :=
  (List.range (Shi + 1 - Slo).toNat).flatMap fun (s : ℕ) =>
    [c, c + 1].flatMap fun (jl : ℕ) => [c', c' + 1].map fun (jh : ℕ) =>
      (Slo + (s : ℤ), jl, ((jh : ℤ) - (jl : ℤ)).toNat)

theorem mem_typesOf {c c' jl jh : ℕ} {S Slo Shi : ℤ} (h1 : Slo ≤ S) (h2 : S ≤ Shi)
    (hl : jl = c ∨ jl = c + 1) (hh : jh = c' ∨ jh = c' + 1) :
    (S, jl, ((jh : ℤ) - jl).toNat) ∈ typesOf c c' Slo Shi := by
  have hS : Slo + ((S - Slo).toNat : ℤ) = S := by omega
  unfold typesOf
  simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_map]
  have hn : (S - Slo).toNat < (Shi + 1 - Slo).toNat := by omega
  refine ⟨(S - Slo).toNat, hn, jl, ?_, jh, ?_, ?_⟩
  · simpa using hl
  · simpa using hh
  · rw [hS]

/-- **Every seen position has a key in the generic list**: the key of a position depends only on
`S_e`, on `b mod p` versus `ℓ_e`, and on `L mod p` versus `ℓ_e`. -/
theorem seenKey_mem_typesOf {H b L p e : ℕ} {Slo Shi : ℤ} (hp : 0 < p)
    (hlo : Slo ≤ ((H : ℤ) - 1 - e) / p) (hhi : ((H : ℤ) - 1 - e) / p ≤ Shi) :
    seenKey H b L p e ∈ typesOf (b / p) (L / p) Slo Shi := by
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp
  have hl0 : 0 ≤ ((H : ℤ) - 1 - e) % p := Int.emod_nonneg _ hpz.ne'
  have hl1 : ((H : ℤ) - 1 - e) % p < p := Int.emod_lt_of_pos _ hpz
  have hkey : seenKey H b L p e =
      (((H : ℤ) - 1 - e) / p,
        (((b : ℤ) - (((H : ℤ) - 1 - e) % p) + p - 1) / p).toNat,
        ((((((L : ℤ) - (((H : ℤ) - 1 - e) % p) + p - 1) / p).toNat : ℕ) : ℤ) -
          ((((b : ℤ) - (((H : ℤ) - 1 - e) % p) + p - 1) / p).toNat : ℕ)).toNat) := by
    unfold seenKey
    have hA : 0 ≤ ((b : ℤ) - (((H : ℤ) - 1 - e) % p) + p - 1) / p :=
      Int.ediv_nonneg (by omega) hpz.le
    have hB : 0 ≤ ((L : ℤ) - (((H : ℤ) - 1 - e) % p) + p - 1) / p :=
      Int.ediv_nonneg (by omega) hpz.le
    generalize ((b : ℤ) - (((H : ℤ) - 1 - e) % p) + p - 1) / p = A at hA ⊢
    generalize ((L : ℤ) - (((H : ℤ) - 1 - e) % p) + p - 1) / p = B at hB ⊢
    refine Prod.ext rfl (Prod.ext ?_ ?_) <;> simp only <;> omega
  rw [hkey]
  generalize ((H : ℤ) - 1 - e) % p = l at hl0 hl1 ⊢
  have hA1 : (b : ℤ) / p ≤ ((b : ℤ) - l + p - 1) / p :=
    Int.ediv_le_ediv hpz (by omega)
  have hA2 : ((b : ℤ) - l + p - 1) / p ≤ (b : ℤ) / p + 1 := by
    have h1 : ((b : ℤ) - l + p - 1) / p ≤ ((b : ℤ) + p - 1) / p := Int.ediv_le_ediv hpz (by omega)
    have h2 : ((b : ℤ) + p - 1) / p < (b : ℤ) / p + 2 := by
      rw [Int.ediv_lt_iff_lt_mul hpz]
      have := Int.emod_add_mul_ediv (b : ℤ) p
      have h3 := Int.emod_lt_of_pos (b : ℤ) hpz
      nlinarith
    omega
  have hB1 : (L : ℤ) / p ≤ ((L : ℤ) - l + p - 1) / p :=
    Int.ediv_le_ediv hpz (by omega)
  have hB2 : ((L : ℤ) - l + p - 1) / p ≤ (L : ℤ) / p + 1 := by
    have h1 : ((L : ℤ) - l + p - 1) / p ≤ ((L : ℤ) + p - 1) / p := Int.ediv_le_ediv hpz (by omega)
    have h2 : ((L : ℤ) + p - 1) / p < (L : ℤ) / p + 2 := by
      rw [Int.ediv_lt_iff_lt_mul hpz]
      have := Int.emod_add_mul_ediv (L : ℤ) p
      have h3 := Int.emod_lt_of_pos (L : ℤ) hpz
      nlinarith
    omega
  have hbpos : 0 ≤ (b : ℤ) / p := Int.ediv_nonneg (by positivity) hpz.le
  have hLpos : 0 ≤ (L : ℤ) / p := Int.ediv_nonneg (by positivity) hpz.le
  refine mem_typesOf hlo hhi ?_ ?_
  · omega
  · omega

/-- The `J` bound of a seen key: `jlo + cnt ≤ ⌊L/p⌋ + 1`. -/
theorem seenKey_sum_le {H b L p e : ℕ} (hp : 0 < p)
    (hc : 0 < (seenKey H b L p e).2.2) :
    (seenKey H b L p e).2.1 + (seenKey H b L p e).2.2 ≤ L / p + 1 := by
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp
  have hl0 : 0 ≤ ((H : ℤ) - 1 - e) % p := Int.emod_nonneg _ hpz.ne'
  have hl1 : ((H : ℤ) - 1 - e) % p < p := Int.emod_lt_of_pos _ hpz
  unfold seenKey at hc ⊢
  simp only at hc ⊢
  generalize ((H : ℤ) - 1 - e) % p = l at hl0 hl1 hc ⊢
  have hLd : ((L / p : ℕ) : ℤ) = (L : ℤ) / p := by push_cast; rfl
  have hB2 : ((L : ℤ) - l + p - 1) / p ≤ (L : ℤ) / p + 1 := by
    have h1 : ((L : ℤ) - l + p - 1) / p ≤ ((L : ℤ) + p - 1) / p := Int.ediv_le_ediv hpz (by omega)
    have h2 : ((L : ℤ) + p - 1) / p < (L : ℤ) / p + 2 := by
      rw [Int.ediv_lt_iff_lt_mul hpz]
      have := Int.emod_add_mul_ediv (L : ℤ) p
      have h3 := Int.emod_lt_of_pos (L : ℤ) hpz
      nlinarith
    omega
  have hA : 0 ≤ ((b : ℤ) - l + p - 1) / p := Int.ediv_nonneg (by omega) hpz.le
  have hLpos : 0 ≤ (L : ℤ) / p := Int.ediv_nonneg (by positivity) hpz.le
  generalize ((b : ℤ) - l + p - 1) / p = A at hA hc ⊢
  generalize ((L : ℤ) - l + p - 1) / p = B at hB2 hc ⊢
  omega

end CatalanMeasure.GenD.Uniform.W.Charts
