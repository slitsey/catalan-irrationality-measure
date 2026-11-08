module

public import CatalanCore.Uniform.Bank.Halves.Frame
public import CatalanCore.Uniform.Content.BankShared.Inst.TwoTerm
public import CatalanCore.Uniform.Content.BankShared.TwoTerm.Trop
public import CatalanCore.Uniform.Content.BankShared.Check.Prefix
public import CatalanCore.Uniform.Support.Producer
public import CatalanCore.Arith.Hybrid.PieceTools

@[expose] public section
set_option Elab.async false

/-!
# The two-term content route, generic in the slope `c` (lane H, wave P210-PI; ledger P210, P213, Z04)

`HalvesContent.Auto` proves `CatValid` and `PreValid` of the half-shift frame `halves` for the slope `c = 3/10` and the
data of the C1 bank.  Both proofs are generic in `c`: `catValid_bankUFwP` and `pre_gle_any` take `c` as a parameter
and ask for `2 ≤ c K`, `q (2 + c) ≤ c N₁` and for the border inequalities of `altGeom c` (`altGeom_border_nat`),
which are linear for a rational `c = cn / cd`.  This module states them once, for every `c`, and transports the
family of the frame to the family of two sequences by `Mn = lw / 4`:

* `halves_catValid_gen`, `halves_preValid_gen`: the two statements, for any catalogue `wins`, `pres`;
* `halves_catValid_c3_10`, `halves_preValid_c3_10`: the instance `c = 3/10` (`K = 9`, `N₁ = 50`, budget `(5, 56)`,
  `α₀ = 23/10`), the statements of `HalvesContent.Auto.halves_catValid`, `halves_preValid`;
* `halves_catValid_c6_41`, `halves_preValid_c6_41`: the instance `c = 6/41` (`K = 14`, `N₁ = 50`, budget `(5, 56)`,
  `α₀ = 22/10`) of the plane 2;
* `seq_content_of_halves`: if `Mn = lw / 4` (the Löwner entries of `(f, g)` are `4` times those of `halves`) the content
  of `AltEven c halves` is the content of the even-scale family `seqFamily f g` of the sequences.
-/

namespace CatalanCore.Uniform.Bank.Plane2.TwoTermContent
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape
  CatalanCore.Uniform.Content.BankShared CatalanCore.Uniform.Content.BankShared.Check
  CatalanCore.Uniform.Content.BankShared.TwoTerm CatalanCore.Uniform.Content.BankShared.Inst
  CatalanCore.Uniform.Content.SmallPrimes CatalanCore.Arith CatalanCore.Arith.Hybrid
  CatalanFrames.HybCommon CatalanFrames.HybGen CatalanCore.Uniform.Bank.Halves
  CatalanCore.Uniform.Content.RankProducer CatalanCore.Uniform.Content.Smith
  CatalanCore.Uniform.Support Polynomial

theorem cFr_halves : cFr halves ≤ 16 := by decide +kernel

/-! ### `CatValid` -/

/-- **`CatValid` of the half-shift frame for the two-term catalogue** `tableT ++ [LP1, LP2w, R, S] ++ windows ++
prefixes`, at every slope `0 < c ≤ 1` with `2 ≤ c K` and `2 (2 + c) ≤ c N₁`. -/
theorem halves_catValid_gen (c : ℚ) (hc : 0 < c) (hc1 : c ≤ 1) (K N1 : ℕ) (hK : 2 ≤ c * K)
    (hN1 : 2 * (2 + c) ≤ c * N1) (depth : ℕ) (wins : List (ℕ × ℕ)) (pres : List (ℕ × ℕ × ℕ)) :
    CatValid c hc halves depth 2 1 4 (max (NFr (1 / halves.norm) (-1 / halves.norm) 2 K) N1)
      (tableT ++ ([brLP1, brLP2w, brRank, brS] ++ wins.map (fun w => brWin w.1 w.2)) ++
        pres.map (fun x => brPre x.1 x.2.1 x.2.2)) :=
  catValid_bankUFwP (twoTermInst halves_shift)
    (twoTerm_arithmetic_small halves_shift (by norm_num) (by norm_num) (by norm_num)).L_eq
    (twoTerm_levels halves_shift) c hc hc1 halves_twoTerm
    (nm := 2 * 2) (by norm_num [halves, CatalanFrames.Thirds.thirdsFrame]) depth 4 K N1
    hK (by exact_mod_cast hN1) (by norm_num) le_rfl
    (twoTerm_hP halves_shift (by norm_num) (by norm_num)) (twoTerm_hkq halves_shift (by norm_num))
    wins pres

/-- `c = 3/10`: the statement of `HalvesContent.Auto.halves_catValid`. -/
theorem halves_catValid_c3_10 (depth : ℕ) (wins : List (ℕ × ℕ)) (pres : List (ℕ × ℕ × ℕ)) :
    CatValid (3 / 10) (by norm_num) halves depth 2 1 4
      (max (NFr (1 / halves.norm) (-1 / halves.norm) 2 9) 50)
      (tableT ++ ([brLP1, brLP2w, brRank, brS] ++ wins.map (fun w => brWin w.1 w.2)) ++
        pres.map (fun x => brPre x.1 x.2.1 x.2.2)) :=
  halves_catValid_gen (3 / 10) (by norm_num) (by norm_num) 9 50 (by norm_num) (by norm_num) depth wins pres

/-- `c = 6/41` (plane 2): `K = 14` (`6 · 14 / 41 ≥ 2`), `N₁ = 50` (`2 (2 + 6/41) ≤ 6 · 50 / 41`). -/
theorem halves_catValid_c6_41 (depth : ℕ) (wins : List (ℕ × ℕ)) (pres : List (ℕ × ℕ × ℕ)) :
    CatValid (6 / 41) (by norm_num) halves depth 2 1 4
      (max (NFr (1 / halves.norm) (-1 / halves.norm) 2 14) 50)
      (tableT ++ ([brLP1, brLP2w, brRank, brS] ++ wins.map (fun w => brWin w.1 w.2)) ++
        pres.map (fun x => brPre x.1 x.2.1 x.2.2)) :=
  halves_catValid_gen (6 / 41) (by norm_num) (by norm_num) 14 50 (by norm_num) (by norm_num) depth wins pres

/-! ### `PreValid` -/

/-- **`PreValid` of the half-shift frame** (`p ≤ r / 1000`, budget `sqrtLog A C + 1`, constant `α₀ = an / ad`) at the
slope `c = cn / cd`.  The numerical hypotheses are the linear inequalities between `r` and the border size `m`
(`cn r ≤ cd (2m) + cd`, `cd (2m) < cn r + cd`, `r ≥ 2000`) that `omega` closes in every instance. -/
theorem halves_preValid_gen (c : ℚ) (hc : 0 < c) (hc1 : c ≤ 1) (cn cd : ℕ) (hcd : 0 < cd)
    (hcq : c = (cn : ℚ) / cd) (A C e an ad : ℕ) (had : 0 < ad) (hA4 : 4 ≤ A) (hC : 56 ≤ C)
    (hA : ∀ r m : ℕ, 2000 ≤ r → cn * r ≤ cd * (2 * m) + cd → cd * (2 * m) < cn * r + cd →
      2 * (r + 2 * m) ≤ A * r)
    (he : ∀ r m : ℕ, 2000 ≤ r → cn * r ≤ cd * (2 * m) + cd → cd * (2 * m) < cn * r + cd →
      2 * (r + 2 * m) ≤ r * 2 ^ e)
    (hC1 : ∀ r m : ℕ, 2000 ≤ r → cn * r ≤ cd * (2 * m) + cd → cd * (2 * m) < cn * r + cd →
      2 * (r + m) * e ≤ C * r)
    (hC2 : ∀ r m : ℕ, 2000 ≤ r → cn * r ≤ cd * (2 * m) + cd → cd * (2 * m) < cn * r + cd →
      2 * (r + m) ≤ C * r)
    (h0 : ∀ r m : ℕ, 2000 ≤ r → cn * r ≤ cd * (2 * m) + cd → cd * (2 * m) < cn * r + cd →
      ad * (2 * (r + m)) ≤ an * r + ad)
    (t0 α0b : ℚ) (ht0 : t0 = 1 / 1000) (hα0b : α0b = (an : ℚ) / ad) (depth : ℕ) :
    PreValid c hc halves depth 2 (SmallBudget.add (SmallBudget.sqrtLog A C) SmallBudget.unit) t0 α0b := by
  intro i hi p _ _ h
  have hp : p.Prime := Fact.out
  have e1 : ((t0 : ℚ) : ℝ) = ((1 : ℕ) : ℝ) / ((1000 : ℕ) : ℝ) := by rw [ht0]; norm_num
  rw [e1, floor_frac 1 1000 i.1] at h
  have h1000 : 1000 * p ≤ i.1 := by omega
  have hp2 := hp.two_le
  have hr2 : i.1 % 2 = 0 := hi.2
  have hr : 2000 ≤ i.1 := by omega
  obtain ⟨hb1, hb2⟩ := altGeom_border_nat c hc cn cd hcd hcq hr2
  set m := (altGeom c hc).borderSize i.1 with hm
  have hbad : p ∈ (twoTermInst halves_shift).cd.bad → p * p ≤ A * i.1 := by
    intro hpb
    have hp_le : p ≤ 2 := twoTerm_bad_le halves_shift hpb
    have h4 : p * p ≤ 2 * 2 := Nat.mul_le_mul hp_le hp_le
    have : 4 * 1 ≤ A * i.1 := Nat.mul_le_mul hA4 (by omega)
    omega
  have hadR : (0 : ℝ) < ad := by exact_mod_cast had
  have h0R : 2 * ((i.1 : ℝ) + m) ≤ ((an : ℝ) / ad) * i.1 + 1 := by
    have h0' : (ad : ℝ) * (2 * ((i.1 : ℝ) + m)) ≤ an * i.1 + ad := by
      exact_mod_cast h0 i.1 m hr hb1 hb2
    have : ((an : ℝ) / ad) * i.1 + 1 = (an * i.1 + ad) / ad := by field_simp
    rw [this, le_div_iff₀ hadR]
    linarith
  obtain ⟨n, hn, hle⟩ := pre_gle_any (twoTermInst halves_shift)
    (twoTerm_arithmetic_small halves_shift (by norm_num) (by norm_num) (by norm_num)).L_eq
    c hc hc1 depth i hr2 (by omega) p A C e 16 ((an : ℝ) / ad) (by positivity) cFr_halves (by omega) hbad
    (hA i.1 m hr hb1 hb2) (he i.1 m hr hb1 hb2) (hC1 i.1 m hr hb1 hb2) (hC2 i.1 m hr hb1 hb2) h0R
    (by omega)
  refine ⟨n, hn, ?_⟩
  have e2 : ((α0b : ℚ) : ℝ) = (an : ℝ) / ad := by rw [hα0b]; push_cast; rfl
  rw [e2]
  exact hle

/-- `c = 3/10`: the statement of `HalvesContent.Auto.halves_preValid`. -/
theorem halves_preValid_c3_10 (depth : ℕ) :
    PreValid (3 / 10) (by norm_num) halves depth 2
      (SmallBudget.add (SmallBudget.sqrtLog 5 56) SmallBudget.unit) (1 / 1000) (23 / 10) :=
  halves_preValid_gen (3 / 10) (by norm_num) (by norm_num) 3 10 (by norm_num) (by norm_num) 5 56 3 23 10
    (by norm_num) (by norm_num) (by norm_num)
    (by intros; omega) (by intros; norm_num; omega) (by intros; omega) (by intros; omega) (by intros; omega)
    _ _ rfl (by norm_num) depth

/-- `c = 6/41` (plane 2): the same budget `(5, 56)` and `α₀ = 22/10 ≥ 2 (1 + 3/41)`. -/
theorem halves_preValid_c6_41 (t0 α0b : ℚ) (ht0 : t0 = 1 / 1000) (hα0b : α0b = 22 / 10) (depth : ℕ) :
    PreValid (6 / 41) (by norm_num) halves depth 2
      (SmallBudget.add (SmallBudget.sqrtLog 5 56) SmallBudget.unit) t0 α0b :=
  halves_preValid_gen (6 / 41) (by norm_num) (by norm_num) 6 41 (by norm_num) (by norm_num) 5 56 3 22 10
    (by norm_num) (by norm_num) (by norm_num)
    (by intros; omega) (by intros; norm_num; omega) (by intros; omega) (by intros; omega) (by intros; omega)
    t0 α0b ht0 (by rw [hα0b]; norm_num) depth

/-! ### From the frame to the sequences -/

/-- Scaling of the argument: if every member polynomial of `Q₂` is `4 ^ k` times that of `Q₁` at `x / 4`, with
`k ≥ deg`, the content of `Q₁` is the content of `Q₂`. -/
theorem hasScaledContent_comp4 (c : ℚ) (hc : 0 < c) (const1 const2 : ℝ) (depth : ℕ)
    (Q1 Q2 : NodeFamily.Index (altGeom c hc).geometry → ℚ[X])
    (k : NodeFamily.Index (altGeom c hc).geometry → ℕ) (hk : ∀ i, i.2.card ≤ k i)
    (hQ : ∀ i (x : ℚ), (Q2 i).eval x = 4 ^ k i * (Q1 i).eval (x / 4)) {Λ : ℝ}
    (h : HasScaledContent (AltEvenFam c hc const1 depth Q1) (altGeom c hc).scale Λ) :
    HasScaledContent (AltEvenFam c hc const2 depth Q2) (altGeom c hc).scale Λ := by
  obtain ⟨den, hpos, hint, hlog⟩ := h
  refine ⟨den, hpos, ?_, hlog⟩
  intro n hn p q hq
  obtain ⟨z, hz⟩ := hint n hn p (4 * q) (by omega)
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le (hk n)
  refine ⟨4 ^ j * z, ?_⟩
  have e1 : (AltEvenFam c hc const2 depth Q2).evalQ n ((p : ℚ) / q) =
      4 ^ k n * (AltEvenFam c hc const1 depth Q1).evalQ n ((p : ℚ) / ((4 * q : ℤ) : ℚ)) := by
    show (Q2 n).eval ((p : ℚ) / q) = 4 ^ k n * (Q1 n).eval ((p : ℚ) / ((4 * q : ℤ) : ℚ))
    have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
    have hx : ((p : ℚ) / q) / 4 = (p : ℚ) / ((4 * q : ℤ) : ℚ) := by
      push_cast
      field_simp
    refine (hQ n _).trans ?_
    rw [hx]
  have hdeg : (AltEvenFam c hc const2 depth Q2).deg n = n.2.card := rfl
  have hdeg1 : (AltEvenFam c hc const1 depth Q1).deg n = n.2.card := rfl
  rw [hdeg1] at hz
  rw [hdeg, e1]
  push_cast at hz ⊢
  rw [hj]
  calc (q : ℚ) ^ n.2.card * den n * (4 ^ (n.2.card + j) * (AltEvenFam c hc const1 depth Q1).evalQ n (p / (4 * q)))
      = 4 ^ j * ((4 * (q : ℚ)) ^ n.2.card * den n * (AltEvenFam c hc const1 depth Q1).evalQ n (p / (4 * q))) := by
        ring
    _ = 4 ^ j * z := by rw [hz]

/-- The member polynomials of the sequences are `4 ^ (|S| + m)` times those of the frame at `x / 4`. -/
theorem hQ_halves (c : ℚ) (hc : 0 < c) (f g : ℕ → ℚ)
    (hMn : ∀ a b : ℕ, halves.Mn a b = (1 / 4) * lw f g a b) (depth : ℕ)
    (i : NodeFamily.Index (altGeom c hc).geometry) (x : ℚ) :
    (SeqFamily.poly f g (altGeom c hc).geometry i).eval x =
      4 ^ (i.2.card + ((altGeom c hc).geometry i.1).k) *
        (NodeFamily.polynomial halves (altGeom c hc).geometry i).eval (x / 4) := by
  have h4 : ∀ a b, lw f g a b = 4 * halves.Mn a b := fun a b => by rw [hMn]; ring
  have e2 := SeqFamily.evalQ_poly f g 0 (altGeom c hc).geometry depth i x
  have e1 := NodeFamily.evalQ_polynomial halves (altGeom c hc).geometry depth i (x / 4)
  change (SeqFamily.poly f g _ i).eval x = _ at e2
  change (NodeFamily.polynomial halves _ i).eval (x / 4) = _ at e1
  rw [e2, e1]
  have hmat : seqFullN f g (fun a : i.2 => ((a.1 : ((altGeom c hc).geometry i.1).C) : ℕ))
      ((altGeom c hc).geometry i.1).xs ((altGeom c hc).geometry i.1).ys x =
      (4 : ℚ) • Rect.FullN halves (fun a : i.2 => ((a.1 : ((altGeom c hc).geometry i.1).C) : ℕ))
        ((altGeom c hc).geometry i.1).xs ((altGeom c hc).geometry i.1).ys (x / 4) := by
    ext a b
    rcases a with a | a <;> rcases b with b | b <;>
      simp [seqFullN, Rect.FullN, Rect.blkA, Rect.blkB, Rect.blkC, Rect.blkD, Rect.Blk, Matrix.fromBlocks,
        Matrix.one_apply, h4]
    all_goals (split_ifs <;> ring)
  rw [hmat, Matrix.det_smul]
  rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_fin]

/-- **From the frame to the sequences.**  If the Löwner entries of `(f, g)` are `4` times those of `halves`, the
content of the family of the frame is the content of the even-scale family of the sequences, for the same `Λ`. -/
theorem seq_content_of_halves (c : ℚ) (hc : 0 < c) (f g : ℕ → ℚ)
    (hMn : ∀ a b : ℕ, halves.Mn a b = (1 / 4) * lw f g a b) (const : ℝ) (depth : ℕ) {Λ : ℝ}
    (h : HasScaledContent (AltEven c hc halves depth) (altGeom c hc).scale Λ) :
    HasScaledContent ((seqFamily f g const (altGeom c hc).geometry depth).restrictAdm
        (fun i => (altGeom c hc).scale i % 2 = 0)) (altGeom c hc).scale Λ := by
  have key : HasScaledContent (AltEvenFam c hc const depth (SeqFamily.poly f g (altGeom c hc).geometry))
      (altGeom c hc).scale Λ :=
    hasScaledContent_comp4 c hc halves.const const depth _ _
      (fun i => i.2.card + ((altGeom c hc).geometry i.1).k) (fun i => Nat.le_add_right _ _)
      (fun i x => hQ_halves c hc f g hMn depth i x) h
  exact key

end CatalanCore.Uniform.Bank.Plane2.TwoTermContent
