module

public import CatalanCore.Lai.B83Blocks

@[expose] public section

/-! # `CatalanCore.Lai.B83OwnNode`: the own-node exact terms of the integral block (Theorem B83, ledger LB04b/LB05b, own part)

Note `N9-LAI-SMALLPRIME-NV-2026-11-20.md` §3.4, Lemmas A and C, "own nodes".  Band `8n/3 < p < 3n - 1`,
`a = p - 2n` odd, `A₂ = 6n - 2p < a`, classes `A = [0, A₂]` (multiplicity 4, nodes `j = 0, 1, 2`) and
`C = (A₂, a)` (multiplicity 3, nodes `j = 0, 1`).

For a residue `s` of `A` (resp. `C`) the node sum of `F = (X + s)^m R` (`R` an `ℤ_(p)`-integral polynomial,
`ρ = R(-s)`), taken over the nodes `k = s + jp ≤ 6n` at the point `(a, b, X'/p³)` with `a, b, X' ∈ ℤ_(p)`, satisfies

* `p⁴ · Σ_j c_k (u_k F'(-k) + e_k F(-k)) = p^m · Z`, `Z̄ = b̄ · ĉ_s · ρ̄ · hh m`   (A, `σ = 0`),
* `p⁴ · Σ_j c_k (u_k F'(-k) + e_k F(-k)) = p^{2+m} · Z`, `Z̄ = b̄ · ĉ_s · ρ̄ · Φ_C m`   (C, `σ = 2`),

with `hh m = 4 Mb(m,1,-2,-6) + Mb(m,2,-9/4,-105/8)` (the own-node values `Φ_A`) and
`Φ_C m = Mb(m,1,-2,-10)`.  Applied to the pair `e_{r,i}·e_{r,i'}` of the basis of the note
(`e_{r,i} = (X+r)^i Π/(X+r)^{μ_r}`) this is the own-node component of the entry `ĉΨ²·h_{i+i'}`
(`own_entry_A`, `own_entry_C`); for `i + i' ≤ 4` (A) resp. `≤ 2` (C) it is the full constant `hA`, `hC` of
`B83Blocks` (`own_entry_A_hA`, `own_entry_C_hC`), and for `m = 5, 6` (A), `m = 3, 4` (C) it is `hh` resp. `Φ_C`,
which the D-node corrections must cancel (`hh_vals`, `PhiC_vals`).
-/

open Polynomial Finset CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Lai CatalanCore.Content
  CatalanCore.Lai.NV7
open scoped Nat

namespace CatalanCore.Lai.B83

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### Part 1: the point data and the generic own-residue node sum -/

/-- `u_k = -3 a H_k(2) - 2 b H_k(3)` of `J_n` at the point `(a, b, X)`. -/
noncomputable def ownU (ca cb : LocRing p) (k : ℕ) : ℚ :=
  -3 * (ca : ℚ) * Hq 2 k - 2 * (cb : ℚ) * Hq 3 k

/-- `e_k` of `J_n` at the point `(a, b, X'/p³)`. -/
noncomputable def ownE (n : ℕ) (ca cb cX : LocRing p) (k : ℕ) : ℚ :=
  laiH n k * (3 * (ca : ℚ) * Hq 2 k + 2 * (cb : ℚ) * Hq 3 k) +
    6 * ((cX : ℚ) / (p : ℚ) ^ 3 - (ca : ℚ) * Hq 3 k - (cb : ℚ) * Hq 4 k)

/-- The exact node sum over the nodes `s + jp`, `j < J`, of `F = (X + s)^m R`, scaled by `p⁴`, is
`p^{ω+m} Z` with `Z̄ = Σ_j w̄₀(j) Mb(m, j, Ū_j, Ē_j, ρ̄)` (`node_expand` at every node). -/
theorem own_sum (n s J ω m : ℕ) (hs : s < p) (R : ℚ[X]) (hR : IntPoly p R) (ρ : LocRing p)
    (hρ : (ρ : ℚ) = R.eval (-(s : ℚ))) (w0 : ℕ → ℕ)
    (hw : ∀ j < J, (laiCoef n (s + j * p) : ℚ) = (p : ℚ) ^ ω * (w0 j : ℚ))
    (U E : ℕ → LocRing p) (u e : ℕ → ℚ)
    (hU : ∀ j < J, (p : ℚ) ^ 3 * u (s + j * p) = (U j : ℚ))
    (hE : ∀ j < J, (p : ℚ) ^ 4 * e (s + j * p) = (E j : ℚ)) :
    ∃ Z : LocRing p,
      (p : ℚ) ^ 4 * ∑ j ∈ range J, (laiCoef n (s + j * p) : ℚ) *
          (u (s + j * p) * (derivative ((X + C (s : ℚ)) ^ m * R)).eval (-(Nat.cast (s + j * p) : ℚ)) +
            e (s + j * p) * ((X + C (s : ℚ)) ^ m * R).eval (-(Nat.cast (s + j * p) : ℚ))) =
        (p : ℚ) ^ (ω + m) * (Z : ℚ) ∧
      redQ p Z = ∑ j ∈ range J, (w0 j : ZMod p) * Mb m j (redQ p (U j)) (redQ p (E j)) (redQ p ρ) := by
  have key : ∀ j, ∃ z : LocRing p, j < J →
      (p : ℚ) ^ 4 * ((laiCoef n (s + j * p) : ℚ) *
          (u (s + j * p) * (derivative ((X + C (s : ℚ)) ^ m * R)).eval (-(Nat.cast (s + j * p) : ℚ)) +
            e (s + j * p) * ((X + C (s : ℚ)) ^ m * R).eval (-(Nat.cast (s + j * p) : ℚ)))) =
        (p : ℚ) ^ (ω + m) * ((w0 j : ℚ) * ((Mr m j (U j) (E j) ρ : LocRing p) : ℚ) + (p : ℚ) * (z : ℚ)) := by
    intro j
    by_cases hj : j < J
    · obtain ⟨hm, hd⟩ := mod_div_node (ℓ := p) s j hs
      obtain ⟨z, hz⟩ := node_expand (ℓ := p) (s + j * p) ω (w0 j) (u (s + j * p)) (e (s + j * p)) (U j)
        (E j) ρ (hU j hj) (hE j hj) m R hR (by rw [hm]; exact hρ)
      refine ⟨z, fun _ => ?_⟩
      rw [hm, hd] at hz
      rw [hw j hj, ← hz]
    · exact ⟨0, fun h => absurd h hj⟩
  choose z hz using key
  refine ⟨∑ j ∈ range J, ((w0 j : LocRing p) * Mr m j (U j) (E j) ρ + (p : LocRing p) * z j), ?_, ?_⟩
  · push_cast
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have := hz j (Finset.mem_range.1 hj)
    push_cast at this
    exact this
  · rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [map_add, map_mul, map_natCast, redQ_Mr, ZMod.natCast_self, zero_mul, add_zero]

/-! ### Part 2: band data at an own residue -/

section Band

theorem sig_own {n A2 a s : ℕ} (ha : a + 2 * n = p) (hA : A2 + 2 * p = 6 * n) (hA2 : A2 < a) (hs : s < a) :
    sig n p s = if s ≤ A2 then 0 else 2 := by
  rw [sig_eq_flags, bflag_eq n a A2 s hA (by omega), eflag_eq n a s ha (by omega)]
  split_ifs <;> omega

theorem h8_band {n A2 a : ℕ} (h5 : 5 ≤ p) (ha : a + 2 * n = p) (hA : A2 + 2 * p = 6 * n) (hA2 : A2 < a) :
    8 * n < p ^ 2 := by
  have h1 : 8 * n < 3 * p := by omega
  have h2 : 3 * p ≤ p ^ 2 := by nlinarith
  omega

/-- unit part `w` of `c_k`, `k = s + jp`, at an own residue `s < a`. -/
theorem unit_own {n A2 a s j : ℕ} (h5 : 5 ≤ p) (ha : a + 2 * n = p) (hA : A2 + 2 * p = 6 * n)
    (hA2 : A2 < a) (hs : s < a) (hk : s + j * p ≤ 6 * n) :
    ∃ w : ℕ, laiCoef n (s + j * p) = p ^ (if s ≤ A2 then 0 else 2) * w ∧
      (w : ZMod p) = kappa p 2 0 (if A2 < s then 1 else 0) 0 j *
        chat p A2 (2 * n) (if A2 < s then 1 else 0) 0 s := by
  have h8 := h8_band h5 ha hA hA2
  obtain ⟨w, h1, h2, -⟩ := laiCoef_unit (p := p) (n := n) h8 (by omega) (s + j * p) hk
  obtain ⟨hm, hd⟩ := mod_div_node (ℓ := p) s j (by omega)
  have hef : eflag n p s = 0 := by rw [eflag_eq n a s ha (by omega), if_neg (by omega)]
  have hbf : bflag n p s = if A2 < s then 1 else 0 := bflag_eq n a A2 s hA (by omega)
  rw [hm] at h1
  rw [hm, hd] at h2
  rw [sig_own ha hA hA2 hs] at h1
  rw [q6_eq n a A2 hA (by omega), q2_eq n a ha (by omega), r6_eq n a A2 hA (by omega),
    r2_eq n a ha (by omega), hbf, hef] at h2
  exact ⟨w, h1, h2⟩

/-- `v_j` at an `A` residue, `j = 1`. -/
theorem vL_A1 {n A2 a s : ℕ} (ha : a + 2 * n = p) (hA : A2 + 2 * p = 6 * n) (hA2 : A2 < a) (hs : s ≤ A2)
    (hk : s + 1 * p ≤ 6 * n) : vL n p (s + 1 * p) 1 = -6 := by
  have := laiDelta_class (ℓ := p) n a A2 s 1 ha hA (by omega) (by omega) (by omega) hk
  unfold vL
  rw [this, if_neg (by omega), if_neg (by omega)]
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10⟩ := Hq_vals
  norm_num [g1, g2, g3, g4, g5, g6, g7, g8, g9, g10]

/-- `v_j` at an `A` residue, `j = 2`. -/
theorem vL_A2 {n A2 a s : ℕ} (ha : a + 2 * n = p) (hA : A2 + 2 * p = 6 * n) (hA2 : A2 < a) (hs : s ≤ A2)
    (hk : s + 2 * p ≤ 6 * n) : vL n p (s + 2 * p) 2 = -105 / 8 := by
  have := laiDelta_class (ℓ := p) n a A2 s 2 ha hA (by omega) (by omega) (by omega) hk
  unfold vL
  rw [this, if_neg (by omega), if_neg (by omega)]
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10⟩ := Hq_vals
  norm_num [g1, g2, g3, g4, g5, g6, g7, g8, g9, g10]

/-- `v_j` at a `C` residue, `j = 1`. -/
theorem vL_C1 {n A2 a s : ℕ} (ha : a + 2 * n = p) (hA : A2 + 2 * p = 6 * n) (hA2 : A2 < a) (hs : A2 < s)
    (hsa : s < a) (hk : s + 1 * p ≤ 6 * n) : vL n p (s + 1 * p) 1 = -10 := by
  have := laiDelta_class (ℓ := p) n a A2 s 1 ha hA (by omega) (by omega) (by omega) hk
  unfold vL
  rw [this, if_neg (by omega), if_pos hs]
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10⟩ := Hq_vals
  norm_num [g1, g2, g3, g4, g5, g6, g7, g8, g9, g10]

theorem kappa_C1 : kappa p 2 0 1 0 1 = 4 := by
  simp [kappa, fz, Nat.factorial]
  norm_num

end Band

/-! ### Part 3: node values `Ū_k`, `Ē_k` -/

/-- `U_k = p³u_k`, `E_k = p⁴e_k` are `p`-integral with `Ū = b̄ ū_j`, `Ē = b̄ v̄_j`, `j = ⌊k/p⌋`, for
rational constants `ū_j`, `v̄_j` given by `Nu·uL j = mU`, `Nv·vL = mV`. -/
theorem own_UE (n k j : ℕ) (hk : k ≤ 6 * n) (h8 : 8 * n < p ^ 2) (hj : k / p = j) (ca cb cX : LocRing p)
    (Nu Nv : ℕ) (mU mV : ℤ) (hNu : (Nu : ZMod p) ≠ 0) (hNv : (Nv : ZMod p) ≠ 0)
    (hu : (Nu : ℚ) * uL j = mU) (hv : (Nv : ℚ) * vL n p k j = mV) :
    ∃ U E : LocRing p, (p : ℚ) ^ 3 * ownU ca cb k = (U : ℚ) ∧ (p : ℚ) ^ 4 * ownE n ca cb cX k = (E : ℚ) ∧
      redQ p U = redQ p cb * ((mU : ZMod p) / Nu) ∧ redQ p E = redQ p cb * ((mV : ZMod p) / Nv) := by
  obtain ⟨U, E, zU, zE, h1, h2, h3, h4⟩ := nv_UE (ℓ := p) n k hk h8 ca cb cX
  have hjl : j < p := by
    rw [← hj, Nat.div_lt_iff_lt_mul hp.out.pos]; nlinarith
  have cu : redQ p (⟨uL j, uL_mem (p := p) j hjl⟩ : LocRing p) = (mU : ZMod p) / Nu :=
    redQ_of_mul_eq _ Nu mU hNu (by show (Nu : ℚ) * uL j = (mU : ℚ); exact hu)
  have hmem := vL_mem (p := p) n k j h8 hk hjl
  have cv : redQ p (⟨vL n p k j, hmem⟩ : LocRing p) = (mV : ZMod p) / Nv :=
    redQ_of_mul_eq _ Nv mV hNv (by show (Nv : ℚ) * vL n p k j = (mV : ℚ); exact hv)
  refine ⟨U, E, h1, h2, ?_, ?_⟩
  · rw [← cu]
    exact redQ_ofEq U cb _ zU (by show (U : ℚ) = (cb : ℚ) * uL j + (p : ℚ) * zU; rw [← hj]; exact h3)
  · rw [← cv]
    exact redQ_ofEq E cb _ zE
      (by show (E : ℚ) = (cb : ℚ) * vL n p k j + (p : ℚ) * zE; rw [← hj]; exact h4)

section Residues

variable {n A2 a : ℕ}

private theorem nz_nat (h5 : 5 ≤ p) {N : ℕ} (hN : N = 1 ∨ N = 4 ∨ N = 8) : (N : ZMod p) ≠ 0 := by
  have h2 := two_ne_zero_zmod (p := p) h5
  rcases hN with rfl | rfl | rfl
  · simp
  · have : ((4 : ℕ) : ZMod p) = 2 ^ 2 := by norm_num
    rw [this]; exact pow_ne_zero _ h2
  · have : ((8 : ℕ) : ZMod p) = 2 ^ 3 := by norm_num
    rw [this]; exact pow_ne_zero _ h2

/-- **Own nodes of an `A` residue (Lemma A, `Φ_A`).**  `s ≤ A₂`, `F = (X + s)^m R`, nodes `s + jp`, `j = 0, 1, 2`.
`p⁴ · Σ = p^m Z`, `Z̄ = b̄ ĉ_s ρ̄ · hh m`. -/
theorem own_A (h5 : 5 ≤ p) (ha : a + 2 * n = p) (hA : A2 + 2 * p = 6 * n) (hA2 : A2 < a) {s : ℕ}
    (hs : s ≤ A2) (m : ℕ) (R : ℚ[X]) (hR : IntPoly p R) (ρ : LocRing p)
    (hρ : (ρ : ℚ) = R.eval (-(s : ℚ))) (ca cb cX : LocRing p) :
    ∃ Z : LocRing p,
      (p : ℚ) ^ 4 * ∑ j ∈ range 3, (laiCoef n (s + j * p) : ℚ) *
          (ownU ca cb (s + j * p) * (derivative ((X + C (s : ℚ)) ^ m * R)).eval (-(Nat.cast (s + j * p) : ℚ)) +
            ownE n ca cb cX (s + j * p) * ((X + C (s : ℚ)) ^ m * R).eval (-(Nat.cast (s + j * p) : ℚ))) =
        (p : ℚ) ^ m * (Z : ℚ) ∧
      redQ p Z = redQ p cb * cunit p n A2 0 s * redQ p ρ * hh p m := by
  have h8 := h8_band h5 ha hA hA2
  have h2 := two_ne_zero_zmod (p := p) h5
  have hsa : s < a := by omega
  have hsp : s < p := by omega
  have hw : ∀ j, ∃ w : ℕ, j < 3 → (laiCoef n (s + j * p) : ℚ) = (p : ℚ) ^ 0 * (w : ℚ) ∧
      (w : ZMod p) = kappa p 2 0 0 0 j * chat p A2 (2 * n) 0 0 s := by
    intro j
    by_cases hj : j < 3
    · obtain ⟨w, h1, h2'⟩ := unit_own (j := j) h5 ha hA hA2 hsa (by nlinarith)
      rw [if_pos hs] at h1
      rw [if_neg (by omega)] at h2'
      exact ⟨w, fun _ => ⟨by rw [h1]; push_cast; ring, h2'⟩⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose w0 hw0 using hw
  have hUE : ∀ j, ∃ U E : LocRing p, j < 3 →
      ((p : ℚ) ^ 3 * ownU ca cb (s + j * p) = (U : ℚ) ∧ (p : ℚ) ^ 4 * ownE n ca cb cX (s + j * p) = (E : ℚ)) ∧
      redQ p U = redQ p cb * (if j = 1 then -2 else if j = 2 then -9 / 4 else 0) ∧
      redQ p E = redQ p cb * (if j = 1 then -6 else if j = 2 then -105 / 8 else 0) := by
    intro j
    by_cases hj : j < 3
    · have hk : s + j * p ≤ 6 * n := by nlinarith
      have hjd : (s + j * p) / p = j := (mod_div_node (ℓ := p) s j hsp).2
      have hz2 : (2 : ZMod p) ≠ 0 := h2
      interval_cases j
      · obtain ⟨U, E, e1, e2, e3, e4⟩ := own_UE (p := p) n (s + 0 * p) 0 hk h8 hjd ca cb cX 1 1 0 0
          (nz_nat h5 (Or.inl rfl)) (nz_nat h5 (Or.inl rfl)) (by simp [(uL_vals).1])
          (by simp [vL_zero])
        exact ⟨U, E, fun _ => ⟨⟨e1, e2⟩, by simpa using e3, by simpa using e4⟩⟩
      · obtain ⟨U, E, e1, e2, e3, e4⟩ := own_UE (p := p) n (s + 1 * p) 1 hk h8 hjd ca cb cX 1 1 (-2) (-6)
          (nz_nat h5 (Or.inl rfl)) (nz_nat h5 (Or.inl rfl)) (by simp [(uL_vals).2.1])
          (by rw [vL_A1 ha hA hA2 hs hk]; norm_num)
        exact ⟨U, E, fun _ => ⟨⟨e1, e2⟩, by simpa using e3, by simpa using e4⟩⟩
      · obtain ⟨U, E, e1, e2, e3, e4⟩ := own_UE (p := p) n (s + 2 * p) 2 hk h8 hjd ca cb cX 4 8 (-9) (-105)
          (nz_nat h5 (Or.inr (Or.inl rfl))) (nz_nat h5 (Or.inr (Or.inr rfl)))
          (by rw [(uL_vals).2.2]; norm_num)
          (by rw [vL_A2 ha hA hA2 hs hk]; norm_num)
        refine ⟨U, E, fun _ => ⟨⟨e1, e2⟩, ?_, ?_⟩⟩
        · rw [e3]; push_cast; simp
        · rw [e4]; push_cast; simp
    · exact ⟨0, 0, fun h => absurd h hj⟩
  choose U E hUE using hUE
  obtain ⟨Z, hZ1, hZ2⟩ := own_sum n s 3 0 m hsp R hR ρ hρ w0
    (fun j hj => (hw0 j hj).1) U E (ownU ca cb) (ownE n ca cb cX)
    (fun j hj => (hUE j hj).1.1) (fun j hj => (hUE j hj).1.2)
  refine ⟨Z, by simpa using hZ1, ?_⟩
  rw [hZ2]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [(hw0 0 (by norm_num)).2, (hw0 1 (by norm_num)).2, (hw0 2 (by norm_num)).2,
    (hUE 0 (by norm_num)).2.1, (hUE 0 (by norm_num)).2.2, (hUE 1 (by norm_num)).2.1,
    (hUE 1 (by norm_num)).2.2, (hUE 2 (by norm_num)).2.1, (hUE 2 (by norm_num)).2.2]
  simp only [Nat.reduceEqDiff, ↓reduceIte, mul_zero, Mb_zero_zero, Mb_scale, NV7.kappa_T1_1 h2,
    NV7.kappa_T1_2 h2, kappa_A0 h5]
  unfold cunit hh
  rw [kappa_A0 h5]
  ring

end Residues


section ResiduesC

variable {n A2 a : ℕ}

/-- **Own node of a `C` residue (Lemma C, `Φ_C`).**  `A₂ < s < a`, `F = (X + s)^m R`, nodes `s + jp`,
`j = 0, 1`.  `p⁴ · Σ = p^{2+m} Z`, `Z̄ = b̄ ĉ_s ρ̄ · Φ_C m`. -/
theorem own_C (h5 : 5 ≤ p) (ha : a + 2 * n = p) (hA : A2 + 2 * p = 6 * n) (hA2 : A2 < a) {s : ℕ}
    (hs1 : A2 < s) (hs2 : s < a) (m : ℕ) (R : ℚ[X]) (hR : IntPoly p R) (ρ : LocRing p)
    (hρ : (ρ : ℚ) = R.eval (-(s : ℚ))) (ca cb cX : LocRing p) :
    ∃ Z : LocRing p,
      (p : ℚ) ^ 4 * ∑ j ∈ range 2, (laiCoef n (s + j * p) : ℚ) *
          (ownU ca cb (s + j * p) * (derivative ((X + C (s : ℚ)) ^ m * R)).eval (-(Nat.cast (s + j * p) : ℚ)) +
            ownE n ca cb cX (s + j * p) * ((X + C (s : ℚ)) ^ m * R).eval (-(Nat.cast (s + j * p) : ℚ))) =
        (p : ℚ) ^ (2 + m) * (Z : ℚ) ∧
      redQ p Z = redQ p cb * cunit p n A2 1 s * redQ p ρ * PhiC p m := by
  have h8 := h8_band h5 ha hA hA2
  have hsp : s < p := by omega
  have hw : ∀ j, ∃ w : ℕ, j < 2 → (laiCoef n (s + j * p) : ℚ) = (p : ℚ) ^ 2 * (w : ℚ) ∧
      (w : ZMod p) = kappa p 2 0 1 0 j * chat p A2 (2 * n) 1 0 s := by
    intro j
    by_cases hj : j < 2
    · obtain ⟨w, h1, h2'⟩ := unit_own (j := j) h5 ha hA hA2 hs2 (by nlinarith)
      rw [if_neg (by omega)] at h1
      rw [if_pos hs1] at h2'
      exact ⟨w, fun _ => ⟨by rw [h1]; push_cast; ring, h2'⟩⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose w0 hw0 using hw
  have hUE : ∀ j, ∃ U E : LocRing p, j < 2 →
      ((p : ℚ) ^ 3 * ownU ca cb (s + j * p) = (U : ℚ) ∧ (p : ℚ) ^ 4 * ownE n ca cb cX (s + j * p) = (E : ℚ)) ∧
      redQ p U = redQ p cb * (if j = 1 then -2 else 0) ∧
      redQ p E = redQ p cb * (if j = 1 then -10 else 0) := by
    intro j
    by_cases hj : j < 2
    · have hk : s + j * p ≤ 6 * n := by nlinarith
      have hjd : (s + j * p) / p = j := (mod_div_node (ℓ := p) s j hsp).2
      interval_cases j
      · obtain ⟨U, E, e1, e2, e3, e4⟩ := own_UE (p := p) n (s + 0 * p) 0 hk h8 hjd ca cb cX 1 1 0 0
          (nz_nat h5 (Or.inl rfl)) (nz_nat h5 (Or.inl rfl)) (by simp [(uL_vals).1])
          (by simp [vL_zero])
        exact ⟨U, E, fun _ => ⟨⟨e1, e2⟩, by simpa using e3, by simpa using e4⟩⟩
      · obtain ⟨U, E, e1, e2, e3, e4⟩ := own_UE (p := p) n (s + 1 * p) 1 hk h8 hjd ca cb cX 1 1 (-2) (-10)
          (nz_nat h5 (Or.inl rfl)) (nz_nat h5 (Or.inl rfl)) (by simp [(uL_vals).2.1])
          (by rw [vL_C1 ha hA hA2 hs1 hs2 hk]; norm_num)
        exact ⟨U, E, fun _ => ⟨⟨e1, e2⟩, by simpa using e3, by simpa using e4⟩⟩
    · exact ⟨0, 0, fun h => absurd h hj⟩
  choose U E hUE using hUE
  obtain ⟨Z, hZ1, hZ2⟩ := own_sum n s 2 2 m hsp R hR ρ hρ w0
    (fun j hj => (hw0 j hj).1) U E (ownU ca cb) (ownE n ca cb cX)
    (fun j hj => (hUE j hj).1.1) (fun j hj => (hUE j hj).1.2)
  refine ⟨Z, hZ1, ?_⟩
  rw [hZ2]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [(hw0 0 (by norm_num)).2, (hw0 1 (by norm_num)).2,
    (hUE 0 (by norm_num)).2.1, (hUE 0 (by norm_num)).2.2, (hUE 1 (by norm_num)).2.1,
    (hUE 1 (by norm_num)).2.2]
  simp only [Nat.reduceEqDiff, ↓reduceIte, mul_zero, Mb_zero_zero, Mb_scale, kappa_C1, kappa_C0]
  unfold cunit PhiC
  rw [kappa_C0]
  ring

end ResiduesC

/-! ### Part 4: the pair `e_{r,i} e_{r,i'}` of the basis of the note -/

section Pair

variable {n A2 a : ℕ}

/-- `Ψ_r(X) = Π/(X + r)^{μ_r} = ∏_{t < a, t ≠ r} (X + t)^{μ_t}`. -/
noncomputable def PsiPoly (A2 a r : ℕ) : ℚ[X] := ∏ t ∈ (range a).erase r, (X + C (t : ℚ)) ^ muB A2 t

/-- the basis element `e_{r,i} = (X + r)^i Π/(X + r)^{μ_r}`. -/
noncomputable def eB (A2 a r i : ℕ) : ℚ[X] := (X + C (r : ℚ)) ^ i * PsiPoly A2 a r

theorem eB_mul (A2 a r i i' : ℕ) :
    eB A2 a r i * eB A2 a r i' = (X + C (r : ℚ)) ^ (i + i') * PsiPoly A2 a r ^ 2 := by
  unfold eB; ring

theorem intPoly_one : IntPoly p (1 : ℚ[X]) := by
  have := IntPoly.pow (p := p) (IntPoly.X_add_C (p := p) 0) 0
  simpa using this

theorem intPoly_PsiPoly (A2 a r : ℕ) : IntPoly p (PsiPoly A2 a r) := by
  unfold PsiPoly
  refine Finset.prod_induction _ (IntPoly p) (fun _ _ h1 h2 => h1.mul h2) intPoly_one (fun t _ => ?_)
  have h : IntPoly p (X + C (t : ℚ)) := by simpa using IntPoly.X_add_C (p := p) (t : ℤ)
  exact h.pow _

/-- the value `Ψ_r(-r)²` as an element of `ℤ_(p)`. -/
noncomputable def rhoB (p A2 a r : ℕ) [Fact p.Prime] : LocRing p :=
  (((∏ t ∈ (range a).erase r, (((t : ℕ) : ℤ) - r) ^ muB A2 t) ^ 2 : ℤ) : LocRing p)

theorem rhoB_eval (A2 a r : ℕ) :
    ((rhoB p A2 a r : LocRing p) : ℚ) = (PsiPoly A2 a r ^ 2).eval (-(r : ℚ)) := by
  unfold rhoB PsiPoly
  simp only [eval_pow, eval_prod, eval_add, eval_X, eval_C]
  push_cast
  congr 2
  funext t
  ring

theorem rhoB_red (A2 a r : ℕ) : redQ p (rhoB p A2 a r) = PsiB p A2 a r ^ 2 := by
  unfold rhoB PsiB
  rw [map_intCast]
  push_cast
  rfl

/-- **Own-node component of the `A`-block entry** (output of lb-own for LB04b).  For `r ≤ A₂`, the exact own
nodes `r + jp` (`j = 0, 1, 2`) of the pair `e_{r,i} e_{r,i'}`, scaled by `p⁴`, are `p^{i+i'} Z` with
`Z̄ = b̄ · wtB · hh (i + i')`, `wtB = ĉ_r Ψ_r(-r)²`.  The remaining components of the entry are the D-nodes
(`B83DNode`) and the other residues (`B83Cross`). -/
theorem own_entry_A (h5 : 5 ≤ p) (ha : a + 2 * n = p) (hA : A2 + 2 * p = 6 * n) (hA2 : A2 < a) {r : ℕ}
    (hr : r ≤ A2) (i i' : ℕ) (ca cb cX : LocRing p) :
    ∃ Z : LocRing p,
      (p : ℚ) ^ 4 * ∑ j ∈ range 3, (laiCoef n (r + j * p) : ℚ) *
          (ownU ca cb (r + j * p) * (derivative (eB A2 a r i * eB A2 a r i')).eval (-(Nat.cast (r + j * p) : ℚ)) +
            ownE n ca cb cX (r + j * p) * (eB A2 a r i * eB A2 a r i').eval (-(Nat.cast (r + j * p) : ℚ))) =
        (p : ℚ) ^ (i + i') * (Z : ℚ) ∧
      redQ p Z = redQ p cb * wtB p n A2 a 0 r * hh p (i + i') := by
  rw [eB_mul]
  obtain ⟨Z, h1, h2⟩ := own_A (n := n) (A2 := A2) (a := a) h5 ha hA hA2 hr (i + i') (PsiPoly A2 a r ^ 2)
    ((intPoly_PsiPoly A2 a r).pow 2) (rhoB p A2 a r) (rhoB_eval A2 a r) ca cb cX
  refine ⟨Z, h1, ?_⟩
  rw [h2, rhoB_red]
  unfold wtB
  ring

/-- **Own-node component of the `C`-block entry** (LB05b).  For `A₂ < r < a`: nodes `r + jp`, `j = 0, 1`;
`p⁴ · Σ = p^{2+i+i'} Z`, `Z̄ = b̄ · wtB · Φ_C (i + i')`. -/
theorem own_entry_C (h5 : 5 ≤ p) (ha : a + 2 * n = p) (hA : A2 + 2 * p = 6 * n) (hA2 : A2 < a) {r : ℕ}
    (hr1 : A2 < r) (hr2 : r < a) (i i' : ℕ) (ca cb cX : LocRing p) :
    ∃ Z : LocRing p,
      (p : ℚ) ^ 4 * ∑ j ∈ range 2, (laiCoef n (r + j * p) : ℚ) *
          (ownU ca cb (r + j * p) * (derivative (eB A2 a r i * eB A2 a r i')).eval (-(Nat.cast (r + j * p) : ℚ)) +
            ownE n ca cb cX (r + j * p) * (eB A2 a r i * eB A2 a r i').eval (-(Nat.cast (r + j * p) : ℚ))) =
        (p : ℚ) ^ (2 + (i + i')) * (Z : ℚ) ∧
      redQ p Z = redQ p cb * wtB p n A2 a 1 r * PhiC p (i + i') := by
  rw [eB_mul]
  obtain ⟨Z, h1, h2⟩ := own_C (n := n) (A2 := A2) (a := a) h5 ha hA hA2 hr1 hr2 (i + i') (PsiPoly A2 a r ^ 2)
    ((intPoly_PsiPoly A2 a r).pow 2) (rhoB p A2 a r) (rhoB_eval A2 a r) ca cb cX
  refine ⟨Z, h1, ?_⟩
  rw [h2, rhoB_red]
  unfold wtB
  ring

/-- the entries with `i + i' ≤ 4` of the `A`-block: own nodes alone give `hA`. -/
theorem own_entry_A_hA (h5 : 5 ≤ p) (ha : a + 2 * n = p) (hAp : A2 + 2 * p = 6 * n) (hA2 : A2 < a) {r : ℕ}
    (hr : r ≤ A2) (i i' : ℕ) (hm : i + i' ≤ 4) (ca cb cX : LocRing p) :
    ∃ Z : LocRing p,
      (p : ℚ) ^ 4 * ∑ j ∈ range 3, (laiCoef n (r + j * p) : ℚ) *
          (ownU ca cb (r + j * p) * (derivative (eB A2 a r i * eB A2 a r i')).eval (-(Nat.cast (r + j * p) : ℚ)) +
            ownE n ca cb cX (r + j * p) * (eB A2 a r i * eB A2 a r i').eval (-(Nat.cast (r + j * p) : ℚ))) =
        (p : ℚ) ^ (i + i') * (Z : ℚ) ∧
      redQ p Z = redQ p cb * wtB p n A2 a 0 r * hA p (i + i') := by
  obtain ⟨Z, h1, h2⟩ := own_entry_A h5 ha hAp hA2 hr i i' ca cb cX
  refine ⟨Z, h1, ?_⟩
  have : corrA (i + i') = 0 := by
    unfold corrA; rw [if_neg (by omega), if_neg (by omega)]
  rw [h2]
  unfold hA
  rw [this]; simp

/-- the entries with `i + i' ≤ 2` of the `C`-block: own nodes alone give `hC`. -/
theorem own_entry_C_hC (h5 : 5 ≤ p) (ha : a + 2 * n = p) (hA : A2 + 2 * p = 6 * n) (hA2 : A2 < a) {r : ℕ}
    (hr1 : A2 < r) (hr2 : r < a) (i i' : ℕ) (hm : i + i' ≤ 2) (ca cb cX : LocRing p) :
    ∃ Z : LocRing p,
      (p : ℚ) ^ 4 * ∑ j ∈ range 2, (laiCoef n (r + j * p) : ℚ) *
          (ownU ca cb (r + j * p) * (derivative (eB A2 a r i * eB A2 a r i')).eval (-(Nat.cast (r + j * p) : ℚ)) +
            ownE n ca cb cX (r + j * p) * (eB A2 a r i * eB A2 a r i').eval (-(Nat.cast (r + j * p) : ℚ))) =
        (p : ℚ) ^ (2 + (i + i')) * (Z : ℚ) ∧
      redQ p Z = redQ p cb * wtB p n A2 a 1 r * hC p (i + i') := by
  obtain ⟨Z, h1, h2⟩ := own_entry_C h5 ha hA hA2 hr1 hr2 i i' ca cb cX
  refine ⟨Z, h1, ?_⟩
  have : corrC (i + i') = 0 := by
    unfold corrC; rw [if_neg (by omega), if_neg (by omega)]
  rw [h2]
  unfold hC
  rw [this]; simp

end Pair

/-! ### Part 5: the numerical values -/

section Values

/-- `Φ_A = hh`: the own-node values; `h₅ = 224`, `h₆ = -384` are cancelled by the D-node corrections. -/
theorem hh_vals {ℓ : ℕ} [Fact ℓ.Prime] (h2 : (2 : ZMod ℓ) ≠ 0) :
    hh ℓ 0 = -297 / 8 ∧ hh ℓ 1 = 40 ∧ hh ℓ 2 = -103 / 2 ∧ hh ℓ 3 = 78 ∧ hh ℓ 4 = -130 ∧
      hh ℓ 5 = 224 ∧ hh ℓ 6 = -384 := by
  obtain ⟨h4, h8⟩ := ne48 h2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [hh, Mb] <;> simp <;> field_simp <;> ring

/-- `Φ_C`: the own-node values; `Φ_C(3) = 4`, `Φ_C(4) = -2` are completed by the D-node corrections. -/
theorem PhiC_vals {ℓ : ℕ} [Fact ℓ.Prime] :
    PhiC ℓ 0 = -10 ∧ PhiC ℓ 1 = 8 ∧ PhiC ℓ 2 = -6 ∧ PhiC ℓ 3 = 4 ∧ PhiC ℓ 4 = -2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [PhiC, Mb] <;> simp <;> ring

end Values

end CatalanCore.Lai.B83

#print axioms CatalanCore.Lai.B83.own_sum
#print axioms CatalanCore.Lai.B83.own_UE
#print axioms CatalanCore.Lai.B83.own_A
#print axioms CatalanCore.Lai.B83.own_C
#print axioms CatalanCore.Lai.B83.own_entry_A
#print axioms CatalanCore.Lai.B83.own_entry_C
#print axioms CatalanCore.Lai.B83.own_entry_A_hA
#print axioms CatalanCore.Lai.B83.own_entry_C_hC
#print axioms CatalanCore.Lai.B83.hh_vals
#print axioms CatalanCore.Lai.B83.PhiC_vals
#print axioms CatalanCore.Lai.B83.unit_own
#print axioms CatalanCore.Lai.B83.vL_A1
#print axioms CatalanCore.Lai.B83.vL_A2
#print axioms CatalanCore.Lai.B83.vL_C1
#print axioms CatalanCore.Lai.B83.kappa_C1
#print axioms CatalanCore.Lai.B83.rhoB_eval
#print axioms CatalanCore.Lai.B83.rhoB_red
