module

public import CatalanCore.Uniform.Content.UFMoments.TypeDataLift
public import CatalanCore.Uniform.Content.UFMoments.StepSum
public import CatalanCore.Uniform.Content.Smith.TwoTerm

@[expose] public section

/-!
# UF moments, frame layer for two-term frames: periodic reduction and the cyclic step

For a two-term frame (`Δ_t = 1/t - q/(qt - o)`, `0 < o < q < p`):

* `tt_red`: for regular `k`, `red Δ_k = δ̄(k̄)`, `δ̄(x) = x⁻¹ - q (q x - o)⁻¹` (so `RegRed`, `tt_regRed`);
* `prim`, `prim_succ`: cyclic primitives on `𝔽_p` of functions with zero total;
* `hT = prim (δ̄(· + 1))` (regular prefix) and `wT = prim jump` (cyclic step, jumps `-1` at `-1`,
  `+1` at `o/q - 1`); `tt_step`: `hT(z) - Σ_c wT(c)(c - z)⁻¹` is constant (`step_identity`);
* `tt_shift_red`: `red(F(t₀+Δ) - F(t₀)) = hT(t₀+Δ) - hT(t₀)` on a nonsingular window.
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Smith CatalanCore.Uniform.Content.Hybrid

namespace CatalanCore.Uniform.Content.UFMoments

variable {p : ℕ} [hp : Fact p.Prime]

/-- The reduced regular increment of a two-term frame. -/
noncomputable def ttDel (p q o : ℕ) [Fact p.Prime] (x : ZMod p) : ZMod p :=
  x⁻¹ - (q : ZMod p) * ((q : ZMod p) * x - (o : ZMod p))⁻¹

/-- The cyclic primitive `Σ_{j < z} f(j)`. -/
noncomputable def prim (f : ZMod p → ZMod p) (z : ZMod p) : ZMod p :=
  ∑ j ∈ range z.val, f (j : ZMod p)

theorem prim_succ (f : ZMod p → ZMod p) (hf : ∑ x : ZMod p, f x = 0) (z : ZMod p) :
    prim f (z + 1) = prim f z + f z := by
  have hp2 := hp.out.two_le
  unfold prim
  by_cases hz : z.val + 1 < p
  · have hv : (z + 1).val = z.val + 1 := by
      rw [ZMod.val_add, ZMod.val_one'' (by omega), Nat.mod_eq_of_lt hz]
    rw [hv, Finset.sum_range_succ, ZMod.natCast_zmod_val]
  · have hzv : z.val = p - 1 := by have := z.val_lt; omega
    have hz1 : z + 1 = 0 := by
      have : ((z.val + 1 : ℕ) : ZMod p) = 0 := by
        rw [show z.val + 1 = p by omega]; exact ZMod.natCast_self p
      rw [← this]; push_cast; rw [ZMod.natCast_zmod_val]
    rw [hz1, ZMod.val_zero, Finset.sum_range_zero]
    have hall : ∑ x : ZMod p, f x = ∑ j ∈ range p, f (j : ZMod p) :=
      Finset.sum_nbij' (fun x => x.val) (fun n => (n : ZMod p))
        (fun a _ => Finset.mem_range.2 a.val_lt) (fun _ _ => Finset.mem_univ _)
        (fun a _ => ZMod.natCast_zmod_val a)
        (fun n hn => ZMod.val_natCast_of_lt (Finset.mem_range.1 hn))
        (fun a _ => by rw [ZMod.natCast_zmod_val])
    rw [hzv]
    have hsplit : ∑ j ∈ range p, f (j : ZMod p) = ∑ j ∈ range (p - 1), f (j : ZMod p) + f z := by
      rw [show range p = range ((p - 1) + 1) by congr 1; omega, Finset.sum_range_succ]
      congr 2
      rw [← hzv, ZMod.natCast_zmod_val]
    rw [← hall, hf] at hsplit
    linear_combination hsplit

theorem sum_inv_affine (hp2 : p ≠ 2) (a b : ZMod p) (ha : a ≠ 0) :
    ∑ x : ZMod p, (a * x + b)⁻¹ = 0 := by
  have hbij : Function.Bijective (fun x : ZMod p => a * x + b) := by
    refine (Finite.injective_iff_bijective).1 ?_
    intro x y h
    have : a * x = a * y := by simpa using h
    exact mul_left_cancel₀ ha this
  rw [Fintype.sum_bijective _ hbij (fun x => (a * x + b)⁻¹) (fun y => y⁻¹) (fun _ => rfl)]
  exact sum_inv_univ hp2

theorem ttDel_eq (q o : ℕ) (hq : (q : ZMod p) ≠ 0) (x : ZMod p) :
    ttDel p q o x = (x - 0)⁻¹ - (x - (o : ZMod p) * (q : ZMod p)⁻¹)⁻¹ := by
  unfold ttDel
  rw [sub_zero]
  congr 1
  have e : (q : ZMod p) * x - o = (q : ZMod p) * (x - o * (q : ZMod p)⁻¹) := by
    field_simp
  rw [e, mul_inv, ← mul_assoc, mul_inv_cancel₀ hq, one_mul]

theorem sum_ttDel (hp2 : p ≠ 2) (q o : ℕ) (hq : (q : ZMod p) ≠ 0) :
    ∑ x : ZMod p, ttDel p q o (x + 1) = 0 := by
  unfold ttDel
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have h1 : ∑ x : ZMod p, (x + 1)⁻¹ = 0 := by
    have := sum_inv_affine hp2 1 1 one_ne_zero
    simpa using this
  have h2 : ∑ x : ZMod p, ((q : ZMod p) * (x + 1) - o)⁻¹ = 0 := by
    have := sum_inv_affine hp2 (q : ZMod p) ((q : ZMod p) - o) hq
    rw [← this]
    exact Finset.sum_congr rfl fun x _ => by ring_nf
  rw [h1, h2, mul_zero, sub_zero]

/-- The regular prefix of a two-term frame on `𝔽_p`. -/
noncomputable def hT (p q o : ℕ) [Fact p.Prime] : ZMod p → ZMod p :=
  prim fun x => ttDel p q o (x + 1)

/-- The two pole residues `-1` and `o/q - 1`. -/
noncomputable def ttPoles (p q o : ℕ) [Fact p.Prime] : Finset (ZMod p) :=
  {-1, (o : ZMod p) * (q : ZMod p)⁻¹ - 1}

/-- Their weights. -/
noncomputable def ttKap (p : ℕ) [Fact p.Prime] (z : ZMod p) : ZMod p := if z = -1 then 1 else -1

/-- The jumps of the cyclic step. -/
noncomputable def ttJump (p q o : ℕ) [Fact p.Prime] (z : ZMod p) : ZMod p :=
  -(if z ∈ ttPoles p q o then ttKap p z else 0)

/-- The cyclic step of a two-term frame. -/
noncomputable def wT (p q o : ℕ) [Fact p.Prime] : ZMod p → ZMod p := prim (ttJump p q o)

theorem poles_ne (q o : ℕ) (ho : (o : ZMod p) ≠ 0) (hq : (q : ZMod p) ≠ 0) :
    (-1 : ZMod p) ≠ (o : ZMod p) * (q : ZMod p)⁻¹ - 1 := by
  intro h
  have : (o : ZMod p) * (q : ZMod p)⁻¹ = 0 := by linear_combination -h
  rcases mul_eq_zero.1 this with h1 | h1
  · exact ho h1
  · exact inv_ne_zero hq h1

theorem sum_ttJump (q o : ℕ) (ho : (o : ZMod p) ≠ 0) (hq : (q : ZMod p) ≠ 0) :
    ∑ x : ZMod p, ttJump p q o x = 0 := by
  unfold ttJump
  rw [Finset.sum_neg_distrib, Finset.sum_ite_mem, Finset.univ_inter, ttPoles,
    Finset.sum_pair (poles_ne q o ho hq)]
  unfold ttKap
  rw [if_pos rfl, if_neg (Ne.symm (poles_ne q o ho hq))]
  ring

/-- **The step identity for two-term frames.** -/
theorem tt_step (hp2 : p ≠ 2) (q o : ℕ) (ho : (o : ZMod p) ≠ 0) (hq : (q : ZMod p) ≠ 0)
    (z : ZMod p) :
    hT p q o z - cauchyH (wT p q o) z = hT p q o 0 - cauchyH (wT p q o) 0 := by
  refine step_identity (wT p q o) (hT p q o) (ttKap p) (ttPoles p q o) ?_ ?_ z
  · intro z
    unfold wT
    rw [prim_succ _ (sum_ttJump q o ho hq)]
    unfold ttJump
    ring
  · intro z
    unfold hT
    rw [prim_succ _ (sum_ttDel hp2 q o hq), ttDel_eq q o hq, ttPoles,
      Finset.sum_pair (poles_ne q o ho hq)]
    unfold ttKap
    rw [if_pos rfl, if_neg (Ne.symm (poles_ne q o ho hq))]
    have e1 : z + 1 - 0 = z - -1 := by ring
    have e2 : z + 1 - (o : ZMod p) * (q : ZMod p)⁻¹ = z - ((o : ZMod p) * (q : ZMod p)⁻¹ - 1) := by
      ring
    rw [e1, e2]
    ring

section Frame

variable {Fr : Frame} {q o N : ℕ}

theorem tt_good (T : TwoTermData Fr q o) {k : ℕ} (hk1 : 1 ≤ k) (hk : ¬ p ∣ k)
    (hk' : ¬ p ∣ q * k - o) : Good p (Fr.Delta k) (ttDel p q o (k : ZMod p)) := by
  have hle : o ≤ q * k := by have := T.o_lt; nlinarith
  have g1 := (Good.natCast (ℓ := p) k).inv (natCast_ne_zero_of_not_dvd hk)
  have g2 := (Good.natCast (ℓ := p) (q * k - o)).inv (natCast_ne_zero_of_not_dvd hk')
  have g := g1.sub ((Good.natCast (ℓ := p) q).mul g2)
  refine (g.congr ?_).congr' ?_
  · unfold ttDel
    rw [Nat.cast_sub hle]; push_cast; ring
  · rw [T.delta_eq k hk1, T.cast_sub hk1]; ring

/-- The `PoleData` of a two-term frame reduces periodically. -/
theorem tt_regRed (T : TwoTermData Fr q o) (hN : N ≤ p * p)
    (hsq : ∀ t, 1 ≤ t → t < N → ¬ p ^ 2 ∣ q * t - o) (hnorm : Fr.norm ∈ S p)
    (hnorm0 : red p Fr.norm ≠ 0) : RegRed (twoTermPoleData T hN hsq hnorm hnorm0) := by
  intro k k' hk1 _ hk1' _ hs hs' hkk
  have h1 : ¬ (p ∣ k ∨ p ∣ q * k - o) := fun h => hs ((ttSing_nat T hk1).2 h)
  have h2 : ¬ (p ∣ k' ∨ p ∣ q * k' - o) := fun h => hs' ((ttSing_nat T hk1').2 h)
  push Not at h1 h2
  rw [(tt_good T hk1 h1.1 h1.2).eq, (tt_good T hk1' h2.1 h2.2).eq, hkk]

/-- **The regular prefix over a nonsingular window.** -/
theorem tt_shift_red (T : TwoTermData Fr q o) (hN : N ≤ p * p)
    (hsq : ∀ t, 1 ≤ t → t < N → ¬ p ^ 2 ∣ q * t - o) (hnorm : Fr.norm ∈ S p)
    (hnorm0 : red p Fr.norm ≠ 0) (hp2 : p ≠ 2) (hq : (q : ZMod p) ≠ 0) (t0 Δ : ℕ)
    (hb : t0 + Δ < N) (hw : NoSingWin (twoTermPoleData T hN hsq hnorm hnorm0) t0 Δ) :
    red p (Fp Fr (t0 + Δ) - Fp Fr t0) =
      hT p q o ((t0 + Δ : ℕ) : ZMod p) - hT p q o ((t0 : ℕ) : ZMod p) := by
  suffices h : ∀ n, n ≤ Δ → Good p (Fp Fr (t0 + n) - Fp Fr t0)
      (hT p q o ((t0 + n : ℕ) : ZMod p) - hT p q o ((t0 : ℕ) : ZMod p)) from (h Δ le_rfl).eq
  intro n
  induction n with
  | zero => intro _; simpa using (Good.zero (ℓ := p))
  | succ m ih =>
    intro hm
    have ih' := ih (by omega)
    have hs := hw (t0 + m + 1) (by omega) (by omega)
    have h1 : ¬ (p ∣ (t0 + m + 1) ∨ p ∣ q * (t0 + m + 1) - o) :=
      fun h => hs ((ttSing_nat T (by omega)).2 h)
    push Not at h1
    have g := ih'.add (tt_good T (by omega) h1.1 h1.2)
    refine (g.congr ?_).congr' ?_
    · rw [show t0 + (m + 1) = (t0 + m) + 1 by ring]
      have e : (((t0 + m + 1 : ℕ)) : ZMod p) = ((t0 + m : ℕ) : ZMod p) + 1 := by push_cast; ring
      rw [e, hT, prim_succ _ (sum_ttDel hp2 q o hq)]
      ring
    · rw [show t0 + (m + 1) = (t0 + m) + 1 by ring, Fp_succ]; ring

/-- **The residue of the prefix shift in Cauchy form** (the hypothesis `hres` of
`typeData_of_shift`). -/
theorem tt_hres (T : TwoTermData Fr q o) (hN : N ≤ p * p)
    (hsq : ∀ t, 1 ≤ t → t < N → ¬ p ^ 2 ∣ q * t - o) (hnorm : Fr.norm ∈ S p)
    (hnorm0 : red p Fr.norm ≠ 0) (hp2 : p ≠ 2) (ho : (o : ZMod p) ≠ 0)
    (hq : (q : ZMod p) ≠ 0) (t0 Δ : ℕ)
    (hb : t0 + Δ < N) (hw : NoSingWin (twoTermPoleData T hN hsq hnorm hnorm0) t0 Δ) :
    rfH p (red p (Fp Fr (t0 + Δ) - Fp Fr t0)) * (rfH p (red p Fr.norm))⁻¹ =
      (-(rfH p (cauchyH (wT p q o) ((t0 : ℕ) : ZMod p))) * (rfH p (red p Fr.norm))⁻¹) +
        ∑ c' : ZMod p, (rfH p (wT p q o c') * (rfH p (red p Fr.norm))⁻¹) *
          rfH p (c' - ((t0 + Δ : ℕ) : ZMod p))⁻¹ := by
  rw [tt_shift_red T hN hsq hnorm hnorm0 hp2 hq t0 Δ hb hw]
  have h1 := tt_step hp2 q o ho hq ((t0 + Δ : ℕ) : ZMod p)
  have h2 := tt_step hp2 q o ho hq ((t0 : ℕ) : ZMod p)
  have e : hT p q o ((t0 + Δ : ℕ) : ZMod p) - hT p q o ((t0 : ℕ) : ZMod p) =
      cauchyH (wT p q o) ((t0 + Δ : ℕ) : ZMod p) - cauchyH (wT p q o) ((t0 : ℕ) : ZMod p) := by
    linear_combination h1 - h2
  rw [e, map_sub]
  have hc : rfH p (cauchyH (wT p q o) ((t0 + Δ : ℕ) : ZMod p)) =
      ∑ c' : ZMod p, rfH p (wT p q o c') * rfH p (c' - ((t0 + Δ : ℕ) : ZMod p))⁻¹ := by
    unfold cauchyH
    rw [map_sum]
    exact Finset.sum_congr rfl fun c' _ => by rw [map_mul]
  rw [hc, sub_mul, Finset.sum_mul]
  have e2 : ∀ c' : ZMod p, rfH p (wT p q o c') * rfH p (c' - ((t0 + Δ : ℕ) : ZMod p))⁻¹ *
      (rfH p (red p Fr.norm))⁻¹ = rfH p (wT p q o c') * (rfH p (red p Fr.norm))⁻¹ *
        rfH p (c' - ((t0 + Δ : ℕ) : ZMod p))⁻¹ := fun c' => by ring
  simp_rw [e2]
  ring

end Frame

end CatalanCore.Uniform.Content.UFMoments
