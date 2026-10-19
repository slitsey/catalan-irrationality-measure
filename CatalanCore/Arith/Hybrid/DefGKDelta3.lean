module

public import CatalanCore.Arith.Hybrid.DefGKFin3

@[expose] public section

/-!
# GK, class 3: the second difference `D - αB - Cβ + αAβ` is integral (`hΔ` of `tcore_vec`)

The `p`-level residues of the nine terms add up to `0` by the translation `c ↦ c + (w - u)`
(`Lz3` is invariant) and the antisymmetry `Σ ā_i ā_j (L_j - L_i) = 0`.
-/

open Finset Polynomial CatalanCore CatalanCore.Basic Matrix
open CatalanCore.Arith.Hybrid.LemmaE

namespace CatalanCore.Arith.Hybrid

section Delta3

variable {p : ℕ} [Fact p.Prime] {k : ℕ} {Fr : Frame} {r m : ℕ}

lemma cast_sub_p_gk {X : ℕ} (h : p ≤ X) : ((X - p : ℕ) : ZMod p) = (X : ZMod p) := by
  rw [Nat.cast_sub h, ZMod.natCast_self, sub_zero]

lemma cast_sub_2p {X : ℕ} (h : 2 * p ≤ X) : ((X - 2 * p : ℕ) : ZMod p) = (X : ZMod p) := by
  rw [Nat.cast_sub h, Nat.cast_mul, ZMod.natCast_self, mul_zero, sub_zero]

lemma avec_disj (u w : ℕ) (hne : u ≠ w) (h1 : u < w + p) (h2 : w < u + p) (c : Fin r) :
    avec p r u c * avec p r w c = 0 := by
  unfold avec
  split_ifs <;> first | (exfalso; omega) | simp

lemma sum_avec_disj (u w : ℕ) (hne : u ≠ w) (h1 : u < w + p) (h2 : w < u + p) :
    ∑ c : Fin r, avec p r u c * avec p r w c = 0 :=
  Finset.sum_eq_zero fun c _ => avec_disj u w hne h1 h2 c

/-- The `p`-level residue of one term, in terms of `δ = w - u`. -/
theorem t_val (hL : LamData Fr 1) (S : GKS3 p r m k) {A B : ℕ} (hA : A < r + 2 * m)
    (hB : B < r + 2 * m) (δ : ZMod p) (hδ : (B : ZMod p) - A = δ) (hδ0 : δ ≠ 0) (La Lb : ℤ)
    (hLa : Lz3 p k A = La) (hLb : Lz3 p k B = Lb) :
    Good p ((p : ℚ) * Fr.Mn A B) ((16 * δ)⁻¹ * (((Lb : ℤ) : ZMod p) - (La : ZMod p)) * 90⁻¹) := by
  have h13 := S.p13
  have hp5 : 5 ≤ p := by omega
  have D := sgData3 hL S
  have hd : (B : ZMod p) - A ≠ 0 := hδ ▸ hδ0
  rcases lt_trichotomy A B with h | h | h
  · have := tab_P1 hL hp5 D h hB hd
    refine this.congr ?_
    rw [Lv_eq_Lz S, Lv_eq_Lz S, hLa, hLb, hδ]
    ring
  · subst h; exact absurd (sub_self _) hd
  · have hd' : (A : ZMod p) - B ≠ 0 := by
      intro h0; apply hd; linear_combination -h0
    have := tab_P1 hL hp5 D h hA hd'
    rw [Mn_symm]
    refine this.congr ?_
    have e : (A : ZMod p) - B = -δ := by rw [← hδ]; ring
    rw [Lv_eq_Lz S, Lv_eq_Lz S, hLa, hLb, e]
    have n16' := n16 (p := p) h13
    have n90' := n90 (p := p) h13
    field_simp
    ring

/-- The rational `X0`. -/
noncomputable def X0 (Fr : Frame) (p u w : ℕ) : ℚ :=
  Fr.Mn u w - (a1q * Fr.Mn (u - 2 * p) w + a2q * Fr.Mn (u - p) w)
    - (a1q * Fr.Mn u (w - 2 * p) + a2q * Fr.Mn u (w - p))
    + (a1q * (a1q * Fr.Mn (u - 2 * p) (w - 2 * p) + a2q * Fr.Mn (u - p) (w - 2 * p))
      + a2q * (a1q * Fr.Mn (u - 2 * p) (w - p) + a2q * Fr.Mn (u - p) (w - p)))

lemma zone_delta_ne (S : GKS3 p r m k) {u w : ℕ} (hu1 : r ≤ u) (hu2 : u < r + 2 * m)
    (hw1 : r ≤ w) (hw2 : w < r + 2 * m) (hne : u ≠ w) : ((w : ZMod p) - u) ≠ 0 := by
  have h13 := S.p13; have hr := S.hr; have hN := S.hN
  rcases lt_or_gt_of_ne hne with h | h
  · exact sub_ne3 h (by omega) (by omega) (by omega)
  · intro h0
    have := sub_ne3 (p := p) h (by omega) (by omega) (by omega)
    apply this; linear_combination -h0

theorem delta_good (hL : LamData Fr 1) (S : GKS3 p r m k) {u w : ℕ} (hu1 : r ≤ u)
    (hu2 : u < r + 2 * m) (hw1 : r ≤ w) (hw2 : w < r + 2 * m) (hne : u ≠ w) :
    Good p ((p : ℚ) * X0 Fr p u w) 0 := by
  have h13 := S.p13; have hk := S.hk; have hkp := S.kp; have hr := S.hr; have hN := S.hN
  have hp139 := S.h139
  have hδ0 := zone_delta_ne S hu1 hu2 hw1 hw2 hne
  set δ : ZMod p := (w : ZMod p) - u with hδ
  have cu1 := cast_sub_2p (p := p) (X := u) (by omega)
  have cu2 := cast_sub_p_gk (p := p) (X := u) (by omega)
  have cw1 := cast_sub_2p (p := p) (X := w) (by omega)
  have cw2 := cast_sub_p_gk (p := p) (X := w) (by omega)
  have Lu := Lz_B5 (p := p) (k := k) (n := u) h13 hk (by omega)
  have Lw := Lz_B5 (p := p) (k := k) (n := w) h13 hk (by omega)
  have L1 := Lz_B1 (p := p) (k := k) (n := u - 2 * p) h13 hk (by omega) (by omega)
  have L2 := Lz_B3 (p := p) (k := k) (n := u - p) h13 hk (by omega) (by omega)
  have L1' := Lz_B1 (p := p) (k := k) (n := w - 2 * p) h13 hk (by omega) (by omega)
  have L2' := Lz_B3 (p := p) (k := k) (n := w - p) h13 hk (by omega) (by omega)
  have g1 := t_val hL S (A := u) (B := w) (by omega) (by omega) δ rfl hδ0 (-337) (-337) Lu Lw
  have g2 := t_val hL S (A := u - 2 * p) (B := w) (by omega) (by omega) δ
    (by rw [cu1]) hδ0 (-360) (-337) L1 Lw
  have g3 := t_val hL S (A := u - p) (B := w) (by omega) (by omega) δ
    (by rw [cu2]) hδ0 (-342) (-337) L2 Lw
  have g4 := t_val hL S (A := u) (B := w - 2 * p) (by omega) (by omega) δ
    (by rw [cw1]) hδ0 (-337) (-360) Lu L1'
  have g5 := t_val hL S (A := u) (B := w - p) (by omega) (by omega) δ
    (by rw [cw2]) hδ0 (-337) (-342) Lu L2'
  have g6 := t_val hL S (A := u - 2 * p) (B := w - 2 * p) (by omega) (by omega) δ
    (by rw [cw1, cu1]) hδ0 (-360) (-360) L1 L1'
  have g7 := t_val hL S (A := u - p) (B := w - 2 * p) (by omega) (by omega) δ
    (by rw [cw1, cu2]) hδ0 (-342) (-360) L2 L1'
  have g8 := t_val hL S (A := u - 2 * p) (B := w - p) (by omega) (by omega) δ
    (by rw [cw2, cu1]) hδ0 (-360) (-342) L1 L2'
  have g9 := t_val hL S (A := u - p) (B := w - p) (by omega) (by omega) δ
    (by rw [cw2, cu2]) hδ0 (-342) (-342) L2 L2'
  have ga1 := good_a1 h13 hp139
  have ga2 := good_a2 h13 hp139
  have G := ((g1.sub ((ga1.mul g2).add (ga2.mul g3))).sub ((ga1.mul g4).add (ga2.mul g5))).add
    ((ga1.mul ((ga1.mul g6).add (ga2.mul g7))).add (ga2.mul ((ga1.mul g8).add (ga2.mul g9))))
  refine (G.congr' (by unfold X0; ring)).congr ?_
  push_cast
  ring

theorem hDelta_bound (hL : LamData Fr 1) (S : GKS3 p r m k) (i j : Fin m) :
    Int1 p (((Matrix.of (fullEntry Fr r m)).toBlocks₂₂ - alphaM Fr p r m *
        (Matrix.of (fullEntry Fr r m)).toBlocks₁₂ -
      (Matrix.of (fullEntry Fr r m)).toBlocks₂₁ * betaM Fr p r m +
      alphaM Fr p r m * (Matrix.of (fullEntry Fr r m)).toBlocks₁₁ * betaM Fr p r m) i j) := by
  have h13 := S.p13; have hk := S.hk; have hkp := S.kp; have hr := S.hr; have hN := S.hN
  have hi := i.2; have hj := j.2
  have hp0 : 0 < p := by omega
  set u := r + 2 * (i : ℕ) with hu
  set w := r + 2 * (j : ℕ) + 1 with hw
  have hne : u ≠ w := by omega
  rw [entDelta, sum_avec_disj u w hne (by omega) (by omega)]
  simp only [map_zero, zero_mul, add_zero]
  have s1 : ∑ c : Fin r, avec p r u c * Fr.Mn (c : ℕ) w =
      a1q * Fr.Mn (u - 2 * p) w + a2q * Fr.Mn (u - p) w :=
    sum_avec u (by omega) (by omega) hp0 (fun n => Fr.Mn n w)
  have s2 : ∑ c : Fin r, Fr.Mn u (c : ℕ) * avec p r w c =
      a1q * Fr.Mn u (w - 2 * p) + a2q * Fr.Mn u (w - p) := by
    calc ∑ c : Fin r, Fr.Mn u (c : ℕ) * avec p r w c
        = ∑ c : Fin r, avec p r w c * Fr.Mn u (c : ℕ) :=
          Finset.sum_congr rfl (fun c _ => mul_comm _ _)
      _ = _ := sum_avec w (by omega) (by omega) hp0 (fun n => Fr.Mn u n)
  have s3 : ∑ c' : Fin r, (∑ c : Fin r, avec p r u c * Fr.Mn (c : ℕ) (c' : ℕ)) * avec p r w c' =
      a1q * (a1q * Fr.Mn (u - 2 * p) (w - 2 * p) + a2q * Fr.Mn (u - p) (w - 2 * p)) +
        a2q * (a1q * Fr.Mn (u - 2 * p) (w - p) + a2q * Fr.Mn (u - p) (w - p)) := by
    calc ∑ c' : Fin r, (∑ c : Fin r, avec p r u c * Fr.Mn (c : ℕ) (c' : ℕ)) * avec p r w c'
        = ∑ c' : Fin r, avec p r w c' *
            (a1q * Fr.Mn (u - 2 * p) (c' : ℕ) + a2q * Fr.Mn (u - p) (c' : ℕ)) := by
          refine Finset.sum_congr rfl (fun c' _ => ?_)
          rw [mul_comm]; congr 1
          exact sum_avec u (by omega) (by omega) hp0 (fun n => Fr.Mn n (c' : ℕ))
      _ = _ := sum_avec w (by omega) (by omega) hp0
          (fun n => a1q * Fr.Mn (u - 2 * p) n + a2q * Fr.Mn (u - p) n)
  rw [s1, s2, s3]
  have := int1_of_good0 (delta_good hL S (u := u) (w := w) (by omega) (by omega) (by omega)
    (by omega) hne)
  convert this using 2
  unfold X0
  ring

end Delta3

end CatalanCore.Arith.Hybrid
