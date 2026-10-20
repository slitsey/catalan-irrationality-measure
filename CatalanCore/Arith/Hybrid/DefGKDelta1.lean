module

public import CatalanCore.Arith.Hybrid.DefGKFin1
public import CatalanCore.Arith.Hybrid.DefGKDelta3

@[expose] public section

/-!
# GK, class 1: the second difference `D - αB - Cβ + αAβ` is integral (`hΔ` of `tcore_vec`)

The `p`-level residues of the nine terms add up to `0` by the translation `c ↦ c + (w - u)`
(`Lz1` is invariant) and the antisymmetry `Σ ā_i ā_j (L_j - L_i) = 0`.
-/

open Finset Polynomial CatalanCore CatalanCore.Basic Matrix
open CatalanCore.Arith.Hybrid.LemmaE

namespace CatalanCore.Arith.Hybrid.GK1

open CatalanCore.Arith.Hybrid

section Delta3

variable {o p : ℕ} [Fact p.Prime] {k : ℕ} {Fr : Frame} {r m : ℕ}

/-- The `p`-level residue of one term, in terms of `δ = w - u`. -/
theorem t_val (hL : LamData Fr o) (S : GKS1 o p r m k) {A B : ℕ} (hA : A < r + 2 * m)
    (hB : B < r + 2 * m) (δ : ZMod p) (hδ : (B : ZMod p) - A = δ) (hδ0 : δ ≠ 0) (La Lb : ℤ)
    (hLa : Lz1 p k A = La) (hLb : Lz1 p k B = Lb) :
    Good p ((p : ℚ) * Fr.Mn A B) ((16 * δ)⁻¹ * (((Lb : ℤ) : ZMod p) - (La : ZMod p)) * 84⁻¹) := by
  have h13 := S.p13
  have hp5 : 5 ≤ p := by omega
  have D := sgData1 hL S
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
    have n84' := n84 (p := p) h13
    field_simp
    ring

/-- The rational `X0`. -/
noncomputable abbrev X0 (Fr : Frame) (p u w : ℕ) : ℚ :=
  GKGen.X0G a1q a2q Fr p u w

lemma zone_delta_ne (S : GKS1 o p r m k) {u w : ℕ} (hu1 : r ≤ u) (hu2 : u < r + 2 * m)
    (hw1 : r ≤ w) (hw2 : w < r + 2 * m) (hne : u ≠ w) : ((w : ZMod p) - u) ≠ 0 := by
  have h13 := S.p13; have hr := S.hr; have hN := S.hN; have hkk := S.hk
  rcases lt_or_gt_of_ne hne with h | h
  · exact sub_ne3 h (by omega) (by omega) (by omega)
  · intro h0
    have := sub_ne3 (p := p) h (by omega) (by omega) (by omega)
    apply this; linear_combination -h0

theorem delta_good (hL : LamData Fr o) (S : GKS1 o p r m k) {u w : ℕ} (hu1 : r ≤ u)
    (hu2 : u < r + 2 * m) (hw1 : r ≤ w) (hw2 : w < r + 2 * m) (hne : u ≠ w) :
    Good p ((p : ℚ) * X0 Fr p u w) 0 := by
  have h13 := S.p13; have hk := S.hk; have hkp := S.kp; have hr := S.hr; have hN := S.hN; have hkk := S.hk
  have hp139 := S.h1009
  have hδ0 := zone_delta_ne S hu1 hu2 hw1 hw2 hne
  set δ : ZMod p := (w : ZMod p) - u with hδ
  have cu1 := cast_sub_2p (p := p) (X := u) (by omega)
  have cu2 := cast_sub_p_gk (p := p) (X := u) (by omega)
  have cw1 := cast_sub_2p (p := p) (X := w) (by omega)
  have cw2 := cast_sub_p_gk (p := p) (X := w) (by omega)
  have Lu := Lz_B4 (p := p) (k := k) (n := u) h13 hk (by omega)
  have Lw := Lz_B4 (p := p) (k := k) (n := w) h13 hk (by omega)
  have L1 := Lz_B0 (p := p) (k := k) (n := u - 2 * p) h13 hk (by omega)
  have L2 := Lz_B2 (p := p) (k := k) (n := u - p) h13 hk (by omega) (by omega)
  have L1' := Lz_B0 (p := p) (k := k) (n := w - 2 * p) h13 hk (by omega)
  have L2' := Lz_B2 (p := p) (k := k) (n := w - p) h13 hk (by omega) (by omega)
  have g1 := t_val hL S (A := u) (B := w) (by omega) (by omega) δ rfl hδ0 (-34) (-34) Lu Lw
  have g2 := t_val hL S (A := u - 2 * p) (B := w) (by omega) (by omega) δ
    (by rw [cu1]) hδ0 0 (-34) L1 Lw
  have g3 := t_val hL S (A := u - p) (B := w) (by omega) (by omega) δ
    (by rw [cu2]) hδ0 (-28) (-34) L2 Lw
  have g4 := t_val hL S (A := u) (B := w - 2 * p) (by omega) (by omega) δ
    (by rw [cw1]) hδ0 (-34) 0 Lu L1'
  have g5 := t_val hL S (A := u) (B := w - p) (by omega) (by omega) δ
    (by rw [cw2]) hδ0 (-34) (-28) Lu L2'
  have g6 := t_val hL S (A := u - 2 * p) (B := w - 2 * p) (by omega) (by omega) δ
    (by rw [cw1, cu1]) hδ0 0 0 L1 L1'
  have g7 := t_val hL S (A := u - p) (B := w - 2 * p) (by omega) (by omega) δ
    (by rw [cw1, cu2]) hδ0 (-28) 0 L2 L1'
  have g8 := t_val hL S (A := u - 2 * p) (B := w - p) (by omega) (by omega) δ
    (by rw [cw2, cu1]) hδ0 0 (-28) L1 L2'
  have g9 := t_val hL S (A := u - p) (B := w - p) (by omega) (by omega) δ
    (by rw [cw2, cu2]) hδ0 (-28) (-28) L2 L2'
  have ga1 := good_a1 h13 hp139
  have ga2 := good_a2 h13 hp139
  have G := ((g1.sub ((ga1.mul g2).add (ga2.mul g3))).sub ((ga1.mul g4).add (ga2.mul g5))).add
    ((ga1.mul ((ga1.mul g6).add (ga2.mul g7))).add (ga2.mul ((ga1.mul g8).add (ga2.mul g9))))
  refine (G.congr' (by unfold X0 GKGen.X0G; ring)).congr ?_
  push_cast
  ring

theorem hDelta_bound (hL : LamData Fr o) (S : GKS1 o p r m k) (i j : Fin m) :
    Int1 p (((Matrix.of (fullEntry Fr r m)).toBlocks₂₂ - alphaM Fr p r m *
        (Matrix.of (fullEntry Fr r m)).toBlocks₁₂ -
      (Matrix.of (fullEntry Fr r m)).toBlocks₂₁ * betaM Fr p r m +
      alphaM Fr p r m * (Matrix.of (fullEntry Fr r m)).toBlocks₁₁ * betaM Fr p r m) i j) :=
  GKGen.hDelta_boundG a1q a2q
    (by have := S.hr; have := S.hk; have := S.p13; omega)
    (by have := S.hr; have := S.hN; have := S.hk; have := S.p13; omega)
    (fun u w h1 h2 h3 h4 hne => int1_of_good0 (delta_good hL S h1 h2 h3 h4 hne)) i j

end Delta3

end CatalanCore.Arith.Hybrid.GK1
