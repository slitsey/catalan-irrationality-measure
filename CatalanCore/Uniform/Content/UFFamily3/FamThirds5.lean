module

public import CatalanCore.Uniform.Content.UFFamily3.DataThirds

@[expose] public section

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.UFMoments
  CatalanCore.Uniform.Content.UFWedge CatalanCore.Uniform.Content.Smith
  CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.UFWire
  CatalanCore.Uniform.Content.Member CatalanCore.Uniform.Content.Wire
  CatalanCore.Uniform.Content.UFFamily CatalanCore.Uniform.Content.UFFamily.SevE
  CatalanCore.Uniform.Content.UFFamily2

namespace CatalanCore.Uniform.Content.UFFamily3
namespace F20

structure Reg (r p : ℕ) : Prop where
  hr : r % 2 = 0
  hp3 : p % 3 = 1
  hlo : 3 * r < 10 * p
  hhi : 10 * p ≤ 39 * r
  hp60 : 60 ≤ p
  hM1 : 2 * p < r
  hM2 : r ≤ 3 * p
  hP1 : 7 * p + 2 < 3 * r
  hP2 : 3 * r ≤ 10 * p + 2
  hb1 : 8 * p + 2 ≤ 3 * r
  hb2 : 3 * r < 9 * p + 2
  hm0 : r < (3*p)
  hf1 : (3*p+1) < (r + 2 * ((3 * r + 9) / 20))
  hf2 : ((10*p+2)/3) < (r + 2 * ((3 * r + 9) / 20))
  hc0 : base3 ((3 * r + 9) / 20) r p ((10*p+2)/3) (r+p-1) < base3 ((3 * r + 9) / 20) r p r ((3*p)-1)
  hc1 : base3 ((3 * r + 9) / 20) r p ((10*p+2)/3) (r+p-1) < base3 ((3 * r + 9) / 20) r p (3*p+1) (((10*p+2)/3)-1)

theorem win {r p : ℕ} (h : Reg r p) :
    Win3 cT cT_pos 3 2 r p (r + p) (((10*p+2)/3)) ((r+p-1)) ((3 * r + 9) / 20) := by
  have hr := h.hr
  have hp3 := h.hp3
  have hlo := h.hlo
  have hhi := h.hhi
  have hp60 := h.hp60
  have hM1 := h.hM1
  have hM2 := h.hM2
  have hP1 := h.hP1
  have hP2 := h.hP2
  have hb1 := h.hb1
  have hb2 := h.hb2
  have hm0 := h.hm0
  have hf1 := h.hf1
  have hf2 := h.hf2
  have hm : (altGeom cT cT_pos).borderSize r = (3 * r + 9) / 20 := borderSize_T hr (by omega)
  have hnd : ¬ p ∣ ((10*p+2)/3) := notdvd_pole (j := 10) (by omega) (by omega)
  exact
    { hr2 := hr, hr0 := by omega, hbs := hm, hrN := by omega, hNp := hNp_T hlo (by omega), hpm := by omega,
      hp2 := by omega, hq0 := by norm_num, hqp := by omega, ho0 := by norm_num, hop := by omega, hqo := by norm_num,
      ht0r := by omega, ht0b := by omega, ht0tv := by omega, htvp := by omega, htvN := by omega,
      hdiv := div_both (x := 3) (by omega) (by omega) (by omega) (by omega), hnt0 := hnd }

theorem nd0 {r p : ℕ} (h : Reg r p) : ¬ p ∣ r := by
  have hr := h.hr
  have hp3 := h.hp3
  have hlo := h.hlo
  have hhi := h.hhi
  have hp60 := h.hp60
  have hM1 := h.hM1
  have hM2 := h.hM2
  have hP1 := h.hP1
  have hP2 := h.hP2
  have hb1 := h.hb1
  have hb2 := h.hb2
  have hm0 := h.hm0
  have hf1 := h.hf1
  have hf2 := h.hf2
  exact notdvd_between (a := 2) (by omega) (by omega)

theorem ns0 {Fr : Frame} (T : TwoTermData Fr 3 2) {r p : ℕ} [Fact p.Prime] (h : Reg r p)
    (hsq : ∀ t, 1 ≤ t → t < r + p → ¬ p ^ 2 ∣ 3 * t - 2) (hnorm : Fr.norm ∈ S p) (hnorm0 : red p Fr.norm ≠ 0) :
    NoSingWin (twoTermPoleData T (hNp_T h.hlo (by have := h.hp60; omega)).le hsq hnorm hnorm0) (r) ((((3*p)-1)) - (r)) := by
  have hr := h.hr
  have hp3 := h.hp3
  have hlo := h.hlo
  have hhi := h.hhi
  have hp60 := h.hp60
  have hM1 := h.hM1
  have hM2 := h.hM2
  have hP1 := h.hP1
  have hP2 := h.hP2
  have hb1 := h.hb1
  have hb2 := h.hb2
  have hm0 := h.hm0
  have hf1 := h.hf1
  have hf2 := h.hf2
  have hnd := nd0 h
  refine noSing_T T _ hsq hnorm hnorm0 _ _ (by omega) (fun k h1 h2 => ?_)
    (nopole_T (fun k h1 h2 => by omega) (fun j hj k h1 h2 h3 => by interval_cases j <;> omega))
  exact notdvd_between (a := 2) (by omega) (by omega)

theorem nd1 {r p : ℕ} (h : Reg r p) : ¬ p ∣ (3*p+1) := by
  have hr := h.hr
  have hp3 := h.hp3
  have hlo := h.hlo
  have hhi := h.hhi
  have hp60 := h.hp60
  have hM1 := h.hM1
  have hM2 := h.hM2
  have hP1 := h.hP1
  have hP2 := h.hP2
  have hb1 := h.hb1
  have hb2 := h.hb2
  have hm0 := h.hm0
  have hf1 := h.hf1
  have hf2 := h.hf2
  exact notdvd_succ_mult (j := 3) (by omega)

theorem ns1 {Fr : Frame} (T : TwoTermData Fr 3 2) {r p : ℕ} [Fact p.Prime] (h : Reg r p)
    (hsq : ∀ t, 1 ≤ t → t < r + p → ¬ p ^ 2 ∣ 3 * t - 2) (hnorm : Fr.norm ∈ S p) (hnorm0 : red p Fr.norm ≠ 0) :
    NoSingWin (twoTermPoleData T (hNp_T h.hlo (by have := h.hp60; omega)).le hsq hnorm hnorm0) ((3*p+1)) (((((10*p+2)/3)-1)) - ((3*p+1))) := by
  have hr := h.hr
  have hp3 := h.hp3
  have hlo := h.hlo
  have hhi := h.hhi
  have hp60 := h.hp60
  have hM1 := h.hM1
  have hM2 := h.hM2
  have hP1 := h.hP1
  have hP2 := h.hP2
  have hb1 := h.hb1
  have hb2 := h.hb2
  have hm0 := h.hm0
  have hf1 := h.hf1
  have hf2 := h.hf2
  have hnd := nd1 h
  refine noSing_T T _ hsq hnorm hnorm0 _ _ (by omega) (fun k h1 h2 => ?_)
    (nopole_T (fun k h1 h2 => by omega) (fun j hj k h1 h2 h3 => by interval_cases j <;> omega))
  exact notdvd_between (a := 3) (by omega) (by omega)

theorem nd2 {r p : ℕ} (h : Reg r p) : ¬ p ∣ ((10*p+2)/3) := by
  have hr := h.hr
  have hp3 := h.hp3
  have hlo := h.hlo
  have hhi := h.hhi
  have hp60 := h.hp60
  have hM1 := h.hM1
  have hM2 := h.hM2
  have hP1 := h.hP1
  have hP2 := h.hP2
  have hb1 := h.hb1
  have hb2 := h.hb2
  have hm0 := h.hm0
  have hf1 := h.hf1
  have hf2 := h.hf2
  exact notdvd_pole (j := 10) (by omega) (by omega)

theorem ns2 {Fr : Frame} (T : TwoTermData Fr 3 2) {r p : ℕ} [Fact p.Prime] (h : Reg r p)
    (hsq : ∀ t, 1 ≤ t → t < r + p → ¬ p ^ 2 ∣ 3 * t - 2) (hnorm : Fr.norm ∈ S p) (hnorm0 : red p Fr.norm ≠ 0) :
    NoSingWin (twoTermPoleData T (hNp_T h.hlo (by have := h.hp60; omega)).le hsq hnorm hnorm0) (((10*p+2)/3)) (((r+p-1)) - (((10*p+2)/3))) := by
  have hr := h.hr
  have hp3 := h.hp3
  have hlo := h.hlo
  have hhi := h.hhi
  have hp60 := h.hp60
  have hM1 := h.hM1
  have hM2 := h.hM2
  have hP1 := h.hP1
  have hP2 := h.hP2
  have hb1 := h.hb1
  have hb2 := h.hb2
  have hm0 := h.hm0
  have hf1 := h.hf1
  have hf2 := h.hf2
  have hnd := nd2 h
  refine noSing_T T _ hsq hnorm hnorm0 _ _ (by omega) (fun k h1 h2 => ?_)
    (nopole_T (fun k h1 h2 => by omega) (fun j hj k h1 h2 h3 => by interval_cases j <;> omega))
  exact notdvd_between (a := 3) (by omega) (by omega)

theorem kill {Fr : Frame} (T : TwoTermData Fr 3 2) {r p : ℕ} [Fact p.Prime] (h : Reg r p) (hn : Fr.norm = 1)
    (hsq : ∀ t, 1 ≤ t → t < r + p → ¬ p ^ 2 ∣ 3 * t - 2) (hnorm : Fr.norm ∈ S p) (hnorm0 : red p Fr.norm ≠ 0) :
    ∀ v, r ≤ v → v < r + 2 * ((3 * r + 9) / 20) → (v < (((10*p+2)/3)) ∨ ((r+p-1)) < v) → ¬ p ∣ v →
      Nonempty (AltKill cT cT_pos (win h).hr2 T (win h).hNp hsq hnorm hnorm0 ((win h).hbs ▸ (win h).hrN) (((10*p+2)/3)) v) := by
  have hr := h.hr
  have hp3 := h.hp3
  have hlo := h.hlo
  have hhi := h.hhi
  have hp60 := h.hp60
  have hM1 := h.hM1
  have hM2 := h.hM2
  have hP1 := h.hP1
  have hP2 := h.hP2
  have hb1 := h.hb1
  have hb2 := h.hb2
  have hm0 := h.hm0
  have hf1 := h.hf1
  have hf2 := h.hf2
  intro v h1 h2 h3 h4
  have hnv : v ≠ 3 * p := fun e => h4 ⟨3, by rw [e]; ring⟩
  rcases (by omega : v < (3*p) ∨ ((3*p+1) ≤ v ∧ v < ((10*p+2)/3)) ∨ ((10*p+2)/3) ≤ v) with hA | hB | hC
  · -- run 0
    exact kill_of_pair T (win h) hsq hnorm hnorm0 (r) v 3 10 2 8
      (by omega) (by omega) (by omega) (nd0 h) (by omega) (by omega)
      (div_both (x := 2) (by omega) (by omega) (by omega) (by omega))
      (nosing_mono (ns0 T h hsq hnorm hnorm0) (by omega))
      (Nat.div_eq_of_lt_le (by omega) (by omega)) (Nat.div_eq_of_lt_le (by omega) (by omega))
      (Nat.div_eq_of_lt_le (by omega) (by omega)) (Nat.div_eq_of_lt_le (by omega) (by omega))
      (pair_1_3_10_2_8 hp3 hp60 hn)
  · -- run 1
    exact kill_of_pair T (win h) hsq hnorm hnorm0 ((3*p+1)) v 3 10 3 9
      (by omega) (by omega) (by omega) (nd1 h) (by omega) (by omega)
      (div_both (x := 3) (by omega) (by omega) (by omega) (by omega))
      (nosing_mono (ns1 T h hsq hnorm hnorm0) (by omega))
      (Nat.div_eq_of_lt_le (by omega) (by omega)) (Nat.div_eq_of_lt_le (by omega) (by omega))
      (Nat.div_eq_of_lt_le (by omega) (by omega)) (Nat.div_eq_of_lt_le (by omega) (by omega))
      (pair_1_3_10_3_9 hp3 hp60 hn)
  · -- run 2
    exfalso; omega

noncomputable def cell {Fr : Frame} (T : TwoTermData Fr 3 2) {r p : ℕ} [Fact p.Prime] (h : Reg r p)
    (hn : Fr.norm = 1) (hnorm : Fr.norm ∈ S p) (hnorm0 : red p Fr.norm ≠ 0) : Cell3 cT cT_pos Fr 3 2 T r p :=
  cell3Gen T (win h) (hsq_T h.hlo (by have := h.hp60; omega)) hnorm hnorm0
    (ns2 T h (hsq_T h.hlo (by have := h.hp60; omega)) hnorm hnorm0)
    (kill T h hn (hsq_T h.hlo (by have := h.hp60; omega)) hnorm hnorm0)

theorem cell_bound {Fr : Frame} (T : TwoTermData Fr 3 2) {r p : ℕ} [Fact p.Prime] (h : Reg r p)
    (hn : Fr.norm = 1) (hnorm : Fr.norm ∈ S p) (hnorm0 : red p Fr.norm ≠ 0) :
    (cell T h hn hnorm hnorm0).bound = base3 ((3 * r + 9) / 20) r p (((10*p+2)/3)) ((r+p-1)) := by
  unfold cell; exact cell3Gen_bound T (win h) _ _ _ _ _

def T0 (r p : ℕ) : ℕ := ((10*p+2)/3)
def TV (r p : ℕ) : ℕ := (r+p-1)

end F20

namespace F21

structure Reg (r p : ℕ) : Prop where
  hr : r % 2 = 0
  hp3 : p % 3 = 1
  hlo : 3 * r < 10 * p
  hhi : 10 * p ≤ 39 * r
  hp60 : 60 ≤ p
  hM1 : 2 * p < r
  hM2 : r ≤ 3 * p
  hP1 : 4 * p + 2 < 3 * r
  hP2 : 3 * r ≤ 7 * p + 2
  hb1 : 6 * p + 2 ≤ 3 * r
  hb2 : 3 * r < 7 * p + 2
  hm0 : r < ((7*p+2)/3)
  hf1 : ((7*p+2)/3) < (r + 2 * ((3 * r + 9) / 20))
  hf2 : (r + 2 * ((3 * r + 9) / 20)) ≤ (3*p+1)
  hc1 : base3 ((3 * r + 9) / 20) r p r (((7*p+2)/3)-1) ≤ base3 ((3 * r + 9) / 20) r p ((7*p+2)/3) ((3*p)-1)

theorem win {r p : ℕ} (h : Reg r p) :
    Win3 cT cT_pos 3 2 r p (r + p) (r) ((((7*p+2)/3)-1)) ((3 * r + 9) / 20) := by
  have hr := h.hr
  have hp3 := h.hp3
  have hlo := h.hlo
  have hhi := h.hhi
  have hp60 := h.hp60
  have hM1 := h.hM1
  have hM2 := h.hM2
  have hP1 := h.hP1
  have hP2 := h.hP2
  have hb1 := h.hb1
  have hb2 := h.hb2
  have hm0 := h.hm0
  have hf1 := h.hf1
  have hf2 := h.hf2
  have hm : (altGeom cT cT_pos).borderSize r = (3 * r + 9) / 20 := borderSize_T hr (by omega)
  have hnd : ¬ p ∣ r := notdvd_between (a := 2) (by omega) (by omega)
  exact
    { hr2 := hr, hr0 := by omega, hbs := hm, hrN := by omega, hNp := hNp_T hlo (by omega), hpm := by omega,
      hp2 := by omega, hq0 := by norm_num, hqp := by omega, ho0 := by norm_num, hop := by omega, hqo := by norm_num,
      ht0r := by omega, ht0b := by omega, ht0tv := by omega, htvp := by omega, htvN := by omega,
      hdiv := div_both (x := 2) (by omega) (by omega) (by omega) (by omega), hnt0 := hnd }

theorem nd0 {r p : ℕ} (h : Reg r p) : ¬ p ∣ r := by
  have hr := h.hr
  have hp3 := h.hp3
  have hlo := h.hlo
  have hhi := h.hhi
  have hp60 := h.hp60
  have hM1 := h.hM1
  have hM2 := h.hM2
  have hP1 := h.hP1
  have hP2 := h.hP2
  have hb1 := h.hb1
  have hb2 := h.hb2
  have hm0 := h.hm0
  have hf1 := h.hf1
  have hf2 := h.hf2
  exact notdvd_between (a := 2) (by omega) (by omega)

theorem ns0 {Fr : Frame} (T : TwoTermData Fr 3 2) {r p : ℕ} [Fact p.Prime] (h : Reg r p)
    (hsq : ∀ t, 1 ≤ t → t < r + p → ¬ p ^ 2 ∣ 3 * t - 2) (hnorm : Fr.norm ∈ S p) (hnorm0 : red p Fr.norm ≠ 0) :
    NoSingWin (twoTermPoleData T (hNp_T h.hlo (by have := h.hp60; omega)).le hsq hnorm hnorm0) (r) (((((7*p+2)/3)-1)) - (r)) := by
  have hr := h.hr
  have hp3 := h.hp3
  have hlo := h.hlo
  have hhi := h.hhi
  have hp60 := h.hp60
  have hM1 := h.hM1
  have hM2 := h.hM2
  have hP1 := h.hP1
  have hP2 := h.hP2
  have hb1 := h.hb1
  have hb2 := h.hb2
  have hm0 := h.hm0
  have hf1 := h.hf1
  have hf2 := h.hf2
  have hnd := nd0 h
  refine noSing_T T _ hsq hnorm hnorm0 _ _ (by omega) (fun k h1 h2 => ?_)
    (nopole_T (fun k h1 h2 => by omega) (fun j hj k h1 h2 h3 => by interval_cases j <;> omega))
  exact notdvd_between (a := 2) (by omega) (by omega)

theorem nd1 {r p : ℕ} (h : Reg r p) : ¬ p ∣ ((7*p+2)/3) := by
  have hr := h.hr
  have hp3 := h.hp3
  have hlo := h.hlo
  have hhi := h.hhi
  have hp60 := h.hp60
  have hM1 := h.hM1
  have hM2 := h.hM2
  have hP1 := h.hP1
  have hP2 := h.hP2
  have hb1 := h.hb1
  have hb2 := h.hb2
  have hm0 := h.hm0
  have hf1 := h.hf1
  have hf2 := h.hf2
  exact notdvd_pole (j := 7) (by omega) (by omega)

theorem ns1 {Fr : Frame} (T : TwoTermData Fr 3 2) {r p : ℕ} [Fact p.Prime] (h : Reg r p)
    (hsq : ∀ t, 1 ≤ t → t < r + p → ¬ p ^ 2 ∣ 3 * t - 2) (hnorm : Fr.norm ∈ S p) (hnorm0 : red p Fr.norm ≠ 0) :
    NoSingWin (twoTermPoleData T (hNp_T h.hlo (by have := h.hp60; omega)).le hsq hnorm hnorm0) (((7*p+2)/3)) ((((3*p)-1)) - (((7*p+2)/3))) := by
  have hr := h.hr
  have hp3 := h.hp3
  have hlo := h.hlo
  have hhi := h.hhi
  have hp60 := h.hp60
  have hM1 := h.hM1
  have hM2 := h.hM2
  have hP1 := h.hP1
  have hP2 := h.hP2
  have hb1 := h.hb1
  have hb2 := h.hb2
  have hm0 := h.hm0
  have hf1 := h.hf1
  have hf2 := h.hf2
  have hnd := nd1 h
  refine noSing_T T _ hsq hnorm hnorm0 _ _ (by omega) (fun k h1 h2 => ?_)
    (nopole_T (fun k h1 h2 => by omega) (fun j hj k h1 h2 h3 => by interval_cases j <;> omega))
  exact notdvd_between (a := 2) (by omega) (by omega)

theorem kill {Fr : Frame} (T : TwoTermData Fr 3 2) {r p : ℕ} [Fact p.Prime] (h : Reg r p) (hn : Fr.norm = 1)
    (hsq : ∀ t, 1 ≤ t → t < r + p → ¬ p ^ 2 ∣ 3 * t - 2) (hnorm : Fr.norm ∈ S p) (hnorm0 : red p Fr.norm ≠ 0) :
    ∀ v, r ≤ v → v < r + 2 * ((3 * r + 9) / 20) → (v < (r) ∨ ((((7*p+2)/3)-1)) < v) → ¬ p ∣ v →
      Nonempty (AltKill cT cT_pos (win h).hr2 T (win h).hNp hsq hnorm hnorm0 ((win h).hbs ▸ (win h).hrN) (r) v) := by
  have hr := h.hr
  have hp3 := h.hp3
  have hlo := h.hlo
  have hhi := h.hhi
  have hp60 := h.hp60
  have hM1 := h.hM1
  have hM2 := h.hM2
  have hP1 := h.hP1
  have hP2 := h.hP2
  have hb1 := h.hb1
  have hb2 := h.hb2
  have hm0 := h.hm0
  have hf1 := h.hf1
  have hf2 := h.hf2
  intro v h1 h2 h3 h4
  have hnv : v ≠ 3 * p := fun e => h4 ⟨3, by rw [e]; ring⟩
  rcases (by omega : v < ((7*p+2)/3) ∨ (((7*p+2)/3) ≤ v ∧ v < (3*p)) ∨ (3*p+1) ≤ v) with hA | hB | hC
  · -- run 0
    exfalso; omega
  · -- run 1
    exact kill_of_pair T (win h) hsq hnorm hnorm0 (((7*p+2)/3)) v 2 6 2 7
      (by omega) (by omega) (by omega) (nd1 h) (by omega) (by omega)
      (div_both (x := 2) (by omega) (by omega) (by omega) (by omega))
      (nosing_mono (ns1 T h hsq hnorm hnorm0) (by omega))
      (Nat.div_eq_of_lt_le (by omega) (by omega)) (Nat.div_eq_of_lt_le (by omega) (by omega))
      (Nat.div_eq_of_lt_le (by omega) (by omega)) (Nat.div_eq_of_lt_le (by omega) (by omega))
      (pair_1_2_6_2_7 hp3 hp60 hn)
  · -- run 2
    exfalso; omega

noncomputable def cell {Fr : Frame} (T : TwoTermData Fr 3 2) {r p : ℕ} [Fact p.Prime] (h : Reg r p)
    (hn : Fr.norm = 1) (hnorm : Fr.norm ∈ S p) (hnorm0 : red p Fr.norm ≠ 0) : Cell3 cT cT_pos Fr 3 2 T r p :=
  cell3Gen T (win h) (hsq_T h.hlo (by have := h.hp60; omega)) hnorm hnorm0
    (ns0 T h (hsq_T h.hlo (by have := h.hp60; omega)) hnorm hnorm0)
    (kill T h hn (hsq_T h.hlo (by have := h.hp60; omega)) hnorm hnorm0)

theorem cell_bound {Fr : Frame} (T : TwoTermData Fr 3 2) {r p : ℕ} [Fact p.Prime] (h : Reg r p)
    (hn : Fr.norm = 1) (hnorm : Fr.norm ∈ S p) (hnorm0 : red p Fr.norm ≠ 0) :
    (cell T h hn hnorm hnorm0).bound = base3 ((3 * r + 9) / 20) r p (r) ((((7*p+2)/3)-1)) := by
  unfold cell; exact cell3Gen_bound T (win h) _ _ _ _ _

def T0 (r p : ℕ) : ℕ := r
def TV (r p : ℕ) : ℕ := (((7*p+2)/3)-1)

end F21

namespace F22

structure Reg (r p : ℕ) : Prop where
  hr : r % 2 = 0
  hp3 : p % 3 = 1
  hlo : 3 * r < 10 * p
  hhi : 10 * p ≤ 39 * r
  hp60 : 60 ≤ p
  hM1 : 2 * p < r
  hM2 : r ≤ 3 * p
  hP1 : 4 * p + 2 < 3 * r
  hP2 : 3 * r ≤ 7 * p + 2
  hb1 : 6 * p + 2 ≤ 3 * r
  hb2 : 3 * r < 7 * p + 2
  hm0 : r < ((7*p+2)/3)
  hf1 : ((7*p+2)/3) < (r + 2 * ((3 * r + 9) / 20))
  hf2 : (r + 2 * ((3 * r + 9) / 20)) ≤ (3*p+1)
  hc0 : base3 ((3 * r + 9) / 20) r p ((7*p+2)/3) ((3*p)-1) < base3 ((3 * r + 9) / 20) r p r (((7*p+2)/3)-1)

theorem win {r p : ℕ} (h : Reg r p) :
    Win3 cT cT_pos 3 2 r p (r + p) (((7*p+2)/3)) (((3*p)-1)) ((3 * r + 9) / 20) := by
  have hr := h.hr
  have hp3 := h.hp3
  have hlo := h.hlo
  have hhi := h.hhi
  have hp60 := h.hp60
  have hM1 := h.hM1
  have hM2 := h.hM2
  have hP1 := h.hP1
  have hP2 := h.hP2
  have hb1 := h.hb1
  have hb2 := h.hb2
  have hm0 := h.hm0
  have hf1 := h.hf1
  have hf2 := h.hf2
  have hm : (altGeom cT cT_pos).borderSize r = (3 * r + 9) / 20 := borderSize_T hr (by omega)
  have hnd : ¬ p ∣ ((7*p+2)/3) := notdvd_pole (j := 7) (by omega) (by omega)
  exact
    { hr2 := hr, hr0 := by omega, hbs := hm, hrN := by omega, hNp := hNp_T hlo (by omega), hpm := by omega,
      hp2 := by omega, hq0 := by norm_num, hqp := by omega, ho0 := by norm_num, hop := by omega, hqo := by norm_num,
      ht0r := by omega, ht0b := by omega, ht0tv := by omega, htvp := by omega, htvN := by omega,
      hdiv := div_both (x := 2) (by omega) (by omega) (by omega) (by omega), hnt0 := hnd }

theorem nd0 {r p : ℕ} (h : Reg r p) : ¬ p ∣ r := by
  have hr := h.hr
  have hp3 := h.hp3
  have hlo := h.hlo
  have hhi := h.hhi
  have hp60 := h.hp60
  have hM1 := h.hM1
  have hM2 := h.hM2
  have hP1 := h.hP1
  have hP2 := h.hP2
  have hb1 := h.hb1
  have hb2 := h.hb2
  have hm0 := h.hm0
  have hf1 := h.hf1
  have hf2 := h.hf2
  exact notdvd_between (a := 2) (by omega) (by omega)

theorem ns0 {Fr : Frame} (T : TwoTermData Fr 3 2) {r p : ℕ} [Fact p.Prime] (h : Reg r p)
    (hsq : ∀ t, 1 ≤ t → t < r + p → ¬ p ^ 2 ∣ 3 * t - 2) (hnorm : Fr.norm ∈ S p) (hnorm0 : red p Fr.norm ≠ 0) :
    NoSingWin (twoTermPoleData T (hNp_T h.hlo (by have := h.hp60; omega)).le hsq hnorm hnorm0) (r) (((((7*p+2)/3)-1)) - (r)) := by
  have hr := h.hr
  have hp3 := h.hp3
  have hlo := h.hlo
  have hhi := h.hhi
  have hp60 := h.hp60
  have hM1 := h.hM1
  have hM2 := h.hM2
  have hP1 := h.hP1
  have hP2 := h.hP2
  have hb1 := h.hb1
  have hb2 := h.hb2
  have hm0 := h.hm0
  have hf1 := h.hf1
  have hf2 := h.hf2
  have hnd := nd0 h
  refine noSing_T T _ hsq hnorm hnorm0 _ _ (by omega) (fun k h1 h2 => ?_)
    (nopole_T (fun k h1 h2 => by omega) (fun j hj k h1 h2 h3 => by interval_cases j <;> omega))
  exact notdvd_between (a := 2) (by omega) (by omega)

theorem nd1 {r p : ℕ} (h : Reg r p) : ¬ p ∣ ((7*p+2)/3) := by
  have hr := h.hr
  have hp3 := h.hp3
  have hlo := h.hlo
  have hhi := h.hhi
  have hp60 := h.hp60
  have hM1 := h.hM1
  have hM2 := h.hM2
  have hP1 := h.hP1
  have hP2 := h.hP2
  have hb1 := h.hb1
  have hb2 := h.hb2
  have hm0 := h.hm0
  have hf1 := h.hf1
  have hf2 := h.hf2
  exact notdvd_pole (j := 7) (by omega) (by omega)

theorem ns1 {Fr : Frame} (T : TwoTermData Fr 3 2) {r p : ℕ} [Fact p.Prime] (h : Reg r p)
    (hsq : ∀ t, 1 ≤ t → t < r + p → ¬ p ^ 2 ∣ 3 * t - 2) (hnorm : Fr.norm ∈ S p) (hnorm0 : red p Fr.norm ≠ 0) :
    NoSingWin (twoTermPoleData T (hNp_T h.hlo (by have := h.hp60; omega)).le hsq hnorm hnorm0) (((7*p+2)/3)) ((((3*p)-1)) - (((7*p+2)/3))) := by
  have hr := h.hr
  have hp3 := h.hp3
  have hlo := h.hlo
  have hhi := h.hhi
  have hp60 := h.hp60
  have hM1 := h.hM1
  have hM2 := h.hM2
  have hP1 := h.hP1
  have hP2 := h.hP2
  have hb1 := h.hb1
  have hb2 := h.hb2
  have hm0 := h.hm0
  have hf1 := h.hf1
  have hf2 := h.hf2
  have hnd := nd1 h
  refine noSing_T T _ hsq hnorm hnorm0 _ _ (by omega) (fun k h1 h2 => ?_)
    (nopole_T (fun k h1 h2 => by omega) (fun j hj k h1 h2 h3 => by interval_cases j <;> omega))
  exact notdvd_between (a := 2) (by omega) (by omega)

theorem kill {Fr : Frame} (T : TwoTermData Fr 3 2) {r p : ℕ} [Fact p.Prime] (h : Reg r p) (hn : Fr.norm = 1)
    (hsq : ∀ t, 1 ≤ t → t < r + p → ¬ p ^ 2 ∣ 3 * t - 2) (hnorm : Fr.norm ∈ S p) (hnorm0 : red p Fr.norm ≠ 0) :
    ∀ v, r ≤ v → v < r + 2 * ((3 * r + 9) / 20) → (v < (((7*p+2)/3)) ∨ (((3*p)-1)) < v) → ¬ p ∣ v →
      Nonempty (AltKill cT cT_pos (win h).hr2 T (win h).hNp hsq hnorm hnorm0 ((win h).hbs ▸ (win h).hrN) (((7*p+2)/3)) v) := by
  have hr := h.hr
  have hp3 := h.hp3
  have hlo := h.hlo
  have hhi := h.hhi
  have hp60 := h.hp60
  have hM1 := h.hM1
  have hM2 := h.hM2
  have hP1 := h.hP1
  have hP2 := h.hP2
  have hb1 := h.hb1
  have hb2 := h.hb2
  have hm0 := h.hm0
  have hf1 := h.hf1
  have hf2 := h.hf2
  intro v h1 h2 h3 h4
  have hnv : v ≠ 3 * p := fun e => h4 ⟨3, by rw [e]; ring⟩
  rcases (by omega : v < ((7*p+2)/3) ∨ (((7*p+2)/3) ≤ v ∧ v < (3*p)) ∨ (3*p+1) ≤ v) with hA | hB | hC
  · -- run 0
    exact kill_of_pair T (win h) hsq hnorm hnorm0 (r) v 2 7 2 6
      (by omega) (by omega) (by omega) (nd0 h) (by omega) (by omega)
      (div_both (x := 2) (by omega) (by omega) (by omega) (by omega))
      (nosing_mono (ns0 T h hsq hnorm hnorm0) (by omega))
      (Nat.div_eq_of_lt_le (by omega) (by omega)) (Nat.div_eq_of_lt_le (by omega) (by omega))
      (Nat.div_eq_of_lt_le (by omega) (by omega)) (Nat.div_eq_of_lt_le (by omega) (by omega))
      (pair_1_2_7_2_6 hp3 hp60 hn)
  · -- run 1
    exfalso; omega
  · -- run 2
    exfalso; omega

noncomputable def cell {Fr : Frame} (T : TwoTermData Fr 3 2) {r p : ℕ} [Fact p.Prime] (h : Reg r p)
    (hn : Fr.norm = 1) (hnorm : Fr.norm ∈ S p) (hnorm0 : red p Fr.norm ≠ 0) : Cell3 cT cT_pos Fr 3 2 T r p :=
  cell3Gen T (win h) (hsq_T h.hlo (by have := h.hp60; omega)) hnorm hnorm0
    (ns1 T h (hsq_T h.hlo (by have := h.hp60; omega)) hnorm hnorm0)
    (kill T h hn (hsq_T h.hlo (by have := h.hp60; omega)) hnorm hnorm0)

theorem cell_bound {Fr : Frame} (T : TwoTermData Fr 3 2) {r p : ℕ} [Fact p.Prime] (h : Reg r p)
    (hn : Fr.norm = 1) (hnorm : Fr.norm ∈ S p) (hnorm0 : red p Fr.norm ≠ 0) :
    (cell T h hn hnorm hnorm0).bound = base3 ((3 * r + 9) / 20) r p (((7*p+2)/3)) (((3*p)-1)) := by
  unfold cell; exact cell3Gen_bound T (win h) _ _ _ _ _

def T0 (r p : ℕ) : ℕ := ((7*p+2)/3)
def TV (r p : ℕ) : ℕ := ((3*p)-1)

end F22

namespace F23

structure Reg (r p : ℕ) : Prop where
  hr : r % 2 = 0
  hp3 : p % 3 = 1
  hlo : 3 * r < 10 * p
  hhi : 10 * p ≤ 39 * r
  hp60 : 60 ≤ p
  hM1 : 2 * p < r
  hM2 : r ≤ 3 * p
  hP1 : 4 * p + 2 < 3 * r
  hP2 : 3 * r ≤ 7 * p + 2
  hb1 : 6 * p + 2 ≤ 3 * r
  hb2 : 3 * r < 7 * p + 2
  hm0 : r < ((7*p+2)/3)
  hf1 : ((7*p+2)/3) < (r + 2 * ((3 * r + 9) / 20))
  hf2 : (3*p+1) < (r + 2 * ((3 * r + 9) / 20))
  hc0 : base3 ((3 * r + 9) / 20) r p ((7*p+2)/3) ((3*p)-1) < base3 ((3 * r + 9) / 20) r p r (((7*p+2)/3)-1)
  hc2 : base3 ((3 * r + 9) / 20) r p ((7*p+2)/3) ((3*p)-1) ≤ base3 ((3 * r + 9) / 20) r p (3*p+1) (r+p-1)

theorem win {r p : ℕ} (h : Reg r p) :
    Win3 cT cT_pos 3 2 r p (r + p) (((7*p+2)/3)) (((3*p)-1)) ((3 * r + 9) / 20) := by
  have hr := h.hr
  have hp3 := h.hp3
  have hlo := h.hlo
  have hhi := h.hhi
  have hp60 := h.hp60
  have hM1 := h.hM1
  have hM2 := h.hM2
  have hP1 := h.hP1
  have hP2 := h.hP2
  have hb1 := h.hb1
  have hb2 := h.hb2
  have hm0 := h.hm0
  have hf1 := h.hf1
  have hf2 := h.hf2
  have hm : (altGeom cT cT_pos).borderSize r = (3 * r + 9) / 20 := borderSize_T hr (by omega)
  have hnd : ¬ p ∣ ((7*p+2)/3) := notdvd_pole (j := 7) (by omega) (by omega)
  exact
    { hr2 := hr, hr0 := by omega, hbs := hm, hrN := by omega, hNp := hNp_T hlo (by omega), hpm := by omega,
      hp2 := by omega, hq0 := by norm_num, hqp := by omega, ho0 := by norm_num, hop := by omega, hqo := by norm_num,
      ht0r := by omega, ht0b := by omega, ht0tv := by omega, htvp := by omega, htvN := by omega,
      hdiv := div_both (x := 2) (by omega) (by omega) (by omega) (by omega), hnt0 := hnd }

theorem nd0 {r p : ℕ} (h : Reg r p) : ¬ p ∣ r := by
  have hr := h.hr
  have hp3 := h.hp3
  have hlo := h.hlo
  have hhi := h.hhi
  have hp60 := h.hp60
  have hM1 := h.hM1
  have hM2 := h.hM2
  have hP1 := h.hP1
  have hP2 := h.hP2
  have hb1 := h.hb1
  have hb2 := h.hb2
  have hm0 := h.hm0
  have hf1 := h.hf1
  have hf2 := h.hf2
  exact notdvd_between (a := 2) (by omega) (by omega)

theorem ns0 {Fr : Frame} (T : TwoTermData Fr 3 2) {r p : ℕ} [Fact p.Prime] (h : Reg r p)
    (hsq : ∀ t, 1 ≤ t → t < r + p → ¬ p ^ 2 ∣ 3 * t - 2) (hnorm : Fr.norm ∈ S p) (hnorm0 : red p Fr.norm ≠ 0) :
    NoSingWin (twoTermPoleData T (hNp_T h.hlo (by have := h.hp60; omega)).le hsq hnorm hnorm0) (r) (((((7*p+2)/3)-1)) - (r)) := by
  have hr := h.hr
  have hp3 := h.hp3
  have hlo := h.hlo
  have hhi := h.hhi
  have hp60 := h.hp60
  have hM1 := h.hM1
  have hM2 := h.hM2
  have hP1 := h.hP1
  have hP2 := h.hP2
  have hb1 := h.hb1
  have hb2 := h.hb2
  have hm0 := h.hm0
  have hf1 := h.hf1
  have hf2 := h.hf2
  have hnd := nd0 h
  refine noSing_T T _ hsq hnorm hnorm0 _ _ (by omega) (fun k h1 h2 => ?_)
    (nopole_T (fun k h1 h2 => by omega) (fun j hj k h1 h2 h3 => by interval_cases j <;> omega))
  exact notdvd_between (a := 2) (by omega) (by omega)

theorem nd1 {r p : ℕ} (h : Reg r p) : ¬ p ∣ ((7*p+2)/3) := by
  have hr := h.hr
  have hp3 := h.hp3
  have hlo := h.hlo
  have hhi := h.hhi
  have hp60 := h.hp60
  have hM1 := h.hM1
  have hM2 := h.hM2
  have hP1 := h.hP1
  have hP2 := h.hP2
  have hb1 := h.hb1
  have hb2 := h.hb2
  have hm0 := h.hm0
  have hf1 := h.hf1
  have hf2 := h.hf2
  exact notdvd_pole (j := 7) (by omega) (by omega)

theorem ns1 {Fr : Frame} (T : TwoTermData Fr 3 2) {r p : ℕ} [Fact p.Prime] (h : Reg r p)
    (hsq : ∀ t, 1 ≤ t → t < r + p → ¬ p ^ 2 ∣ 3 * t - 2) (hnorm : Fr.norm ∈ S p) (hnorm0 : red p Fr.norm ≠ 0) :
    NoSingWin (twoTermPoleData T (hNp_T h.hlo (by have := h.hp60; omega)).le hsq hnorm hnorm0) (((7*p+2)/3)) ((((3*p)-1)) - (((7*p+2)/3))) := by
  have hr := h.hr
  have hp3 := h.hp3
  have hlo := h.hlo
  have hhi := h.hhi
  have hp60 := h.hp60
  have hM1 := h.hM1
  have hM2 := h.hM2
  have hP1 := h.hP1
  have hP2 := h.hP2
  have hb1 := h.hb1
  have hb2 := h.hb2
  have hm0 := h.hm0
  have hf1 := h.hf1
  have hf2 := h.hf2
  have hnd := nd1 h
  refine noSing_T T _ hsq hnorm hnorm0 _ _ (by omega) (fun k h1 h2 => ?_)
    (nopole_T (fun k h1 h2 => by omega) (fun j hj k h1 h2 h3 => by interval_cases j <;> omega))
  exact notdvd_between (a := 2) (by omega) (by omega)

theorem nd2 {r p : ℕ} (h : Reg r p) : ¬ p ∣ (3*p+1) := by
  have hr := h.hr
  have hp3 := h.hp3
  have hlo := h.hlo
  have hhi := h.hhi
  have hp60 := h.hp60
  have hM1 := h.hM1
  have hM2 := h.hM2
  have hP1 := h.hP1
  have hP2 := h.hP2
  have hb1 := h.hb1
  have hb2 := h.hb2
  have hm0 := h.hm0
  have hf1 := h.hf1
  have hf2 := h.hf2
  exact notdvd_succ_mult (j := 3) (by omega)

theorem ns2 {Fr : Frame} (T : TwoTermData Fr 3 2) {r p : ℕ} [Fact p.Prime] (h : Reg r p)
    (hsq : ∀ t, 1 ≤ t → t < r + p → ¬ p ^ 2 ∣ 3 * t - 2) (hnorm : Fr.norm ∈ S p) (hnorm0 : red p Fr.norm ≠ 0) :
    NoSingWin (twoTermPoleData T (hNp_T h.hlo (by have := h.hp60; omega)).le hsq hnorm hnorm0) ((3*p+1)) (((r+p-1)) - ((3*p+1))) := by
  have hr := h.hr
  have hp3 := h.hp3
  have hlo := h.hlo
  have hhi := h.hhi
  have hp60 := h.hp60
  have hM1 := h.hM1
  have hM2 := h.hM2
  have hP1 := h.hP1
  have hP2 := h.hP2
  have hb1 := h.hb1
  have hb2 := h.hb2
  have hm0 := h.hm0
  have hf1 := h.hf1
  have hf2 := h.hf2
  have hnd := nd2 h
  refine noSing_T T _ hsq hnorm hnorm0 _ _ (by omega) (fun k h1 h2 => ?_)
    (nopole_T (fun k h1 h2 => by omega) (fun j hj k h1 h2 h3 => by interval_cases j <;> omega))
  exact notdvd_between (a := 3) (by omega) (by omega)

theorem kill {Fr : Frame} (T : TwoTermData Fr 3 2) {r p : ℕ} [Fact p.Prime] (h : Reg r p) (hn : Fr.norm = 1)
    (hsq : ∀ t, 1 ≤ t → t < r + p → ¬ p ^ 2 ∣ 3 * t - 2) (hnorm : Fr.norm ∈ S p) (hnorm0 : red p Fr.norm ≠ 0) :
    ∀ v, r ≤ v → v < r + 2 * ((3 * r + 9) / 20) → (v < (((7*p+2)/3)) ∨ (((3*p)-1)) < v) → ¬ p ∣ v →
      Nonempty (AltKill cT cT_pos (win h).hr2 T (win h).hNp hsq hnorm hnorm0 ((win h).hbs ▸ (win h).hrN) (((7*p+2)/3)) v) := by
  have hr := h.hr
  have hp3 := h.hp3
  have hlo := h.hlo
  have hhi := h.hhi
  have hp60 := h.hp60
  have hM1 := h.hM1
  have hM2 := h.hM2
  have hP1 := h.hP1
  have hP2 := h.hP2
  have hb1 := h.hb1
  have hb2 := h.hb2
  have hm0 := h.hm0
  have hf1 := h.hf1
  have hf2 := h.hf2
  intro v h1 h2 h3 h4
  have hnv : v ≠ 3 * p := fun e => h4 ⟨3, by rw [e]; ring⟩
  rcases (by omega : v < ((7*p+2)/3) ∨ (((7*p+2)/3) ≤ v ∧ v < (3*p)) ∨ (3*p+1) ≤ v) with hA | hB | hC
  · -- run 0
    exact kill_of_pair T (win h) hsq hnorm hnorm0 (r) v 2 7 2 6
      (by omega) (by omega) (by omega) (nd0 h) (by omega) (by omega)
      (div_both (x := 2) (by omega) (by omega) (by omega) (by omega))
      (nosing_mono (ns0 T h hsq hnorm hnorm0) (by omega))
      (Nat.div_eq_of_lt_le (by omega) (by omega)) (Nat.div_eq_of_lt_le (by omega) (by omega))
      (Nat.div_eq_of_lt_le (by omega) (by omega)) (Nat.div_eq_of_lt_le (by omega) (by omega))
      (pair_1_2_7_2_6 hp3 hp60 hn)
  · -- run 1
    exfalso; omega
  · -- run 2
    exact kill_of_pair T (win h) hsq hnorm hnorm0 ((3*p+1)) v 2 7 3 9
      (by omega) (by omega) (by omega) (nd2 h) (by omega) (by omega)
      (div_both (x := 3) (by omega) (by omega) (by omega) (by omega))
      (nosing_mono (ns2 T h hsq hnorm hnorm0) (by omega))
      (Nat.div_eq_of_lt_le (by omega) (by omega)) (Nat.div_eq_of_lt_le (by omega) (by omega))
      (Nat.div_eq_of_lt_le (by omega) (by omega)) (Nat.div_eq_of_lt_le (by omega) (by omega))
      (pair_1_2_7_3_9 hp3 hp60 hn)

noncomputable def cell {Fr : Frame} (T : TwoTermData Fr 3 2) {r p : ℕ} [Fact p.Prime] (h : Reg r p)
    (hn : Fr.norm = 1) (hnorm : Fr.norm ∈ S p) (hnorm0 : red p Fr.norm ≠ 0) : Cell3 cT cT_pos Fr 3 2 T r p :=
  cell3Gen T (win h) (hsq_T h.hlo (by have := h.hp60; omega)) hnorm hnorm0
    (ns1 T h (hsq_T h.hlo (by have := h.hp60; omega)) hnorm hnorm0)
    (kill T h hn (hsq_T h.hlo (by have := h.hp60; omega)) hnorm hnorm0)

theorem cell_bound {Fr : Frame} (T : TwoTermData Fr 3 2) {r p : ℕ} [Fact p.Prime] (h : Reg r p)
    (hn : Fr.norm = 1) (hnorm : Fr.norm ∈ S p) (hnorm0 : red p Fr.norm ≠ 0) :
    (cell T h hn hnorm hnorm0).bound = base3 ((3 * r + 9) / 20) r p (((7*p+2)/3)) (((3*p)-1)) := by
  unfold cell; exact cell3Gen_bound T (win h) _ _ _ _ _

def T0 (r p : ℕ) : ℕ := ((7*p+2)/3)
def TV (r p : ℕ) : ℕ := ((3*p)-1)

end F23

end CatalanCore.Uniform.Content.UFFamily3
