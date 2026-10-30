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
namespace F32

structure Reg (r p : ℕ) : Prop where
  hr : r % 2 = 0
  hp3 : p % 3 = 2
  hlo : 3 * r < 10 * p
  hhi : 10 * p ≤ 39 * r
  hp60 : 60 ≤ p
  hM1 : 0 * p < r
  hM2 : r ≤ 1 * p
  hP1 : 2 * p + 2 < 3 * r
  hP2 : 3 * r ≤ 5 * p + 2
  hb1 : 2 * p + 2 ≤ 3 * r
  hb2 : 3 * r < 3 * p + 2
  hm0 : r < (1*p)
  hf1 : (1*p+1) < (r + 2 * ((3 * r + 9) / 20))
  hf2 : (r + 2 * ((3 * r + 9) / 20)) ≤ ((5*p+2)/3)
  hc1 : base3 ((3 * r + 9) / 20) r p r ((1*p)-1) ≤ base3 ((3 * r + 9) / 20) r p (1*p+1) (((5*p+2)/3)-1)

theorem win {r p : ℕ} (h : Reg r p) :
    Win3 cT cT_pos 3 2 r p (r + p) (r) (((1*p)-1)) ((3 * r + 9) / 20) := by
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
  have hnd : ¬ p ∣ r := notdvd_between (a := 0) (by omega) (by omega)
  exact
    { hr2 := hr, hr0 := by omega, hbs := hm, hrN := by omega, hNp := hNp_T hlo (by omega), hpm := by omega,
      hp2 := by omega, hq0 := by norm_num, hqp := by omega, ho0 := by norm_num, hop := by omega, hqo := by norm_num,
      ht0r := by omega, ht0b := by omega, ht0tv := by omega, htvp := by omega, htvN := by omega,
      hdiv := div_both (x := 0) (by omega) (by omega) (by omega) (by omega), hnt0 := hnd }

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
  exact notdvd_between (a := 0) (by omega) (by omega)

theorem ns0 {Fr : Frame} (T : TwoTermData Fr 3 2) {r p : ℕ} [Fact p.Prime] (h : Reg r p)
    (hsq : ∀ t, 1 ≤ t → t < r + p → ¬ p ^ 2 ∣ 3 * t - 2) (hnorm : Fr.norm ∈ S p) (hnorm0 : red p Fr.norm ≠ 0) :
    NoSingWin (twoTermPoleData T (hNp_T h.hlo (by have := h.hp60; omega)).le hsq hnorm hnorm0) (r) ((((1*p)-1)) - (r)) := by
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
  exact notdvd_between (a := 0) (by omega) (by omega)

theorem nd1 {r p : ℕ} (h : Reg r p) : ¬ p ∣ (1*p+1) := by
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
  exact notdvd_succ_mult (j := 1) (by omega)

theorem ns1 {Fr : Frame} (T : TwoTermData Fr 3 2) {r p : ℕ} [Fact p.Prime] (h : Reg r p)
    (hsq : ∀ t, 1 ≤ t → t < r + p → ¬ p ^ 2 ∣ 3 * t - 2) (hnorm : Fr.norm ∈ S p) (hnorm0 : red p Fr.norm ≠ 0) :
    NoSingWin (twoTermPoleData T (hNp_T h.hlo (by have := h.hp60; omega)).le hsq hnorm hnorm0) ((1*p+1)) (((((5*p+2)/3)-1)) - ((1*p+1))) := by
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
  exact notdvd_between (a := 1) (by omega) (by omega)

theorem kill {Fr : Frame} (T : TwoTermData Fr 3 2) {r p : ℕ} [Fact p.Prime] (h : Reg r p) (hn : Fr.norm = 1)
    (hsq : ∀ t, 1 ≤ t → t < r + p → ¬ p ^ 2 ∣ 3 * t - 2) (hnorm : Fr.norm ∈ S p) (hnorm0 : red p Fr.norm ≠ 0) :
    ∀ v, r ≤ v → v < r + 2 * ((3 * r + 9) / 20) → (v < (r) ∨ (((1*p)-1)) < v) → ¬ p ∣ v →
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
  have hnv : v ≠ 1 * p := fun e => h4 ⟨1, by rw [e]; ring⟩
  rcases (by omega : v < (1*p) ∨ ((1*p+1) ≤ v ∧ v < ((5*p+2)/3)) ∨ ((5*p+2)/3) ≤ v) with hA | hB | hC
  · -- run 0
    exfalso; omega
  · -- run 1
    exact kill_of_pair T (win h) hsq hnorm hnorm0 ((1*p+1)) v 0 2 1 3
      (by omega) (by omega) (by omega) (nd1 h) (by omega) (by omega)
      (div_both (x := 1) (by omega) (by omega) (by omega) (by omega))
      (nosing_mono (ns1 T h hsq hnorm hnorm0) (by omega))
      (Nat.div_eq_of_lt_le (by omega) (by omega)) (Nat.div_eq_of_lt_le (by omega) (by omega))
      (Nat.div_eq_of_lt_le (by omega) (by omega)) (Nat.div_eq_of_lt_le (by omega) (by omega))
      (pair_2_0_2_1_3 hp3 hp60 hn)
  · -- run 2
    exfalso; omega

noncomputable def cell {Fr : Frame} (T : TwoTermData Fr 3 2) {r p : ℕ} [Fact p.Prime] (h : Reg r p)
    (hn : Fr.norm = 1) (hnorm : Fr.norm ∈ S p) (hnorm0 : red p Fr.norm ≠ 0) : Cell3 cT cT_pos Fr 3 2 T r p :=
  cell3Gen T (win h) (hsq_T h.hlo (by have := h.hp60; omega)) hnorm hnorm0
    (ns0 T h (hsq_T h.hlo (by have := h.hp60; omega)) hnorm hnorm0)
    (kill T h hn (hsq_T h.hlo (by have := h.hp60; omega)) hnorm hnorm0)

theorem cell_bound {Fr : Frame} (T : TwoTermData Fr 3 2) {r p : ℕ} [Fact p.Prime] (h : Reg r p)
    (hn : Fr.norm = 1) (hnorm : Fr.norm ∈ S p) (hnorm0 : red p Fr.norm ≠ 0) :
    (cell T h hn hnorm hnorm0).bound = base3 ((3 * r + 9) / 20) r p (r) (((1*p)-1)) := by
  unfold cell; exact cell3Gen_bound T (win h) _ _ _ _ _

def T0 (r p : ℕ) : ℕ := r
def TV (r p : ℕ) : ℕ := ((1*p)-1)

end F32

namespace F33

structure Reg (r p : ℕ) : Prop where
  hr : r % 2 = 0
  hp3 : p % 3 = 2
  hlo : 3 * r < 10 * p
  hhi : 10 * p ≤ 39 * r
  hp60 : 60 ≤ p
  hM1 : 0 * p < r
  hM2 : r ≤ 1 * p
  hP1 : 2 * p + 2 < 3 * r
  hP2 : 3 * r ≤ 5 * p + 2
  hb1 : 2 * p + 2 ≤ 3 * r
  hb2 : 3 * r < 3 * p + 2
  hm0 : r < (1*p)
  hf1 : (1*p+1) < (r + 2 * ((3 * r + 9) / 20))
  hf2 : (r + 2 * ((3 * r + 9) / 20)) ≤ ((5*p+2)/3)
  hc0 : base3 ((3 * r + 9) / 20) r p (1*p+1) (((5*p+2)/3)-1) < base3 ((3 * r + 9) / 20) r p r ((1*p)-1)

theorem win {r p : ℕ} (h : Reg r p) :
    Win3 cT cT_pos 3 2 r p (r + p) ((1*p+1)) ((((5*p+2)/3)-1)) ((3 * r + 9) / 20) := by
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
  have hnd : ¬ p ∣ (1*p+1) := notdvd_succ_mult (j := 1) (by omega)
  exact
    { hr2 := hr, hr0 := by omega, hbs := hm, hrN := by omega, hNp := hNp_T hlo (by omega), hpm := by omega,
      hp2 := by omega, hq0 := by norm_num, hqp := by omega, ho0 := by norm_num, hop := by omega, hqo := by norm_num,
      ht0r := by omega, ht0b := by omega, ht0tv := by omega, htvp := by omega, htvN := by omega,
      hdiv := div_both (x := 1) (by omega) (by omega) (by omega) (by omega), hnt0 := hnd }

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
  exact notdvd_between (a := 0) (by omega) (by omega)

theorem ns0 {Fr : Frame} (T : TwoTermData Fr 3 2) {r p : ℕ} [Fact p.Prime] (h : Reg r p)
    (hsq : ∀ t, 1 ≤ t → t < r + p → ¬ p ^ 2 ∣ 3 * t - 2) (hnorm : Fr.norm ∈ S p) (hnorm0 : red p Fr.norm ≠ 0) :
    NoSingWin (twoTermPoleData T (hNp_T h.hlo (by have := h.hp60; omega)).le hsq hnorm hnorm0) (r) ((((1*p)-1)) - (r)) := by
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
  exact notdvd_between (a := 0) (by omega) (by omega)

theorem nd1 {r p : ℕ} (h : Reg r p) : ¬ p ∣ (1*p+1) := by
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
  exact notdvd_succ_mult (j := 1) (by omega)

theorem ns1 {Fr : Frame} (T : TwoTermData Fr 3 2) {r p : ℕ} [Fact p.Prime] (h : Reg r p)
    (hsq : ∀ t, 1 ≤ t → t < r + p → ¬ p ^ 2 ∣ 3 * t - 2) (hnorm : Fr.norm ∈ S p) (hnorm0 : red p Fr.norm ≠ 0) :
    NoSingWin (twoTermPoleData T (hNp_T h.hlo (by have := h.hp60; omega)).le hsq hnorm hnorm0) ((1*p+1)) (((((5*p+2)/3)-1)) - ((1*p+1))) := by
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
  exact notdvd_between (a := 1) (by omega) (by omega)

theorem kill {Fr : Frame} (T : TwoTermData Fr 3 2) {r p : ℕ} [Fact p.Prime] (h : Reg r p) (hn : Fr.norm = 1)
    (hsq : ∀ t, 1 ≤ t → t < r + p → ¬ p ^ 2 ∣ 3 * t - 2) (hnorm : Fr.norm ∈ S p) (hnorm0 : red p Fr.norm ≠ 0) :
    ∀ v, r ≤ v → v < r + 2 * ((3 * r + 9) / 20) → (v < ((1*p+1)) ∨ ((((5*p+2)/3)-1)) < v) → ¬ p ∣ v →
      Nonempty (AltKill cT cT_pos (win h).hr2 T (win h).hNp hsq hnorm hnorm0 ((win h).hbs ▸ (win h).hrN) ((1*p+1)) v) := by
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
  have hnv : v ≠ 1 * p := fun e => h4 ⟨1, by rw [e]; ring⟩
  rcases (by omega : v < (1*p) ∨ ((1*p+1) ≤ v ∧ v < ((5*p+2)/3)) ∨ ((5*p+2)/3) ≤ v) with hA | hB | hC
  · -- run 0
    exact kill_of_pair T (win h) hsq hnorm hnorm0 (r) v 1 3 0 2
      (by omega) (by omega) (by omega) (nd0 h) (by omega) (by omega)
      (div_both (x := 0) (by omega) (by omega) (by omega) (by omega))
      (nosing_mono (ns0 T h hsq hnorm hnorm0) (by omega))
      (Nat.div_eq_of_lt_le (by omega) (by omega)) (Nat.div_eq_of_lt_le (by omega) (by omega))
      (Nat.div_eq_of_lt_le (by omega) (by omega)) (Nat.div_eq_of_lt_le (by omega) (by omega))
      (pair_2_1_3_0_2 hp3 hp60 hn)
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
    (cell T h hn hnorm hnorm0).bound = base3 ((3 * r + 9) / 20) r p ((1*p+1)) ((((5*p+2)/3)-1)) := by
  unfold cell; exact cell3Gen_bound T (win h) _ _ _ _ _

def T0 (r p : ℕ) : ℕ := (1*p+1)
def TV (r p : ℕ) : ℕ := (((5*p+2)/3)-1)

end F33

namespace F34

structure Reg (r p : ℕ) : Prop where
  hr : r % 2 = 0
  hp3 : p % 3 = 2
  hlo : 3 * r < 10 * p
  hhi : 10 * p ≤ 39 * r
  hp60 : 60 ≤ p
  hM1 : 1 * p < r
  hM2 : r ≤ 2 * p
  hP1 : 2 * p + 2 < 3 * r
  hP2 : 3 * r ≤ 5 * p + 2
  hb1 : 3 * p + 2 ≤ 3 * r
  hb2 : 3 * r < 4 * p + 2
  hm0 : r < ((5*p+2)/3)
  hf1 : (r + 2 * ((3 * r + 9) / 20)) ≤ ((5*p+2)/3)
  hf2 : (r + 2 * ((3 * r + 9) / 20)) ≤ (2*p+1)

theorem win {r p : ℕ} (h : Reg r p) :
    Win3 cT cT_pos 3 2 r p (r + p) (r) ((((5*p+2)/3)-1)) ((3 * r + 9) / 20) := by
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
  have hnd : ¬ p ∣ r := notdvd_between (a := 1) (by omega) (by omega)
  exact
    { hr2 := hr, hr0 := by omega, hbs := hm, hrN := by omega, hNp := hNp_T hlo (by omega), hpm := by omega,
      hp2 := by omega, hq0 := by norm_num, hqp := by omega, ho0 := by norm_num, hop := by omega, hqo := by norm_num,
      ht0r := by omega, ht0b := by omega, ht0tv := by omega, htvp := by omega, htvN := by omega,
      hdiv := div_both (x := 1) (by omega) (by omega) (by omega) (by omega), hnt0 := hnd }

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
  exact notdvd_between (a := 1) (by omega) (by omega)

theorem ns0 {Fr : Frame} (T : TwoTermData Fr 3 2) {r p : ℕ} [Fact p.Prime] (h : Reg r p)
    (hsq : ∀ t, 1 ≤ t → t < r + p → ¬ p ^ 2 ∣ 3 * t - 2) (hnorm : Fr.norm ∈ S p) (hnorm0 : red p Fr.norm ≠ 0) :
    NoSingWin (twoTermPoleData T (hNp_T h.hlo (by have := h.hp60; omega)).le hsq hnorm hnorm0) (r) (((((5*p+2)/3)-1)) - (r)) := by
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
  exact notdvd_between (a := 1) (by omega) (by omega)

theorem kill {Fr : Frame} (T : TwoTermData Fr 3 2) {r p : ℕ} [Fact p.Prime] (h : Reg r p) (hn : Fr.norm = 1)
    (hsq : ∀ t, 1 ≤ t → t < r + p → ¬ p ^ 2 ∣ 3 * t - 2) (hnorm : Fr.norm ∈ S p) (hnorm0 : red p Fr.norm ≠ 0) :
    ∀ v, r ≤ v → v < r + 2 * ((3 * r + 9) / 20) → (v < (r) ∨ ((((5*p+2)/3)-1)) < v) → ¬ p ∣ v →
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
  have hnv : v ≠ 2 * p := fun e => h4 ⟨2, by rw [e]; ring⟩
  rcases (by omega : v < ((5*p+2)/3) ∨ (((5*p+2)/3) ≤ v ∧ v < (2*p)) ∨ (2*p+1) ≤ v) with hA | hB | hC
  · -- run 0
    exfalso; omega
  · -- run 1
    exfalso; omega
  · -- run 2
    exfalso; omega

noncomputable def cell {Fr : Frame} (T : TwoTermData Fr 3 2) {r p : ℕ} [Fact p.Prime] (h : Reg r p)
    (hn : Fr.norm = 1) (hnorm : Fr.norm ∈ S p) (hnorm0 : red p Fr.norm ≠ 0) : Cell3 cT cT_pos Fr 3 2 T r p :=
  cell3Gen T (win h) (hsq_T h.hlo (by have := h.hp60; omega)) hnorm hnorm0
    (ns0 T h (hsq_T h.hlo (by have := h.hp60; omega)) hnorm hnorm0)
    (kill T h hn (hsq_T h.hlo (by have := h.hp60; omega)) hnorm hnorm0)

theorem cell_bound {Fr : Frame} (T : TwoTermData Fr 3 2) {r p : ℕ} [Fact p.Prime] (h : Reg r p)
    (hn : Fr.norm = 1) (hnorm : Fr.norm ∈ S p) (hnorm0 : red p Fr.norm ≠ 0) :
    (cell T h hn hnorm hnorm0).bound = base3 ((3 * r + 9) / 20) r p (r) ((((5*p+2)/3)-1)) := by
  unfold cell; exact cell3Gen_bound T (win h) _ _ _ _ _

def T0 (r p : ℕ) : ℕ := r
def TV (r p : ℕ) : ℕ := (((5*p+2)/3)-1)

end F34

namespace F35

structure Reg (r p : ℕ) : Prop where
  hr : r % 2 = 0
  hp3 : p % 3 = 2
  hlo : 3 * r < 10 * p
  hhi : 10 * p ≤ 39 * r
  hp60 : 60 ≤ p
  hM1 : 1 * p < r
  hM2 : r ≤ 2 * p
  hP1 : 2 * p + 2 < 3 * r
  hP2 : 3 * r ≤ 5 * p + 2
  hb1 : 3 * p + 2 ≤ 3 * r
  hb2 : 3 * r < 4 * p + 2
  hm0 : r < ((5*p+2)/3)
  hf1 : ((5*p+2)/3) < (r + 2 * ((3 * r + 9) / 20))
  hf2 : (r + 2 * ((3 * r + 9) / 20)) ≤ (2*p+1)
  hc1 : base3 ((3 * r + 9) / 20) r p r (((5*p+2)/3)-1) ≤ base3 ((3 * r + 9) / 20) r p ((5*p+2)/3) ((2*p)-1)

theorem win {r p : ℕ} (h : Reg r p) :
    Win3 cT cT_pos 3 2 r p (r + p) (r) ((((5*p+2)/3)-1)) ((3 * r + 9) / 20) := by
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
  have hnd : ¬ p ∣ r := notdvd_between (a := 1) (by omega) (by omega)
  exact
    { hr2 := hr, hr0 := by omega, hbs := hm, hrN := by omega, hNp := hNp_T hlo (by omega), hpm := by omega,
      hp2 := by omega, hq0 := by norm_num, hqp := by omega, ho0 := by norm_num, hop := by omega, hqo := by norm_num,
      ht0r := by omega, ht0b := by omega, ht0tv := by omega, htvp := by omega, htvN := by omega,
      hdiv := div_both (x := 1) (by omega) (by omega) (by omega) (by omega), hnt0 := hnd }

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
  exact notdvd_between (a := 1) (by omega) (by omega)

theorem ns0 {Fr : Frame} (T : TwoTermData Fr 3 2) {r p : ℕ} [Fact p.Prime] (h : Reg r p)
    (hsq : ∀ t, 1 ≤ t → t < r + p → ¬ p ^ 2 ∣ 3 * t - 2) (hnorm : Fr.norm ∈ S p) (hnorm0 : red p Fr.norm ≠ 0) :
    NoSingWin (twoTermPoleData T (hNp_T h.hlo (by have := h.hp60; omega)).le hsq hnorm hnorm0) (r) (((((5*p+2)/3)-1)) - (r)) := by
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
  exact notdvd_between (a := 1) (by omega) (by omega)

theorem nd1 {r p : ℕ} (h : Reg r p) : ¬ p ∣ ((5*p+2)/3) := by
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
  exact notdvd_pole (j := 5) (by omega) (by omega)

theorem ns1 {Fr : Frame} (T : TwoTermData Fr 3 2) {r p : ℕ} [Fact p.Prime] (h : Reg r p)
    (hsq : ∀ t, 1 ≤ t → t < r + p → ¬ p ^ 2 ∣ 3 * t - 2) (hnorm : Fr.norm ∈ S p) (hnorm0 : red p Fr.norm ≠ 0) :
    NoSingWin (twoTermPoleData T (hNp_T h.hlo (by have := h.hp60; omega)).le hsq hnorm hnorm0) (((5*p+2)/3)) ((((2*p)-1)) - (((5*p+2)/3))) := by
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
  exact notdvd_between (a := 1) (by omega) (by omega)

theorem kill {Fr : Frame} (T : TwoTermData Fr 3 2) {r p : ℕ} [Fact p.Prime] (h : Reg r p) (hn : Fr.norm = 1)
    (hsq : ∀ t, 1 ≤ t → t < r + p → ¬ p ^ 2 ∣ 3 * t - 2) (hnorm : Fr.norm ∈ S p) (hnorm0 : red p Fr.norm ≠ 0) :
    ∀ v, r ≤ v → v < r + 2 * ((3 * r + 9) / 20) → (v < (r) ∨ ((((5*p+2)/3)-1)) < v) → ¬ p ∣ v →
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
  have hnv : v ≠ 2 * p := fun e => h4 ⟨2, by rw [e]; ring⟩
  rcases (by omega : v < ((5*p+2)/3) ∨ (((5*p+2)/3) ≤ v ∧ v < (2*p)) ∨ (2*p+1) ≤ v) with hA | hB | hC
  · -- run 0
    exfalso; omega
  · -- run 1
    exact kill_of_pair T (win h) hsq hnorm hnorm0 (((5*p+2)/3)) v 1 3 1 5
      (by omega) (by omega) (by omega) (nd1 h) (by omega) (by omega)
      (div_both (x := 1) (by omega) (by omega) (by omega) (by omega))
      (nosing_mono (ns1 T h hsq hnorm hnorm0) (by omega))
      (Nat.div_eq_of_lt_le (by omega) (by omega)) (Nat.div_eq_of_lt_le (by omega) (by omega))
      (Nat.div_eq_of_lt_le (by omega) (by omega)) (Nat.div_eq_of_lt_le (by omega) (by omega))
      (pair_2_1_3_1_5 hp3 hp60 hn)
  · -- run 2
    exfalso; omega

noncomputable def cell {Fr : Frame} (T : TwoTermData Fr 3 2) {r p : ℕ} [Fact p.Prime] (h : Reg r p)
    (hn : Fr.norm = 1) (hnorm : Fr.norm ∈ S p) (hnorm0 : red p Fr.norm ≠ 0) : Cell3 cT cT_pos Fr 3 2 T r p :=
  cell3Gen T (win h) (hsq_T h.hlo (by have := h.hp60; omega)) hnorm hnorm0
    (ns0 T h (hsq_T h.hlo (by have := h.hp60; omega)) hnorm hnorm0)
    (kill T h hn (hsq_T h.hlo (by have := h.hp60; omega)) hnorm hnorm0)

theorem cell_bound {Fr : Frame} (T : TwoTermData Fr 3 2) {r p : ℕ} [Fact p.Prime] (h : Reg r p)
    (hn : Fr.norm = 1) (hnorm : Fr.norm ∈ S p) (hnorm0 : red p Fr.norm ≠ 0) :
    (cell T h hn hnorm hnorm0).bound = base3 ((3 * r + 9) / 20) r p (r) ((((5*p+2)/3)-1)) := by
  unfold cell; exact cell3Gen_bound T (win h) _ _ _ _ _

def T0 (r p : ℕ) : ℕ := r
def TV (r p : ℕ) : ℕ := (((5*p+2)/3)-1)

end F35

end CatalanCore.Uniform.Content.UFFamily3
