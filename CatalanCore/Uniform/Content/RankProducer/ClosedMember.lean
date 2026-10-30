module

public import CatalanCore.Uniform.Content.RankProducer.ClosedAssign

@[expose] public section
set_option Elab.async false

/-! # The closed rank member of one line class (Theorem R, lane C2L)

`closed_member`: for an assignment `Assign` of untouched fibres and a line class `l` whose reduced
moment is nonzero, a `RankMember` with

  `price + max(|RA| + |SQ|, |RA_l| + |CA_l| + 2 [l = D0] |SQ|) ≤ 2 (|T| + m)`.

The certificates are `closedCert`; `w` is the class moment; the bound is `price_line_bound`, with
the scores counted by `card_filter_le_score`, `lineMc_eq_one_of_mem`, `lineMr_eq_one_of_single`.
-/

namespace CatalanCore.Uniform.Content.RankProducer
open Finset Module CatalanCore CatalanCore.Basic CatalanCore.Uniform CatalanCore.Uniform.Content.Hybrid
  CatalanCore.Uniform.Content.Member CatalanCore.Uniform.Content.Wire
open scoped Classical

theorem omegaL_self {K : Type*} [Field K] (v : K × K) : omegaL v v = 0 := by
  rw [omegaL_apply]; ring

section Eval
variable {p : ℕ} [hp : Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι] {B : ℕ} {f e : ℕ → ℚ}
  (PS : PoleSplit p B f e) (a b : ι → ℕ) {G : BlockGeom} {r m ρ : ℕ}
  {T : Finset (G.geometry r).C} (Lz Ez : Bool → ℕ → ℚ) {RA CA SQ : Finset ℕ}

theorem val_mod_cast (n : ℕ) : (((n % p : ℕ) : ZMod p)).val = n % p := by
  rw [ZMod.val_natCast, Nat.mod_mod]

theorem closedCert_of_RA (hA : Assign r m p ρ T RA CA SQ) (hpm : 2 * m < p) {t : ℕ}
    (ht : t ∈ RA) :
    closedCert PS a b r ρ Lz Ez RA CA SQ ((t % p : ℕ) : ZMod p) =
      clsRow Lz Ez (t / p) (decide (ρ ≤ t % p)) := by
  have hp0 := hp.out.pos
  obtain ⟨t1, t2, -⟩ := hA.hRA t ht
  have hmem : t % p ∈ RA.image (· % p) := Finset.mem_image_of_mem (· % p) ht
  unfold closedCert
  rw [val_mod_cast, if_pos hmem, kOf_eq hp0 t1 (by omega)]

theorem closedCert_of_CA (hA : Assign r m p ρ T RA CA SQ) (hpm : 2 * m < p) {t : ℕ}
    (ht : t ∈ CA) :
    closedCert PS a b r ρ Lz Ez RA CA SQ ((t % p : ℕ) : ZMod p) =
      clsCol Lz Ez (t / p) (decide (ρ ≤ t % p)) := by
  have hp0 := hp.out.pos
  obtain ⟨t1, t2, t3, -⟩ := hA.hCA t ht
  have hinj := assign_inj hA hpm
  have hmem : t % p ∈ CA.image (· % p) := Finset.mem_image_of_mem (· % p) ht
  have hnot : t % p ∉ RA.image (· % p) := by
    intro h
    obtain ⟨s, hs, hst⟩ := Finset.mem_image.1 h
    have hst' : s % p = t % p := hst
    have := hinj s (by simp [hs]) t (by simp [ht]) hst'
    subst this
    have := (hA.hRA s hs).2.2.1
    omega
  unfold closedCert
  rw [val_mod_cast, if_neg hnot, if_pos hmem, kOf_eq hp0 t1 (by omega)]

theorem closedCert_of_SQ (hA : Assign r m p ρ T RA CA SQ) (hpm : 2 * m < p) {x0 : ℕ}
    (hx : x0 ∈ SQ) :
    closedCert PS a b r ρ Lz Ez RA CA SQ ((x0 % p : ℕ) : ZMod p) =
      sqCert (Lz false) (Ez false) := by
  obtain ⟨s1, s2, s3, -⟩ := hA.hSQ x0 hx
  have hinj := assign_inj hA hpm
  have hmod : x0 % p = x0 := Nat.mod_eq_of_lt (by have := hA.hρp; omega)
  have hnR : x0 ∉ RA.image (· % p) := by
    intro h
    obtain ⟨s, hs, hst⟩ := Finset.mem_image.1 h
    have hst' : s % p = x0 % p := by rw [hmod]; exact hst
    have := hinj s (by simp [hs]) x0 (by simp [hx]) hst'
    subst this
    have := (hA.hRA s hs).1
    omega
  have hnC : x0 ∉ CA.image (· % p) := by
    intro h
    obtain ⟨s, hs, hst⟩ := Finset.mem_image.1 h
    have hst' : s % p = x0 % p := by rw [hmod]; exact hst
    have := hinj s (by simp [hs]) x0 (by simp [hx]) hst'
    subst this
    have := (hA.hCA s hs).1
    omega
  have hz : decide (ρ ≤ x0) = false := decide_eq_false (by omega)
  unfold closedCert
  rw [val_mod_cast, hmod, if_neg hnR, if_neg hnC, if_pos hx, hz]

end Eval

section Facts
variable {p : ℕ} [hp : Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι] {B : ℕ} {f e : ℕ → ℚ}
  (PS : PoleSplit p B f e) (a b : ι → ℕ) {G : BlockGeom} {r m ρ : ℕ}
  {T : Finset (G.geometry r).C} (Lz Ez : Bool → ℕ → ℚ) {RA CA SQ : Finset ℕ}

theorem closedCert_ok (hA : Assign r m p ρ T RA CA SQ) (hpm : 2 * m < p) (hE0 : Ez false 0 = 0)
    (x : ZMod p) : (closedCert PS a b r ρ Lz Ez RA CA SQ x).Ok := by
  have hE0' : ∀ (kk : ℕ) (z : Bool), kk ≤ 1 ∧ z = false → Ez z 0 = 0 :=
    fun _ _ h => by rw [h.2]; exact hE0
  rcases closedCert_cases PS a b Lz Ez hA hpm x with
    ⟨t, -, -, hc⟩ | ⟨t, -, -, hc⟩ | ⟨x0, -, -, hc⟩ | hc <;> rw [hc]
  · exact bordRow_ok (clsIdx_mem _ _ _ _) (clsVec_idx _ _ _ _) (clsVec_ker _ _ _ _ (hE0' _ _))
  · exact bordCol_ok (clsIdx_mem _ _ _ _) (clsVec_idx _ _ _ _) (clsVec_ker _ _ _ _ (hE0' _ _))
  · exact sqCert_ok hE0
  · exact FibreCert.triv_ok _ _ _ _

theorem closedCert_int (hA : Assign r m p ρ T RA CA SQ) (hpm : 2 * m < p)
    (hBnd : ∀ (kk : ℕ) (z : Bool), kk ≤ (r + 2 * m) / p → clsBnd (Lz z) (Ez z) kk z < p)
    (x : ZMod p) : (closedCert PS a b r ρ Lz Ez RA CA SQ x).Integral p := by
  rcases closedCert_cases PS a b Lz Ez hA hpm x with
    ⟨t, ht, -, hc⟩ | ⟨t, ht, -, hc⟩ | ⟨x0, -, -, hc⟩ | hc <;> rw [hc]
  · have h2 := (hA.hRA t ht).2.1
    exact bordRow_integral (clsVec_mem _ _ _ _ (hBnd _ _ (Nat.div_le_div_right h2.le)))
  · have h2 := (hA.hCA t ht).2.1
    exact bordCol_integral (clsVec_mem _ _ _ _ (hBnd _ _ (Nat.div_le_div_right h2.le)))
  · exact sqCert_integral
  · exact FibreCert.triv_integral _ _ _ _

theorem closedCert_kr_le (hA : Assign r m p ρ T RA CA SQ) (hpm : 2 * m < p) (x : ZMod p) :
    (closedCert PS a b r ρ Lz Ez RA CA SQ x).kr.card ≤ 1 := by
  rcases closedCert_cases PS a b Lz Ez hA hpm x with
    ⟨t, -, -, hc⟩ | ⟨t, -, -, hc⟩ | ⟨x0, -, -, hc⟩ | hc <;> rw [hc] <;>
    simp [clsRow, clsCol, bordRow, bordCol, sqCert, trivCert, FibreCert.triv]

theorem closedCert_kc_le (hA : Assign r m p ρ T RA CA SQ) (hpm : 2 * m < p) (x : ZMod p) :
    (closedCert PS a b r ρ Lz Ez RA CA SQ x).kc.card ≤ 1 := by
  rcases closedCert_cases PS a b Lz Ez hA hpm x with
    ⟨t, -, -, hc⟩ | ⟨t, -, -, hc⟩ | ⟨x0, -, -, hc⟩ | hc <;> rw [hc] <;>
    simp [clsRow, clsCol, bordRow, bordCol, sqCert, trivCert, FibreCert.triv]

end Facts

theorem closedCert_real {G : BlockGeom} {r : ℕ} (hs : HybShape G r) (T : Finset (G.geometry r).C)
    {p : ℕ} [hp : Fact p.Prime] {B : ℕ} {f e : ℕ → ℚ} (PS : PoleSplit p B f e)
    (Lz Ez : Bool → ℕ → ℚ) {ρ : ℕ} (hρp : ρ < p) {RA CA SQ : Finset ℕ}
    (hA : Assign r (G.geometry r).k p ρ T RA CA SQ) (hpm : 2 * (G.geometry r).k < p)
    (hLf : ∀ x0 < p, ∀ d, PS.Lf (x0 + p * d) = Lz (decide (ρ ≤ x0)) d)
    (hEf : ∀ x0 < p, ∀ d, PS.E (x0 + p * d) = Ez (decide (ρ ≤ x0)) d) (x : ZMod p) :
    Realizes PS (rowsM T) (colsM T) x
      (closedCert PS (rowsM T) (colsM T) r ρ Lz Ez RA CA SQ x) := by
  have hp0 := hp.out.pos
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  rcases closedCert_cases PS (rowsM T) (colsM T) Lz Ez hA hpm x with
    ⟨t, ht, hxv, hc⟩ | ⟨t, ht, hxv, hc⟩ | ⟨x0, hx0, hxv, hc⟩ | hc <;> rw [hc]
  · obtain ⟨t1, t2, t3, t4⟩ := hA.hRA t ht
    have hx : x = ((t % p : ℕ) : ZMod p) := by rw [← hxv, ZMod.natCast_zmod_val]
    rw [hx]
    exact real_row hs T PS t t1 t2 t3 hpm t4 _ _ (fun d => hLf _ (Nat.mod_lt t hp0) d)
      (fun d => hEf _ (Nat.mod_lt t hp0) d) _ _
  · obtain ⟨t1, t2, t3, t4⟩ := hA.hCA t ht
    have hx : x = ((t % p : ℕ) : ZMod p) := by rw [← hxv, ZMod.natCast_zmod_val]
    rw [hx]
    exact real_col hs T PS t t1 t2 t3 hpm t4 _ _ (fun d => hLf _ (Nat.mod_lt t hp0) d)
      (fun d => hEf _ (Nat.mod_lt t hp0) d) _ _
  · obtain ⟨s1, s2, s3, s4⟩ := hA.hSQ x0 hx0
    have hx : x = ((x0 : ℕ) : ZMod p) := by rw [← hxv, ZMod.natCast_zmod_val]
    have hz : decide (ρ ≤ x0) = false := decide_eq_false (by omega)
    rw [hx]
    refine real_sq hs T PS x0 (by omega) s1 s2 s4 _ _ (fun d => ?_) (fun d => ?_)
    · rw [hLf x0 (by omega) d, hz]
    · rw [hEf x0 (by omega) d, hz]
  · exact trivCert_realizes PS _ _ x

/-- Kill balance of the assignment. -/
theorem closedCert_hcard {G : BlockGeom} {r : ℕ} (hs : HybShape G r) (T : Finset (G.geometry r).C)
    {p : ℕ} [hp : Fact p.Prime] {B : ℕ} {f e : ℕ → ℚ} (PS : PoleSplit p B f e)
    (Lz Ez : Bool → ℕ → ℚ) {ρ : ℕ} (hρp : ρ < p) {RA CA SQ : Finset ℕ}
    (hA : Assign r (G.geometry r).k p ρ T RA CA SQ) (hpm : 2 * (G.geometry r).k < p)
    (hE0 : Ez false 0 = 0)
    (hLf : ∀ x0 < p, ∀ d, PS.Lf (x0 + p * d) = Lz (decide (ρ ≤ x0)) d)
    (hEf : ∀ x0 < p, ∀ d, PS.E (x0 + p * d) = Ez (decide (ρ ≤ x0)) d) :
    (killRows (p := p) (rowsM T) (closedCert PS (rowsM T) (colsM T) r ρ Lz Ez RA CA SQ)).card =
        RA.card + SQ.card ∧
      (killCols (p := p) (colsM T) (closedCert PS (rowsM T) (colsM T) r ρ Lz Ez RA CA SQ)).card =
        CA.card + SQ.card := by
  have hp0 := hp.out.pos
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hinj := assign_inj hA hpm
  have hOk := closedCert_ok PS (rowsM T) (colsM T) Lz Ez hA hpm hE0
  have hReal := closedCert_real hs T PS Lz Ez hρp hA hpm hLf hEf
  have hSQp : ∀ x0 ∈ SQ, x0 < p := fun x0 hx => by
    have := (hA.hSQ x0 hx).2.2.1; omega
  have hRAc : (RA.image (· % p)).card = RA.card := by
    refine Finset.card_image_of_injOn ?_
    intro s hs t ht hst
    exact hinj s (by simp [Finset.mem_coe.1 hs]) t (by simp [Finset.mem_coe.1 ht]) hst
  have hCAc : (CA.image (· % p)).card = CA.card := by
    refine Finset.card_image_of_injOn ?_
    intro s hs t ht hst
    exact hinj s (by simp [Finset.mem_coe.1 hs]) t (by simp [Finset.mem_coe.1 ht]) hst
  have hRlt : ∀ y ∈ RA.image (· % p), y < p := fun y hy => by
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 hy; exact Nat.mod_lt t hp0
  have hClt : ∀ y ∈ CA.image (· % p), y < p := fun y hy => by
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 hy; exact Nat.mod_lt t hp0
  constructor
  · rw [killRows_card_eq_sum PS (rowsM T) (colsM T) (rowsM_inj hs T) _ hOk hReal]
    simp only [closedCert_kr_card PS (rowsM T) (colsM T) Lz Ez hA hpm]
    rw [Finset.sum_add_distrib, sum_val_ind _ hRlt, sum_val_ind _ hSQp, hRAc]
  · rw [killCols_card_eq_sum PS (rowsM T) (colsM T) (colsM_inj hs T) _ hOk hReal]
    simp only [closedCert_kc_card PS (rowsM T) (colsM T) Lz Ez hA hpm]
    rw [Finset.sum_add_distrib, sum_val_ind _ hClt, sum_val_ind _ hSQp, hCAc]

section Scores
variable {p : ℕ} [hp : Fact p.Prime] (Lz Ez : Bool → ℕ → ℚ)

theorem lineMc_clsCol (l : LineCls) (k : ℕ) (z : Bool) (hP : inCls l k z)
    (hl : castV p (clsMomL Lz Ez l) ≠ 0) :
    lineMc p (clsCol Lz Ez k z) (castV p (clsMomL Lz Ez l)) = 1 := by
  have hcl : (clsCol Lz Ez k z).cload (clsIdx (Lz z) (Ez z) k z) = clsMomL Lz Ez l := by
    rw [clsCol, bordCol_cload, mom_cls_of_inCls Lz Ez l k z hP]
  exact lineMc_eq_one_of_mem _ _ (clsIdx (Lz z) (Ez z) k z) (by simp [clsCol, bordCol])
    (by rw [hcl]; exact hl) (by rw [hcl]; exact Submodule.mem_span_singleton_self _)

theorem lineMr_clsRow (l : LineCls) (k : ℕ) (z : Bool) (hP : inCls l k z) :
    lineMr p (clsRow Lz Ez k z) (castV p (clsMomL Lz Ez l)) = 1 := by
  have hrl : (clsRow Lz Ez k z).rload (clsIdx (Lz z) (Ez z) k z) = clsMomL Lz Ez l := by
    rw [clsRow, bordRow_rload, mom_cls_of_inCls Lz Ez l k z hP]
  exact lineMr_eq_one_of_single _ _ (by simp [clsRow, bordRow]) (clsIdx (Lz z) (Ez z) k z)
    (by simp [clsRow, bordRow]) (by rw [hrl]; exact omegaL_self _)

theorem lineMc_sq (hl : castV p (clsMomL Lz Ez none) ≠ 0) :
    lineMc p (sqCert (Lz false) (Ez false)) (castV p (clsMomL Lz Ez none)) = 1 := by
  have hcl : (sqCert (Lz false) (Ez false)).cload 0 = clsMomL Lz Ez none := sqCert_cload
  exact lineMc_eq_one_of_mem _ _ 0 (by simp [sqCert]) (by rw [hcl]; exact hl)
    (by rw [hcl]; exact Submodule.mem_span_singleton_self _)

theorem lineMr_sq :
    lineMr p (sqCert (Lz false) (Ez false)) (castV p (clsMomL Lz Ez none)) = 1 := by
  have hrl : (sqCert (Lz false) (Ez false)).rload 0 = clsMomL Lz Ez none := sqCert_rload
  exact lineMr_eq_one_of_single _ _ (by simp [sqCert]) 0 (by simp [sqCert])
    (by rw [hrl]; exact omegaL_self _)

end Scores

set_option maxHeartbeats 1600000 in
/-- **The closed rank member of a line class.** -/
theorem closed_member {G : BlockGeom} {r : ℕ} (hs : HybShape G r) (T : Finset (G.geometry r).C)
    (Fr : Frame) (u q : Fin Fr.d → ℕ) (p : ℕ) [hp : Fact p.Prime] (B : ℕ)
    (hcoef : ∀ j, (frameDigamma Fr u q).c j ∈ S p) (hpq : ∀ j, ¬ p ∣ (frameDigamma Fr u q).q j)
    (hp3 : 3 ≤ p)
    (hbd : ∀ j, (frameDigamma Fr u q).q j * B + (frameDigamma Fr u q).u j ≤ p ^ 2)
    (hB : B < p ^ 2) (hBr : r + 2 * (G.geometry r).k ≤ B + 1)
    (hpm : 2 * (G.geometry r).k < p) (Lz Ez : Bool → ℕ → ℚ) (ρ : ℕ)
    (hLf : ∀ x0 < p, ∀ d, (frameDigamma Fr u q).Lf p (x0 + p * d) = Lz (decide (ρ ≤ x0)) d)
    (hEf : ∀ x0 < p, ∀ d, (frameDigamma Fr u q).E p (x0 + p * d) = Ez (decide (ρ ≤ x0)) d)
    (hE0 : Ez false 0 = 0)
    (hBnd : ∀ (kk : ℕ) (z : Bool), kk ≤ (r + 2 * (G.geometry r).k) / p →
      clsBnd (Lz z) (Ez z) kk z < p)
    (RA CA SQ : Finset ℕ) (hA : Assign r (G.geometry r).k p ρ T RA CA SQ)
    (l : LineCls) (hl : castV p (clsMomL Lz Ez l) ≠ 0) :
    ∃ M : RankMember Fr u q (fun a : (G.geometry r).C => (a : ℕ)) (G.geometry r).xs
        (G.geometry r).ys T p,
      M.price + max (RA.card + SQ.card)
        ((RA.filter (fun t => inCls l (t / p) (decide (ρ ≤ t % p)))).card +
          (CA.filter (fun t => inCls l (t / p) (decide (ρ ≤ t % p)))).card +
          2 * (if l = none then SQ.card else 0)) ≤ 2 * (T.card + (G.geometry r).k) := by
  have hp0 := hp.out.pos
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hρp := hA.hρp
  have ha : ∀ i, rowsM T i ≤ B := fun i => by have := rowsM_lt hs T i; omega
  have hb : ∀ j, colsM T j ≤ B := fun j => by have := colsM_lt hs T j; omega
  have hinj := assign_inj hA hpm
  have hOk := closedCert_ok ((frameDigamma Fr u q).poleSplit B hcoef hpq hp3 hbd) (rowsM T)
    (colsM T) Lz Ez hA hpm hE0
  have hInt := closedCert_int ((frameDigamma Fr u q).poleSplit B hcoef hpq hp3 hbd) (rowsM T)
    (colsM T) Lz Ez hA hpm hBnd
  have hReal := closedCert_real hs T ((frameDigamma Fr u q).poleSplit B hcoef hpq hp3 hbd) Lz Ez
    hρp hA hpm hLf hEf
  obtain ⟨hKR, hKC⟩ := closedCert_hcard hs T ((frameDigamma Fr u q).poleSplit B hcoef hpq hp3 hbd)
    Lz Ez hρp hA hpm hE0 hLf hEf
  have hcard : (killRows (p := p) (rowsM T) (closedCert
      ((frameDigamma Fr u q).poleSplit B hcoef hpq hp3 hbd) (rowsM T) (colsM T) r ρ Lz Ez RA CA SQ)).card =
      (killCols (p := p) (colsM T) (closedCert
      ((frameDigamma Fr u q).poleSplit B hcoef hpq hp3 hbd) (rowsM T) (colsM T) r ρ Lz Ez RA CA SQ)).card := by
    rw [hKR, hKC, hA.hcard]
  refine ⟨RankMember.ofLine Fr u q (fun a : (G.geometry r).C => (a : ℕ)) (G.geometry r).xs
    (G.geometry r).ys T p B hcoef hpq hp3 hbd hB ha hb (rowsM_inj hs T) (colsM_inj hs T) _ hOk hInt
    hReal hcard (castV p (clsMomL Lz Ez l)) hl, ?_⟩
  have hline := RankMember.price_line_bound (RankMember.ofLine Fr u q
    (fun a : (G.geometry r).C => (a : ℕ)) (G.geometry r).xs
    (G.geometry r).ys T p B hcoef hpq hp3 hbd hB ha hb (rowsM_inj hs T) (colsM_inj hs T) _ hOk hInt
    hReal hcard (castV p (clsMomL Lz Ez l)) hl) (finrank_span_singleton hl)
    (closedCert_kr_le _ _ _ Lz Ez hA hpm) (closedCert_kc_le _ _ _ Lz Ez hA hpm)
  have hgInj : ∀ A : Finset ℕ, A ⊆ RA ∪ CA ∪ SQ →
      Set.InjOn (fun n : ℕ => ((n % p : ℕ) : ZMod p)) (A : Set ℕ) := by
    intro A hAs n hn n' hn' h
    have h' : n % p % p = n' % p % p := (ZMod.natCast_eq_natCast_iff' _ _ p).1 h
    rw [Nat.mod_mod, Nat.mod_mod] at h'
    exact hinj n (hAs hn) n' (hAs hn') h'
  have hSQl_sub : (if l = none then SQ else ∅) ⊆ SQ := by split_ifs <;> simp
  have hSQl_none : ∀ x ∈ (if l = none then SQ else ∅), l = none := by
    intro x hx
    split_ifs at hx with h
    · exact h
    · simp at hx
  -- column scores
  have hcolS := card_filter_le_score
    ((CA.filter (fun t => inCls l (t / p) (decide (ρ ≤ t % p)))) ∪ (if l = none then SQ else ∅))
    (colFib ((frameDigamma Fr u q).poleSplit B hcoef hpq hp3 hbd) (rowsM T) (colsM T)
      (digitHyp_of_lt ha hb hB) (rowsM_inj hs T) (colsM_inj hs T) _ hOk hInt hReal hcard)
    (fun n : ℕ => ((n % p : ℕ) : ZMod p)) (fun _ => True)
    (fun x => lineMc p (closedCert ((frameDigamma Fr u q).poleSplit B hcoef hpq hp3 hbd)
      (rowsM T) (colsM T) r ρ Lz Ez RA CA SQ x) (castV p (clsMomL Lz Ez l)))
    (hgInj _ (by
      intro n hn
      rcases Finset.mem_union.1 hn with h | h
      · simp [(Finset.mem_filter.1 h).1]
      · simp [hSQl_sub h]))
    (by
      intro n hn
      rcases Finset.mem_union.1 hn with h | h
      · have hnC := (Finset.mem_filter.1 h).1
        refine mem_colFib_of _ _ _ _ _ _ _ hOk hInt hReal hcard _
          (clsIdx (Lz (decide (ρ ≤ n % p))) (Ez (decide (ρ ≤ n % p))) (n / p)
            (decide (ρ ≤ n % p))) ?_
        rw [closedCert_of_CA _ _ _ Lz Ez hA hpm hnC]
        simp [clsCol, bordCol]
      · refine mem_colFib_of _ _ _ _ _ _ _ hOk hInt hReal hcard _ 0 ?_
        rw [closedCert_of_SQ _ _ _ Lz Ez hA hpm (hSQl_sub h)]
        simp [sqCert])
    (by
      intro n hn _
      rcases Finset.mem_union.1 hn with h | h
      · have hnC := (Finset.mem_filter.1 h).1
        have hPn : inCls l (n / p) (decide (ρ ≤ n % p)) := (Finset.mem_filter.1 h).2
        show 1 ≤ lineMc p (closedCert _ _ _ r ρ Lz Ez RA CA SQ ((n % p : ℕ) : ZMod p)) _
        rw [closedCert_of_CA _ _ _ Lz Ez hA hpm hnC]
        exact (lineMc_clsCol Lz Ez l _ _ hPn hl).ge
      · have hl0 := hSQl_none n h
        show 1 ≤ lineMc p (closedCert _ _ _ r ρ Lz Ez RA CA SQ ((n % p : ℕ) : ZMod p)) _
        rw [closedCert_of_SQ _ _ _ Lz Ez hA hpm (hSQl_sub h)]
        subst hl0
        exact (lineMc_sq Lz Ez hl).ge)
  -- row scores
  have hrowS := card_filter_le_score
    ((RA.filter (fun t => inCls l (t / p) (decide (ρ ≤ t % p)))) ∪ (if l = none then SQ else ∅))
    (rowFib ((frameDigamma Fr u q).poleSplit B hcoef hpq hp3 hbd) (rowsM T) (colsM T)
      (digitHyp_of_lt ha hb hB) (rowsM_inj hs T) (colsM_inj hs T) _ hOk hInt hReal hcard)
    (fun n : ℕ => ((n % p : ℕ) : ZMod p)) (fun _ => True)
    (fun x => lineMr p (closedCert ((frameDigamma Fr u q).poleSplit B hcoef hpq hp3 hbd)
      (rowsM T) (colsM T) r ρ Lz Ez RA CA SQ x) (castV p (clsMomL Lz Ez l)))
    (hgInj _ (by
      intro n hn
      rcases Finset.mem_union.1 hn with h | h
      · simp [(Finset.mem_filter.1 h).1]
      · simp [hSQl_sub h]))
    (by
      intro n hn
      rcases Finset.mem_union.1 hn with h | h
      · have hnR := (Finset.mem_filter.1 h).1
        refine mem_rowFib_of _ _ _ _ _ _ _ hOk hInt hReal hcard _
          (clsIdx (Lz (decide (ρ ≤ n % p))) (Ez (decide (ρ ≤ n % p))) (n / p)
            (decide (ρ ≤ n % p))) ?_
        rw [closedCert_of_RA _ _ _ Lz Ez hA hpm hnR]
        simp [clsRow, bordRow]
      · refine mem_rowFib_of _ _ _ _ _ _ _ hOk hInt hReal hcard _ 0 ?_
        rw [closedCert_of_SQ _ _ _ Lz Ez hA hpm (hSQl_sub h)]
        simp [sqCert])
    (by
      intro n hn _
      rcases Finset.mem_union.1 hn with h | h
      · have hnR := (Finset.mem_filter.1 h).1
        have hPn : inCls l (n / p) (decide (ρ ≤ n % p)) := (Finset.mem_filter.1 h).2
        show 1 ≤ lineMr p (closedCert _ _ _ r ρ Lz Ez RA CA SQ ((n % p : ℕ) : ZMod p)) _
        rw [closedCert_of_RA _ _ _ Lz Ez hA hpm hnR]
        exact (lineMr_clsRow Lz Ez l _ _ hPn).ge
      · have hl0 := hSQl_none n h
        show 1 ≤ lineMr p (closedCert _ _ _ r ρ Lz Ez RA CA SQ ((n % p : ℕ) : ZMod p)) _
        rw [closedCert_of_SQ _ _ _ Lz Ez hA hpm (hSQl_sub h)]
        subst hl0
        exact (lineMr_sq Lz Ez).ge)
  simp only [Finset.filter_true] at hcolS hrowS
  -- cardinalities
  have hdC : Disjoint (CA.filter (fun t => inCls l (t / p) (decide (ρ ≤ t % p))))
      (if l = none then SQ else ∅) := by
    rw [Finset.disjoint_left]
    intro n h1 h2
    have := (hA.hCA n (Finset.mem_filter.1 h1).1).1
    have := (hA.hSQ n (hSQl_sub h2)).1
    omega
  have hdR : Disjoint (RA.filter (fun t => inCls l (t / p) (decide (ρ ≤ t % p))))
      (if l = none then SQ else ∅) := by
    rw [Finset.disjoint_left]
    intro n h1 h2
    have := (hA.hRA n (Finset.mem_filter.1 h1).1).1
    have := (hA.hSQ n (hSQl_sub h2)).1
    omega
  rw [Finset.card_union_of_disjoint hdC] at hcolS
  rw [Finset.card_union_of_disjoint hdR] at hrowS
  have hSQc : (if l = none then SQ else ∅).card = if l = none then SQ.card else 0 := by
    split_ifs <;> simp
  have hTk : Fintype.card (T ⊕ Fin (G.geometry r).k) = T.card + (G.geometry r).k := by
    simp [Fintype.card_sum]
  rw [hSQc] at hcolS hrowS
  have hK : (RankMember.ofLine Fr u q (fun a : (G.geometry r).C => (a : ℕ)) (G.geometry r).xs
      (G.geometry r).ys T p B hcoef hpq hp3 hbd hB ha hb (rowsM_inj hs T) (colsM_inj hs T) _ hOk
      hInt hReal hcard (castV p (clsMomL Lz Ez l)) hl).killCount = RA.card + SQ.card := hKR
  have hC : (RankMember.ofLine Fr u q (fun a : (G.geometry r).C => (a : ℕ)) (G.geometry r).xs
      (G.geometry r).ys T p B hcoef hpq hp3 hbd hB ha hb (rowsM_inj hs T) (colsM_inj hs T) _ hOk
      hInt hReal hcard (castV p (clsMomL Lz Ez l)) hl).colScore =
      ∑ x ∈ colFib ((frameDigamma Fr u q).poleSplit B hcoef hpq hp3 hbd) (rowsM T) (colsM T)
        (digitHyp_of_lt ha hb hB) (rowsM_inj hs T) (colsM_inj hs T) _ hOk hInt hReal hcard,
        lineMc p (closedCert ((frameDigamma Fr u q).poleSplit B hcoef hpq hp3 hbd)
          (rowsM T) (colsM T) r ρ Lz Ez RA CA SQ x) (castV p (clsMomL Lz Ez l)) := rfl
  have hR : (RankMember.ofLine Fr u q (fun a : (G.geometry r).C => (a : ℕ)) (G.geometry r).xs
      (G.geometry r).ys T p B hcoef hpq hp3 hbd hB ha hb (rowsM_inj hs T) (colsM_inj hs T) _ hOk
      hInt hReal hcard (castV p (clsMomL Lz Ez l)) hl).rowScore =
      ∑ x ∈ rowFib ((frameDigamma Fr u q).poleSplit B hcoef hpq hp3 hbd) (rowsM T) (colsM T)
        (digitHyp_of_lt ha hb hB) (rowsM_inj hs T) (colsM_inj hs T) _ hOk hInt hReal hcard,
        lineMr p (closedCert ((frameDigamma Fr u q).poleSplit B hcoef hpq hp3 hbd)
          (rowsM T) (colsM T) r ρ Lz Ez RA CA SQ x) (castV p (clsMomL Lz Ez l)) := rfl
  rw [hTk, hK, hC, hR] at hline
  generalize (if l = none then SQ.card else 0) = s at hcolS hrowS ⊢
  omega

#print axioms closed_member
end CatalanCore.Uniform.Content.RankProducer
