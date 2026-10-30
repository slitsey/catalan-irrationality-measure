module

public import CatalanCore.Uniform.Content.RankProducer.Build
public import CatalanCore.Uniform.Content.RankProducer.LineWitness

@[expose] public section
set_option Elab.async false
namespace CatalanCore.Uniform.Content.RankProducer
open Module CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.Hybrid
open CatalanCore.Uniform.Content.Member
open scoped Classical
variable (p : ℕ) [Fact p.Prime]

noncomputable def lineMc (c : FibreCert) (w : RatFunc (ZMod p) × RatFunc (ZMod p)) : ℕ :=
  if ∃ d ∈ c.kc, castV p (c.cload d) ≠ 0 ∧
      castV p (c.cload d) ∈ Submodule.span (RatFunc (ZMod p)) {w} then 1 else 0

noncomputable def lineMr (c : FibreCert) (w : RatFunc (ZMod p) × RatFunc (ZMod p)) : ℕ :=
  if ∀ d ∈ c.kr, omegaL (castV p (c.rload d)) w = 0 then 1 else 0

theorem lineMc_le_one (c : FibreCert) (w : RatFunc (ZMod p) × RatFunc (ZMod p)) :
    lineMc p c w ≤ 1 := by unfold lineMc; split_ifs <;> omega

theorem lineMr_le_one (c : FibreCert) (w : RatFunc (ZMod p) × RatFunc (ZMod p)) :
    lineMr p c w ≤ 1 := by unfold lineMr; split_ifs <;> omega

theorem lineMc_intersection (c : FibreCert) (w : RatFunc (ZMod p) × RatFunc (ZMod p))
    (hw : w ≠ 0) : lineMc p c w ≤ finrank (RatFunc (ZMod p))
      ↥(Submodule.span (RatFunc (ZMod p)) {w} ⊓ Ucol p c) := by
  unfold lineMc
  split_ifs with h
  · obtain ⟨d, hd, hn, hm⟩ := h
    exact one_le_col_intersection p c _ d hd hn hm
  · exact Nat.zero_le _

theorem lineMr_intersection (c : FibreCert) (w : RatFunc (ZMod p) × RatFunc (ZMod p))
    (hw : w ≠ 0) : lineMr p c w ≤ finrank (RatFunc (ZMod p))
      ↥(Submodule.span (RatFunc (ZMod p)) {w} ⊓ Urow p c) := by
  unfold lineMr
  split_ifs with h
  · exact one_le_row_intersection p c _ w hw (Submodule.subset_span (by simp)) h
  · exact Nat.zero_le _

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
noncomputable def RankMember.ofLine (Fr : Frame) (u q : Fin Fr.d → ℕ) (common : ι → ℕ)
    (xs ys : κ → ℕ) (T : Finset ι) (p : ℕ) [Fact p.Prime] (B : ℕ)
    (hcoef : ∀ j, (frameDigamma Fr u q).c j ∈ S p) (hpq : ∀ j, ¬ p ∣ (frameDigamma Fr u q).q j)
    (hp3 : 3 ≤ p) (hbd : ∀ j, (frameDigamma Fr u q).q j * B + (frameDigamma Fr u q).u j ≤ p ^ 2)
    (hB : B < p ^ 2) (ha : ∀ i, memberRows common xs T i ≤ B)
    (hb : ∀ j, memberCols common ys T j ≤ B)
    (hia : Function.Injective (memberRows common xs T))
    (hib : Function.Injective (memberCols common ys T))
    (cert : ZMod p → FibreCert) (hOk : ∀ x, (cert x).Ok) (hInt : ∀ x, (cert x).Integral p)
    (hReal : ∀ x, Realizes ((frameDigamma Fr u q).poleSplit B hcoef hpq hp3 hbd)
      (memberRows common xs T) (memberCols common ys T) x (cert x))
    (hcard : (killRows (p := p) (memberRows common xs T) cert).card =
      (killCols (p := p) (memberCols common ys T) cert).card)
    (w : RatFunc (ZMod p) × RatFunc (ZMod p)) (hw : w ≠ 0) :
    RankMember Fr u q common xs ys T p where
  B := B
  hcoef := hcoef
  hpq := hpq
  hp3 := hp3
  hbd := hbd
  hB := hB
  ha := ha
  hb := hb
  hia := hia
  hib := hib
  cert := cert
  hOk := hOk
  hInt := hInt
  hReal := hReal
  hcard := hcard
  Vs := Submodule.span (RatFunc (ZMod p)) {w}
  mc := fun x => lineMc p (cert x) w
  mr := fun x => lineMr p (cert x) w
  hmc2 := fun x => by
    rw [finrank_span_singleton hw]
    exact lineMc_le_one p (cert x) w
  hmr2 := fun x => by
    rw [finrank_span_singleton hw]
    exact lineMr_le_one p (cert x) w
  hmc := fun x _ => lineMc_intersection p (cert x) w hw
  hmr := fun x _ => lineMr_intersection p (cert x) w hw

#print axioms RankMember.ofLine
end CatalanCore.Uniform.Content.RankProducer
