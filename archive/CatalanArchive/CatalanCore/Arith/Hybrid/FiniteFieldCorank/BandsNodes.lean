module
public import CatalanArchive.CatalanCore.Arith.Hybrid.FiniteFieldCorank.BandsGeometry
public import CatalanArchive.CatalanCore.Linalg.CauchyPolynomial
@[expose] public section
open Finset Polynomial
namespace CatalanCore.Arith.Hybrid.FiniteFieldCorank
variable {ell K m S g : ℕ} [Fact ell.Prime]

lemma negNatNodes_injective (H : BandGeometry ell K m S g) :
    Function.Injective (fun a : Fin K => -(a.val : ZMod ell)) := by
  intro a b hab
  have hk := H.hK; have hs := H.hS; have hsg := H.hSg; have hr := H.room
  apply Fin.ext
  have h := congrArg ZMod.val (neg_injective hab)
  simpa only [ZMod.val_natCast_of_lt (show a.val < ell by omega),
    ZMod.val_natCast_of_lt (show b.val < ell by omega)] using h

lemma lowBand_eq_image_neg (H : BandGeometry ell K m S g) :
    lowBand ell K = Finset.univ.image (fun a : Fin K => -(a.val : ZMod ell)) := by
  have hk := H.hK; have hs := H.hS; have hsg := H.hSg; have hr := H.room
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    rw [lowBand_mem H]
    by_cases hz : a.val=0
    · left; simp [hz]
    · right
      have hv : (a.val : ZMod ell).val = a.val :=
        ZMod.val_natCast_of_lt (by omega)
      have hc : (a.val : ZMod ell) ≠ 0 := by
        intro h
        rw [h, ZMod.val_zero] at hv
        omega
      letI : NeZero (a.val : ZMod ell) := ⟨hc⟩
      rw [ZMod.val_neg_of_ne_zero, hv]
      omega
  · rw [card_lowBand H, card_image_of_injective _ (negNatNodes_injective H)]
    simp

lemma lowBand_rootProduct_eq_denom (H : BandGeometry ell K m S g) :
    rootProduct (lowBand ell K) =
      CatalanCore.Linalg.CauchyPolynomial.denom (fun a : Fin K => -(a.val : ZMod ell)) := by
  rw [lowBand_eq_image_neg H]
  unfold rootProduct CatalanCore.Linalg.CauchyPolynomial.denom Lagrange.nodal
  rw [Finset.prod_image]
  exact fun a ha b hb hab => negNatNodes_injective H hab

#print axioms lowBand_rootProduct_eq_denom



lemma band_nodeWeight_derivative (low : Fin K → ZMod ell) (a : Fin K) :
    CatalanCore.Linalg.CauchyPolynomial.nodeWeight low a =
      ((CatalanCore.Linalg.CauchyPolynomial.denom low).derivative.eval (low a))⁻¹ :=
  Lagrange.nodalWeight_eq_eval_derivative_nodal (Finset.mem_univ a)

/-- Split a consecutive product into its odd and even subsequences. -/
lemma prod_range_pairs {M : Type*} [CommMonoid M] (f : ℕ → M) (m : ℕ) :
    (∏ i ∈ range (2*m), f i) =
      (∏ i ∈ range m, f (2*i+1)) * (∏ i ∈ range m, f (2*i)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2*(m+1)=2*m+1+1 by omega, prod_range_succ, prod_range_succ, ih,
      prod_range_succ, prod_range_succ]
    ac_rfl

lemma borderBand_rootProduct_eq_interleaved (H : BandGeometry ell K m S g) :
    rootProduct (borderBand ell g m) =
      CatalanCore.Linalg.CauchyPolynomial.denom
        (fun a : Fin m => ((g+2*a.val+2 : ℕ) : ZMod ell)) *
      CatalanCore.Linalg.CauchyPolynomial.denom
        (fun a : Fin m => ((g+2*a.val+1 : ℕ) : ZMod ell)) := by
  have hk := H.hK; have hs := H.hS; have hsg := H.hSg; have hr := H.room
  unfold rootProduct borderBand zband
  rw [Finset.prod_image]
  · rw [Finset.prod_Ico_eq_prod_range]
    have hc : g+2*m+1-(g+1)=2*m := by omega
    rw [hc, prod_range_pairs]
    unfold CatalanCore.Linalg.CauchyPolynomial.denom Lagrange.nodal
    rw [← Finset.prod_range (fun a : ℕ => (X : (ZMod ell)[X]) - C ((g+2*a+2 : ℕ) : ZMod ell)),
      ← Finset.prod_range (fun a : ℕ => (X : (ZMod ell)[X]) - C ((g+2*a+1 : ℕ) : ZMod ell))]
    congr 1 <;> apply Finset.prod_congr rfl <;> intro a ha <;> congr 2 <;>
      apply congrArg (fun b : ℕ => (b : ZMod ell)) <;> omega
  · intro a ha b hb hab
    have ha' := (Finset.mem_Ico.mp ha).2
    have hb' := (Finset.mem_Ico.mp hb).2
    have he := congrArg ZMod.val hab
    simpa only [ZMod.val_natCast_of_lt (show a < ell by omega),
      ZMod.val_natCast_of_lt (show b < ell by omega)] using he

#print axioms borderBand_rootProduct_eq_interleaved



lemma mem_lowBand_iff_exists_neg (H : BandGeometry ell K m S g) (x : ZMod ell) :
    x ∈ lowBand ell K ↔ ∃ a : Fin K, -(a.val : ZMod ell) = x := by
  rw [lowBand_eq_image_neg H]
  simp only [Finset.mem_image, Finset.mem_univ, true_and]

end CatalanCore.Arith.Hybrid.FiniteFieldCorank
