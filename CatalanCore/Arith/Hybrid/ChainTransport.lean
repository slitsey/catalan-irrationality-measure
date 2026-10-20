module
public import CatalanCore.Arith.Hybrid.ChainData
@[expose] public section
open Finset CatalanCore
namespace CatalanCore.Arith.Hybrid.ChainClasses

/-- Positive periods taking a zone node down into the finite core. -/
abbrev ChainIndex (p r z : ℕ) := {i : ℤ // InChain p r z i}

def chainNode {p r z : ℕ} (i : ChainIndex p r z) : Fin r :=
  ⟨((z : ℤ)-i.val*p).toNat, by have hi := i.property; change 0 < i.val ∧ 0 ≤ (z : ℤ)-i.val*p ∧ (z : ℤ)-i.val*p < r at hi; omega⟩

lemma chainNode_cast {p r z : ℕ} (i : ChainIndex p r z) :
    ((chainNode i).val : ℤ) = (z : ℤ)-i.val*p :=
  Int.toNat_of_nonneg i.property.2.1

lemma chainNode_injective {p r z : ℕ} (hp : 0<p) :
    Function.Injective (@chainNode p r z) := by
  intro i j hij
  apply Subtype.ext
  have h := congrArg (fun a : Fin r => (a.val : ℤ)) hij
  rw [chainNode_cast, chainNode_cast] at h
  have hp' : (0 : ℤ)<p := by exact_mod_cast hp
  nlinarith

noncomputable instance {p r z : ℕ} [NeZero p] : Fintype (ChainIndex p r z) :=
  Fintype.ofInjective chainNode (chainNode_injective (NeZero.pos p))

/-- The period index stays fixed under translation inside a cut-free interval. -/
def chainTransport {p r z w : ℕ} {sing : ℤ → Prop} (hzw : z≤w)
    (h : NoCut (Cut p r sing) z w) : ChainIndex p r z ≃ ChainIndex p r w where
  toFun i := ⟨i.val, (chain_iff (by exact_mod_cast hzw) h).mp i.property⟩
  invFun i := ⟨i.val, (chain_iff (by exact_mod_cast hzw) h).mpr i.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma chainNode_transport {p r z w : ℕ} {sing : ℤ → Prop} (hzw : z≤w)
    (h : NoCut (Cut p r sing) z w) (i : ChainIndex p r z) :
    ((chainNode (chainTransport hzw h i)).val : ℤ) =
      ((chainNode i).val : ℤ) + ((w : ℤ)-z) := by
  rw [chainNode_cast, chainNode_cast]
  change (w : ℤ)-i.val*p = (z : ℤ)-i.val*p+(w-z)
  ring

lemma chainNode_dvd {p r z : ℕ} (i : ChainIndex p r z) :
    (p : ℤ) ∣ (z : ℤ)-(chainNode i).val := by
  refine ⟨i.val, ?_⟩
  rw [chainNode_cast]
  ring

lemma exists_chainNode {p r z : ℕ} (hp : 0<p) (hz : r≤z) (a : Fin r)
    (ha : (p : ℤ) ∣ (z : ℤ)-a.val) :
    ∃ i : ChainIndex p r z, chainNode i=a := by
  obtain ⟨i, hi⟩ := ha
  have hp' : (0 : ℤ)<p := by exact_mod_cast hp
  have ha' : (a.val : ℤ)<r := by exact_mod_cast a.isLt
  have hz' : (r : ℤ)≤z := by exact_mod_cast hz
  have hi' : 0 < i := by nlinarith
  have he : (z : ℤ)-i*p=a.val := by nlinarith
  refine ⟨⟨i, hi', by omega, by omega⟩, ?_⟩
  apply Fin.ext
  apply Int.ofNat_inj.mp
  rw [chainNode_cast]
  exact he

variable {p : ℕ} [Fact p.Prime]

/-- The actual singular cumulative transports on corresponding core nodes. -/
theorem uniform_Lv_chain_eq {o N r z w : ℕ} (ho : o≤3) (hzw : z≤w)
    (h : NoCut (Cut p r (Singular p o)) z w) (v : ℕ → ZMod p)
    (i : ChainIndex p r z) :
    Lv (singularNodes p o N) v (chainNode i).val =
      Lv (singularNodes p o N) v (chainNode (chainTransport hzw h i)).val := by
  have he := uniform_prefix_chain_eq (N := N) ho (by exact_mod_cast hzw) h v (i := i.val)
  have he2 : ((chainNode (chainTransport hzw h i)).val : ℤ) = (w : ℤ)-i.val*p := chainNode_cast _
  rw [← chainNode_cast i, ← he2] at he
  simpa only [prefix_nat, Lv] using he

/-- The same no-cut hypothesis identifies the two zone-node cumulative values. -/
theorem uniform_Lv_zone_eq {o N r z w : ℕ} (ho : o≤3) (hzw : z≤w)
    (h : NoCut (Cut p r (Singular p o)) z w) (v : ℕ → ZMod p) :
    Lv (singularNodes p o N) v z = Lv (singularNodes p o N) v w := by
  have he := uniform_prefix_chain_eq (N := N) ho (by exact_mod_cast hzw) h v (i := 0)
  simpa only [zero_mul, sub_zero, prefix_nat, Lv] using he

#print axioms uniform_Lv_chain_eq
#print axioms exists_chainNode
end CatalanCore.Arith.Hybrid.ChainClasses
