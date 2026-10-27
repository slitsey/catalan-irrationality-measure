module
public import CatalanMeasure.GenD.Uniform.Prefix.VirtualCutoff
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Sum
@[expose] public section
set_option Elab.async false
namespace CatalanMeasure.GenD.Uniform.Prefix
open Polynomial
variable {K : Type*} [Field K]

theorem distinct_degree_cut {ι : Type*} [Fintype ι] (v : ι → K[X]) (δ : ι → Nat)
    (hinj : Function.Injective δ) (hv : ∀ i, (v i).degree=(δ i : WithBot Nat))
    (r : Nat) (c : ι → K) :
    (∑ i, c i • v i).degree<(r : WithBot Nat) ↔ ∀ i, r ≤ δ i → c i=0 := by
  classical
  have hn : ∀ i, v i≠0 := by
    intro i he
    have hd := hv i
    rw [he,degree_zero] at hd
    exact WithBot.bot_ne_coe hd
  have hd : ∀ i, c i≠0 → (c i • v i).degree=(δ i : WithBot Nat) := by
    intro i hi
    rw [degree_smul_of_isRightRegular_leadingCoeff hi
      (IsRegular.of_ne_zero (leadingCoeff_ne_zero.mpr (hn i))).right,hv]
  have hp : Set.Pairwise {i | i∈Finset.univ ∧ c i • v i≠0}
      (fun i j => (c i • v i).degree≠(c j • v j).degree) := by
    intro i hi j hj hij
    rw [hd i (smul_ne_zero_iff.mp hi.2).1,hd j (smul_ne_zero_iff.mp hj.2).1]
    intro he
    exact hij (hinj (WithBot.coe_injective he))
  rw [degree_sum_eq_of_disjoint (fun i => c i • v i) Finset.univ hp]
  constructor
  · intro hcut i hi
    by_contra hci
    have hle := Finset.le_sup (f := fun j => (c j • v j).degree) (Finset.mem_univ i)
    rw [hd i hci] at hle
    have hlt : (δ i : WithBot Nat)<r := lt_of_le_of_lt hle hcut
    have hnat : δ i<r := WithBot.coe_lt_coe.mp hlt
    omega
  · intro hc
    apply (Finset.sup_lt_iff (by simp : (⊥ : WithBot Nat)<(r : WithBot Nat))).mpr
    intro i _
    by_cases hci : c i=0
    · simp [hci]
    · rw [hd i hci]
      have hnat : δ i<r := lt_of_not_ge (fun h => hci (hc i h))
      exact_mod_cast hnat

abbrev EndpointModes (h : Nat) := Option (Fin h ⊕ Fin h)
def modeDegree {h : Nat} : EndpointModes h → Nat
  | none => 2*h
  | some (.inl j) => j.val
  | some (.inr j) => 2*h-j.val-1

theorem modeDegree_injective (h : Nat) : Function.Injective (modeDegree (h := h)) := by
  intro x y he
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some y =>
      rcases y with j|j <;> simp only [modeDegree] at he <;> have := j.is_lt <;> omega
  | some x =>
    cases y with
    | none =>
      rcases x with j|j <;> simp only [modeDegree] at he <;> have := j.is_lt <;> omega
    | some y =>
      rcases x with i|i <;> rcases y with j|j <;> simp only [modeDegree] at he
      · exact congrArg (some ∘ Sum.inl) (Fin.ext he)
      · have := i.is_lt; have := j.is_lt; omega
      · have := i.is_lt; have := j.is_lt; omega
      · exact congrArg (some ∘ Sum.inr) (Fin.ext (by have := i.is_lt; have := j.is_lt; omega))

noncomputable def endpointMode {h : Nat} (i : EndpointModes h) : K[X] :=
  Polynomial.Chebyshev.U K ((modeDegree i : Nat) : Int)

theorem endpoint_modes_cut [NeZero (2 : K)] (h r : Nat) (c : EndpointModes h → K) :
    (∑ i, c i • endpointMode (K := K) i).degree<(r : WithBot Nat) ↔
      ∀ i, r ≤ modeDegree i → c i=0 :=
  distinct_degree_cut (endpointMode (K := K)) modeDegree (modeDegree_injective h)
    (fun i => Polynomial.Chebyshev.degree_U_natCast K _) r c

#print axioms endpoint_modes_cut
end CatalanMeasure.GenD.Uniform.Prefix

