module
public import CatalanMeasure.Parametric.SparseFilteredRelation
@[expose] public section
namespace CatalanMeasure.Parametric
open Finset
noncomputable section

def sparseTargetRows (n g p e : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => g+2*p< i.val ∧ i.val ≤ g+2*p+e)

theorem sparseTargetRows_card {n g p e : ℕ} (hfit : g+2*p+e<n) :
    (sparseTargetRows n g p e).card=e := by
  classical
  let f : Fin e → Fin n :=fun d =>⟨g+2*p+d.val+1,by have :=d.isLt; omega⟩
  have heq : sparseTargetRows n g p e=Finset.univ.image f :=by
    ext i
    simp only [sparseTargetRows,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_image]
    constructor
    · intro hi
      let d : Fin e :=⟨i.val-(g+2*p+1),by omega⟩
      refine ⟨d,?_⟩
      apply Fin.ext
      dsimp only [f,d]
      omega
    · rintro ⟨d,rfl⟩
      dsimp only [f]
      have :=d.isLt
      constructor <;> omega
  rw [heq,Finset.card_image_of_injective]
  · exact Finset.card_fin e
  · intro a b hab
    apply Fin.ext
    have h :=congrArg Fin.val hab
    dsimp only [f] at h
    omega

def boundedSource {n : ℕ} (fallback : Fin n) (r : ℕ) : Fin n :=
  if hr : r<n then ⟨r,hr⟩ else fallback

theorem boundedSource_val {n r : ℕ} (i : Fin n) (hr : r<n) :
    (boundedSource i r).val=r :=by simp [boundedSource,hr]

def sparseMode {n : ℕ} (g p : ℕ) (i : Fin n) : ℕ :=i.val-(g+2*p)

theorem sparseMode_bounds {n g p e : ℕ} {i : Fin n} (hi : i∈sparseTargetRows n g p e) :
    0<sparseMode g p i ∧ sparseMode g p i ≤ e ∧ i.val=g+2*p+sparseMode g p i :=by
  simp only [sparseTargetRows,Finset.mem_filter,Finset.mem_univ,true_and] at hi
  unfold sparseMode
  omega

theorem sparseMode_sources_below {n g p e : ℕ} (hp : 0<p)
    {i : Fin n} (hi : i∈sparseTargetRows n g p e) :
    g+2*p-sparseMode g p i< i.val ∧
    g+p+sparseMode g p i< i.val ∧
    g+p-sparseMode g p i< i.val ∧
    g+sparseMode g p i< i.val ∧
    g-sparseMode g p i< i.val :=by
  have hh :=sparseMode_bounds hi
  omega

theorem baseline_sparse_modes_fit {N p : ℕ} (hN : 0<N) (hp : p ≤ 21*N) :
    4*N+2*p+min (4*N) (63*N-3*p)<48*N :=by
  have hlo :=Nat.min_le_left (4*N) (63*N-3*p)
  have hhi :=Nat.min_le_right (4*N) (63*N-3*p)
  have hcut : 3*p ≤ 63*N :=by omega
  have he :=Nat.sub_add_cancel hcut
  omega

end
end CatalanMeasure.Parametric

