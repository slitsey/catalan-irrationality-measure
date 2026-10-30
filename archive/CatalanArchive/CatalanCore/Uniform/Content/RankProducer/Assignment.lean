import CatalanCore.Uniform.Content.RankProducer.Triv
set_option Elab.async false
namespace CatalanCore.Uniform.Content.RankProducer
open CatalanCore CatalanCore.Uniform.Content.Hybrid
open scoped Classical
variable {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {B : ℕ} {f e : ℕ → ℚ}

/-- Every boundary or deletion-touched fibre receives its actual trivial certificate. -/
noncomputable def extendAssignment (PS : PoleSplit p B f e) (a b : ι → ℕ)
    (good : Finset (ZMod p)) (cert : ZMod p → FibreCert) (x : ZMod p) : FibreCert :=
  if x ∈ good then cert x else trivCert PS a b x

theorem extendAssignment_ok (PS : PoleSplit p B f e) (a b : ι → ℕ)
    (good : Finset (ZMod p)) (cert : ZMod p → FibreCert)
    (hOk : ∀ x ∈ good, (cert x).Ok) (x : ZMod p) :
    (extendAssignment PS a b good cert x).Ok := by
  unfold extendAssignment
  split_ifs with h
  · exact hOk x h
  · exact FibreCert.triv_ok _ _ _ _

theorem extendAssignment_integral (PS : PoleSplit p B f e) (a b : ι → ℕ)
    (good : Finset (ZMod p)) (cert : ZMod p → FibreCert)
    (hInt : ∀ x ∈ good, (cert x).Integral p) (x : ZMod p) :
    (extendAssignment PS a b good cert x).Integral p := by
  unfold extendAssignment
  split_ifs with h
  · exact hInt x h
  · exact FibreCert.triv_integral _ _ _ _

theorem extendAssignment_realizes (PS : PoleSplit p B f e) (a b : ι → ℕ)
    (good : Finset (ZMod p)) (cert : ZMod p → FibreCert)
    (hReal : ∀ x ∈ good, Realizes PS a b x (cert x)) (x : ZMod p) :
    Realizes PS a b x (extendAssignment PS a b good cert x) := by
  unfold extendAssignment
  split_ifs with h
  · exact hReal x h
  · exact trivCert_realizes PS a b x

theorem extendAssignment_killRows (PS : PoleSplit p B f e) (a b : ι → ℕ)
    (good : Finset (ZMod p)) (cert : ZMod p → FibreCert) :
    killRows (p := p) a (extendAssignment PS a b good cert) =
      (killRows (p := p) a cert).filter (fun i => (a i : ZMod p) ∈ good) := by
  ext i
  simp only [killRows, Finset.mem_filter, Finset.mem_univ, true_and]
  unfold extendAssignment
  split_ifs with h <;> simp [h, trivCert, FibreCert.triv]

theorem extendAssignment_killCols (PS : PoleSplit p B f e) (a b : ι → ℕ)
    (good : Finset (ZMod p)) (cert : ZMod p → FibreCert) :
    killCols (p := p) b (extendAssignment PS a b good cert) =
      (killCols (p := p) b cert).filter (fun i => (b i : ZMod p) ∈ good) := by
  ext i
  simp only [killCols, Finset.mem_filter, Finset.mem_univ, true_and]
  unfold extendAssignment
  split_ifs with h <;> simp [h, trivCert, FibreCert.triv]

#print axioms extendAssignment_realizes
#print axioms extendAssignment_killRows
end CatalanCore.Uniform.Content.RankProducer
