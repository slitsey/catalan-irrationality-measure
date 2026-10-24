module
public import CatalanMeasure.Parametric.Parameters
@[expose] public section
namespace CatalanMeasure.Parametric

def twenty : Parameters :=⟨20,3,1,2,1⟩
theorem twenty_admissible : Admissible twenty :=by decide

theorem twenty_H (N : Nat) : twenty.H N=27*N :=by
  unfold Parameters.H Parameters.C Parameters.L Parameters.n Parameters.b Parameters.q Parameters.g Parameters.h twenty
  dsimp
  omega

theorem twenty_C (N : Nat) : twenty.C N=26*N :=by
  unfold Parameters.C Parameters.L Parameters.n Parameters.b Parameters.q Parameters.g twenty
  dsimp
  omega

theorem twenty_A (N : Nat) : twenty.A N=8*N :=by
  unfold Parameters.A Parameters.b Parameters.q Parameters.g twenty
  dsimp
  omega

end CatalanMeasure.Parametric
