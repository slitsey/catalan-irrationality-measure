module

public import CatalanFrames.LambdaMirrorHybrid.MirN
public import CatalanFrames.LambdaMirror.ContentData
public import CatalanCore.Arith.Hybrid.InstNeg

@[expose] public section

/-!
# The mirror hybrid instance `mirNInst : HybInst mirNFrame`

The block-valued instance of the legacy mirror content data `mirCD` (`Φ(k) = k(4k-3)`, bad primes
`{2, 3}`), transported to `mirNFrame` by the sign transfer `HybInst.neg`.
-/

open Finset CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanFrames.LambdaMirror

namespace CatalanFrames.LambdaMirrorHybrid

lemma mirPhi_le (k N : ℕ) (h : k ≤ N) : mirCD.Phi k ≤ 4 * N * N := by
  show k * (4 * k - 3) ≤ 4 * N * N
  calc k * (4 * k - 3) ≤ N * (4 * N) := Nat.mul_le_mul h (by omega)
    _ = 4 * N * N := by ring

/-- The block-valued hybrid instance of the legacy mirror frame. -/
noncomputable def mirInst : HybInst mirFrame :=
  HybInst.ofSing mirCD (fun N => 4 * N * N) mirPhi_le

instance mirInst_diagOK (r m : ℕ) : mirInst.DiagOK r m :=
  inferInstanceAs ((HybInst.ofSing mirCD (fun N => 4 * N * N) mirPhi_le).DiagOK r m)

/-- The mirror hybrid instance for the λ-like sign. -/
noncomputable def mirNInst : HybInst mirNFrame :=
  mirInst.neg (fun k => by rw [mir_Delta_neg, neg_neg]) (fun k => by rw [mir_Dsq_neg, neg_neg]) rfl
    (fun a b => by rw [mir_Mn_neg, neg_neg])

instance mirNInst_diagOK (r m : ℕ) : mirNInst.DiagOK r m := ⟨fun _ _ => trivial⟩

lemma mirNInst_lev (q c : ℕ) : mirNInst.lev q c = blk mirCD.Phi q c := rfl

end CatalanFrames.LambdaMirrorHybrid
