module
public import CatalanMeasure.G728.Cell
public import CatalanMeasure.G728.ZNorm
@[expose] public section
/-!
# 2-adically normalised Chebyshev fold for the MG certificates

Entry `j` of the Chebyshev states in `tfold` is divisible by `2 ^ (j - 1)`, and the Y/R coefficients
`Bs` share a factor `2 ^ 138`, so almost every literal is a multiple of `2 ^ 64`; such literals collide
in the kernel's 64-bit `Nat` hash. `tfoldN` runs the doubled states divided by `2 ^ j` (no doubling
step) on `Bs = d · Bsp`, and `tcomb_of_N` recovers `tcomb Bs` from it.
-/
namespace CatalanMeasure.G728

def tfoldN : List ℤ → (List ℤ × List ℤ) × List ℤ → (List ℤ × List ℤ) × List ℤ
  | [], st => st
  | b :: bs, ((u, u'), w) => tfoldN bs ((u', zsub (0 :: u') u), zadd w (zsc b u))

theorem zsub_eq : ∀ p q : List ℤ, zsub p q = zSub p q
  | [], _ => rfl
  | _ :: _, [] => rfl
  | a :: p, b :: q => by simp only [zsub, zSub, zsub_eq p q]

theorem zadd_eq : ∀ p q : List ℤ, zadd p q = zAdd p q
  | [], _ => rfl
  | _ :: _, [] => rfl
  | a :: p, b :: q => by simp only [zadd, zAdd, zadd_eq p q]

theorem zsc_comm (c b : ℤ) (t : List ℤ) : zsc c (zsc b t) = zsc b (zsc c t) := by
  simp only [zsc, List.map_map, Function.comp_def, mul_left_comm]

theorem zsc_mul (d b : ℤ) (t : List ℤ) : zsc (d * b) t = zsc d (zsc b t) := by
  simp only [zsc, List.map_map, Function.comp_def, mul_assoc]

theorem zsc_t2x (c : ℤ) (t : List ℤ) : zsc c (t2x t) = t2x (zsc c t) := by
  simp only [t2x, zsc, List.map_cons, mul_zero, List.map_map, Function.comp_def, mul_left_comm]

theorem tfold_shl : ∀ (bs u u' w : List ℤ),
    tfold bs (shl 2 u, shl 2 u') (shl 2 w) = shl 2 (tfoldN bs ((u, u'), w)).2
  | [], _, _, _ => rfl
  | b :: bs, u, u', w => by
    have h1 : zsub (t2x (shl 2 u')) (shl 2 u) = shl 2 (zsub (0 :: u') u) := by
      rw [zsub_eq, zsub_eq, shl_zSub]; rfl
    have h2 : zadd (shl 2 w) (zsc b (shl 2 u)) = shl 2 (zadd w (zsc b u)) := by
      rw [zadd_eq, zadd_eq, ← shl_zsc, shl_zAdd]
    show tfold bs (shl 2 u', zsub (t2x (shl 2 u')) (shl 2 u)) (zadd (shl 2 w) (zsc b (shl 2 u))) = _
    rw [h1, h2]; exact tfold_shl bs _ _ _

theorem tfold_zsc (c : ℤ) : ∀ (bs t t' acc : List ℤ),
    zsc c (tfold bs (t, t') acc) = tfold bs (zsc c t, zsc c t') (zsc c acc)
  | [], _, _, _ => rfl
  | b :: bs, t, t', acc => by
    have h1 : zsc c (zsub (t2x t') t) = zsub (t2x (zsc c t')) (zsc c t) := by
      rw [zsub_eq, zsub_eq, zsc_zSub, zsc_t2x]
    have h2 : zsc c (zadd acc (zsc b t)) = zadd (zsc c acc) (zsc b (zsc c t)) := by
      rw [zadd_eq, zadd_eq, zsc_zAdd, zsc_comm]
    show zsc c (tfold bs (t', zsub (t2x t') t) (zadd acc (zsc b t))) = tfold bs (zsc c t', zsub (t2x (zsc c t')) (zsc c t)) (zadd (zsc c acc) (zsc b (zsc c t)))
    rw [tfold_zsc c bs, h1, h2]

theorem tfoldN_zsc (d : ℤ) : ∀ (bs : List ℤ) (s : List ℤ × List ℤ) (w : List ℤ),
    tfoldN (zsc d bs) (s, zsc d w) = ((tfoldN bs (s, w)).1, zsc d (tfoldN bs (s, w)).2)
  | [], _, _ => rfl
  | b :: bs, (u, u'), w => by
    have h : zadd (zsc d w) (zsc (d * b) u) = zsc d (zadd w (zsc b u)) := by
      rw [zadd_eq, zadd_eq, zsc_zAdd, zsc_mul]
    show tfoldN (zsc d bs) ((u', zsub (0 :: u') u), zadd (zsc d w) (zsc (d * b) u)) = _
    rw [h]; exact tfoldN_zsc d bs _ _

theorem zsc_two_inj {a b : List ℤ} (h : zsc 2 a = zsc 2 b) : a = b :=
  (List.map_injective_iff.2 (mul_right_injective₀ (two_ne_zero (α := ℤ)))) h

theorem tfoldN_append (xs ys : List ℤ) (st : (List ℤ × List ℤ) × List ℤ) :
    tfoldN (xs ++ ys) st = tfoldN ys (tfoldN xs st) := by
  induction xs generalizing st with
  | nil => rfl
  | cons b bs ih => obtain ⟨⟨u, u'⟩, w⟩ := st; exact ih _

theorem tfoldN_chain (l : List ℤ) (k : ℕ) {s t u : (List ℤ × List ℤ) × List ℤ}
    (h1 : tfoldN (l.take k) s = t) (h2 : tfoldN (l.drop k) t = u) : tfoldN l s = u := by
  rw [← List.take_append_drop k l, tfoldN_append, h1, h2]

/-- `tcomb Bs` from a normalised run on `Bsp` with `Bs = d · Bsp`. -/
theorem tcomb_of_N (Bs Bsp tgt : List ℤ) (d : ℤ) (T : (List ℤ × List ℤ) × List ℤ)
    (hB : Bs = zsc d Bsp) (hT : tfoldN Bsp (([2], [0, 1]), []) = T)
    (h : shl 2 (zsc d T.2) = zsc 2 tgt) : tcomb Bs = tgt := by
  apply zsc_two_inj
  rw [← h, tcomb, tfold_zsc]
  show tfold Bs (shl 2 [2], shl 2 [0, 1]) (shl 2 []) = _
  rw [tfold_shl, hB]
  have := tfoldN_zsc d Bsp ([2], [0, 1]) []
  rw [show (zsc d [] : List ℤ) = [] from rfl] at this
  rw [this, hT]

end CatalanMeasure.G728
