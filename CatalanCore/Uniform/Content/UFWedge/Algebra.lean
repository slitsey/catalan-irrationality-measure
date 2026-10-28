module

public import CatalanCore.Uniform.Content.UFMoments.NodeLoc

@[expose] public section

/-!
# UF wedge, algebra of a bordered fiber (lane H9)

For a fiber block `M` (square matrix over a commutative ring), a border vector `s`, a vector `u`
and a scalar `t` put

  `fibA M s u t = det M * t - Σ_i s_i Σ_j adj(M)_{ij} u_j`  (= det of the bordered matrix).

With `u = 1, t = 1` this is `fibB`.  In a field with `det M ≠ 0`, `fibA = det M (t - s M⁻¹ u)`:
`fibA` is `det M` times the Python `A` (`t = L_z`, `u = L`) and `fibB` is `det M` times `B = 1 - Σ g`.
The cross wedge is `fibB_J fibA_K - fibA_J fibB_K`.

* `map_fibA`: ring homomorphisms (evaluation of polynomials) commute with `fibA`;
* `fibA_equiv`: invariance under a relabelling of the fiber;
* `fibA_smul`: homogeneity of degree `card n + 1` (for the common-denominator certificate).
-/

open Matrix Finset

namespace CatalanCore.Uniform.Content.UFWedge

section Generic

variable {R S : Type*} [CommRing R] [CommRing S] {n m : Type*} [Fintype n] [DecidableEq n]
  [Fintype m] [DecidableEq m]

/-- The bordered determinant of a fiber. -/
def fibA (M : Matrix n n R) (s u : n → R) (t : R) : R :=
  M.det * t - ∑ i, s i * ∑ j, M.adjugate i j * u j

/-- `fibA` with the all-ones vector and the scalar one. -/
def fibB (M : Matrix n n R) (s : n → R) : R := fibA M s (fun _ => 1) 1

/-- The cross wedge `B_J A_K - A_J B_K` of two bordered fibers. -/
def fibCross (M₀ : Matrix n n R) (s₀ u₀ : n → R) (t₀ : R)
    (M₁ : Matrix m m R) (s₁ u₁ : m → R) (t₁ : R) : R :=
  fibB M₀ s₀ * fibA M₁ s₁ u₁ t₁ - fibA M₀ s₀ u₀ t₀ * fibB M₁ s₁

theorem map_fibA (f : R →+* S) (M : Matrix n n R) (s u : n → R) (t : R) :
    f (fibA M s u t) = fibA (M.map f) (fun i => f (s i)) (fun i => f (u i)) (f t) := by
  have hd : f M.det = (M.map f).det := by
    have := RingHom.map_det f M
    simpa using this
  have ha : ∀ i j, f (M.adjugate i j) = (M.map f).adjugate i j := by
    intro i j
    have := RingHom.map_adjugate f M
    exact congrFun (congrFun this i) j
  unfold fibA
  rw [map_sub, map_mul, hd, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, ha]

theorem map_fibB (f : R →+* S) (M : Matrix n n R) (s : n → R) :
    f (fibB M s) = fibB (M.map f) (fun i => f (s i)) := by
  unfold fibB
  rw [map_fibA]
  simp

theorem map_fibCross (f : R →+* S) (M₀ : Matrix n n R) (s₀ u₀ : n → R) (t₀ : R)
    (M₁ : Matrix m m R) (s₁ u₁ : m → R) (t₁ : R) :
    f (fibCross M₀ s₀ u₀ t₀ M₁ s₁ u₁ t₁) =
      fibCross (M₀.map f) (fun i => f (s₀ i)) (fun i => f (u₀ i)) (f t₀)
        (M₁.map f) (fun i => f (s₁ i)) (fun i => f (u₁ i)) (f t₁) := by
  unfold fibCross
  rw [map_sub, map_mul, map_mul, map_fibA, map_fibA, map_fibB, map_fibB]

/-- Invariance under a relabelling of the fiber. -/
theorem fibA_equiv (e : n ≃ m) (M : Matrix n n R) (M' : Matrix m m R) (s u : n → R)
    (s' u' : m → R) (t : R) (hM : ∀ i j, M' (e i) (e j) = M i j) (hs : ∀ i, s' (e i) = s i)
    (hu : ∀ i, u' (e i) = u i) :
    fibA M' s' u' t = fibA M s u t := by
  have hMe : M' = M.submatrix e.symm e.symm := by
    ext a b
    simp only [Matrix.submatrix_apply]
    have := hM (e.symm a) (e.symm b)
    simpa using this
  unfold fibA
  rw [hMe, Matrix.det_submatrix_equiv_self, Matrix.adjugate_submatrix_equiv_self]
  congr 1
  rw [← Equiv.sum_comp e]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hs i]
  congr 1
  rw [← Equiv.sum_comp e]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [hu j]

theorem fibB_equiv (e : n ≃ m) (M : Matrix n n R) (M' : Matrix m m R) (s : n → R) (s' : m → R)
    (hM : ∀ i j, M' (e i) (e j) = M i j) (hs : ∀ i, s' (e i) = s i) :
    fibB M' s' = fibB M s :=
  fibA_equiv e M M' s (fun _ => 1) s' (fun _ => 1) 1 hM hs (fun _ => rfl)

theorem fibCross_equiv (e₀ : n ≃ n) (M₀ M₀' : Matrix n n R) (s₀ s₀' u₀ u₀' : n → R) (t₀ : R)
    (e₁ : m ≃ m) (M₁ M₁' : Matrix m m R) (s₁ s₁' u₁ u₁' : m → R) (t₁ : R)
    (hM₀ : ∀ i j, M₀' (e₀ i) (e₀ j) = M₀ i j) (hs₀ : ∀ i, s₀' (e₀ i) = s₀ i)
    (hu₀ : ∀ i, u₀' (e₀ i) = u₀ i)
    (hM₁ : ∀ i j, M₁' (e₁ i) (e₁ j) = M₁ i j) (hs₁ : ∀ i, s₁' (e₁ i) = s₁ i)
    (hu₁ : ∀ i, u₁' (e₁ i) = u₁ i) :
    fibCross M₀' s₀' u₀' t₀ M₁' s₁' u₁' t₁ = fibCross M₀ s₀ u₀ t₀ M₁ s₁ u₁ t₁ := by
  unfold fibCross
  rw [fibB_equiv e₀ M₀ M₀' s₀ s₀' hM₀ hs₀, fibB_equiv e₁ M₁ M₁' s₁ s₁' hM₁ hs₁,
    fibA_equiv e₀ M₀ M₀' s₀ u₀ s₀' u₀' t₀ hM₀ hs₀ hu₀,
    fibA_equiv e₁ M₁ M₁' s₁ u₁ s₁' u₁' t₁ hM₁ hs₁ hu₁]

/-- Homogeneity: scaling all data by `c` multiplies `fibA` by `c ^ (card n + 1)`. -/
theorem fibA_smul (c : R) (M : Matrix n n R) (s u : n → R) (t : R) :
    fibA (c • M) (fun i => c * s i) (fun i => c * u i) (c * t) =
      c ^ (Fintype.card n + 1) * fibA M s u t := by
  unfold fibA
  rw [Matrix.det_smul, Matrix.adjugate_smul]
  rcases isEmpty_or_nonempty n with hn | hn
  · simp [Fintype.card_eq_zero]
  · obtain ⟨k, hk⟩ : ∃ k, Fintype.card n = k + 1 :=
      ⟨Fintype.card n - 1, by have := Fintype.card_pos (α := n); omega⟩
    rw [hk, Nat.add_sub_cancel]
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [mul_sub, Finset.mul_sum]
    congr 1
    · ring
    · refine Finset.sum_congr rfl fun i _ => ?_
      have : ∑ j, c ^ k * M.adjugate i j * (c * u j) = c ^ (k + 1) * ∑ j, M.adjugate i j * u j := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      rw [this]; ring

end Generic

/-! ### Bordered fibers as data -/

/-- A bordered fiber: block `M`, border vector `s`, prefix vector `u` and border prefix `z`. -/
structure FibD (R : Type*) [CommRing R] where
  n : Type
  [fin : Fintype n]
  [dec : DecidableEq n]
  M : Matrix n n R
  s : n → R
  u : n → R
  z : R

attribute [instance] FibD.fin FibD.dec

namespace FibD

variable {R S : Type*} [CommRing R] [CommRing S]

/-- `A = det M · (z - s M⁻¹ u)`. -/
def A (F : FibD R) : R := fibA F.M F.s F.u F.z

/-- `B = det M · (1 - s M⁻¹ 1)`. -/
def B (F : FibD R) : R := fibB F.M F.s

/-- The cross wedge `B_J A_K - A_J B_K`. -/
def cross (F G : FibD R) : R := F.B * G.A - F.A * G.B

/-- Image under a ring homomorphism. -/
def map (f : R →+* S) (F : FibD R) : FibD S :=
  { n := F.n, M := F.M.map f, s := fun i => f (F.s i), u := fun i => f (F.u i), z := f F.z }

theorem map_A (f : R →+* S) (F : FibD R) : f F.A = (F.map f).A := map_fibA f _ _ _ _

theorem map_B (f : R →+* S) (F : FibD R) : f F.B = (F.map f).B := map_fibB f _ _

theorem map_cross (f : R →+* S) (F G : FibD R) : f (F.cross G) = (F.map f).cross (G.map f) := by
  unfold cross
  rw [map_sub, map_mul, map_mul, map_A, map_A, map_B, map_B]

/-- Isomorphism of bordered fibers (relabelling). -/
def Iso (F G : FibD R) : Prop :=
  ∃ e : F.n ≃ G.n, (∀ i j, G.M (e i) (e j) = F.M i j) ∧ (∀ i, G.s (e i) = F.s i) ∧
    (∀ i, G.u (e i) = F.u i) ∧ G.z = F.z

theorem Iso.A_eq {F G : FibD R} (h : F.Iso G) : G.A = F.A := by
  obtain ⟨e, hM, hs, hu, hz⟩ := h
  unfold A
  rw [hz]
  exact fibA_equiv e F.M G.M F.s F.u G.s G.u F.z hM hs hu

theorem Iso.B_eq {F G : FibD R} (h : F.Iso G) : G.B = F.B := by
  obtain ⟨e, hM, hs, hu, hz⟩ := h
  exact fibB_equiv e F.M G.M F.s G.s hM hs

theorem Iso.cross_left {F F' G : FibD R} (h : F.Iso F') : F'.cross G = F.cross G := by
  unfold cross; rw [h.A_eq, h.B_eq]

theorem Iso.cross_right {F G G' : FibD R} (h : G.Iso G') : F.cross G' = F.cross G := by
  unfold cross; rw [h.A_eq, h.B_eq]

end FibD

end CatalanCore.Uniform.Content.UFWedge
