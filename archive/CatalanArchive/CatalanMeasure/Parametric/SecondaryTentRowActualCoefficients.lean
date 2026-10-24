module
public import CatalanArchive.CatalanMeasure.Parametric.SecondaryTentRowDivisor
public import CatalanArchive.CatalanMeasure.Parametric.SecondaryTentRowInputExpansion
public import CatalanArchive.CatalanMeasure.Parametric.SecondaryTentRowDirectFlags
public import CatalanArchive.CatalanMeasure.Parametric.SecondaryTentRowDirectDegree
@[expose] public section

namespace CatalanMeasure.Parametric
open Polynomial Matrix
open scoped BigOperators
noncomputable section

def secondaryTentRowNaturalNumeratorLinear {K : Type*} [Field K] (p d : ℕ) :
    (K[X] × K[X]) →ₗ[K] K[X] where
  toFun F := secondaryTentRowNaturalNumerator p d F.1 F.2
  map_add' F G := by
    change (X-1)^p*(secondaryTentRowInputLinear d) (F.1+G.1)+
      (X+1)^p*(secondaryTentRowInputLinear d) (F.2+G.2) = _
    rw [map_add,map_add]
    change (X-1)^p*(secondaryTentRowInput d F.1+secondaryTentRowInput d G.1)+
      (X+1)^p*(secondaryTentRowInput d F.2+secondaryTentRowInput d G.2) =
      ((X-1)^p*secondaryTentRowInput d F.1+(X+1)^p*secondaryTentRowInput d F.2)+
      ((X-1)^p*secondaryTentRowInput d G.1+(X+1)^p*secondaryTentRowInput d G.2)
    ring
  map_smul' t F := by
    change (X-1)^p*(secondaryTentRowInputLinear d) (t • F.1)+
      (X+1)^p*(secondaryTentRowInputLinear d) (t • F.2) = _
    rw [map_smul,map_smul]
    change (X-1)^p*(t • secondaryTentRowInput d F.1)+
      (X+1)^p*(t • secondaryTentRowInput d F.2) =
      t • secondaryTentRowNaturalNumerator p d F.1 F.2
    simp only [← C_mul',secondaryTentRowNaturalNumerator]
    ring

def secondaryTentRowFixedNaturalPacketLinear {K : Type*} [Field K] (p : ℕ) :
    (Fin p → (Fin 5 → K)) →ₗ[K] K[X] :=
  (secondaryTentRowNaturalNumeratorLinear p (4*p-1)).comp
    (((secondaryTentInterleaveLinear p).comp (LinearMap.pi fun e =>
      ((LinearMap.fst K K[X] K[X]).comp secondaryTentRowFixedSeedPair).comp (LinearMap.proj e))).prod
     ((secondaryTentInterleaveLinear p).comp (LinearMap.pi fun e =>
      ((LinearMap.snd K K[X] K[X]).comp secondaryTentRowFixedSeedPair).comp (LinearMap.proj e))))

theorem secondaryTent_row_fixed_natural_packet_linear_apply {K : Type*} [Field K]
    (p : ℕ) (c : Fin p → (Fin 5 → K)) :
    secondaryTentRowFixedNaturalPacketLinear p c = secondaryTentRowFixedNaturalPacket p c := rfl

/-- The concrete full-frame row map. Index i is the physical row ell=i-2N. -/
def secondaryTentActualRowLinear {K : Type*} [Field K] (N p a : ℕ) :
    (Fin p → (Fin 5 → K)) →ₗ[K] (Fin (20*N) → K) :=
  (secondaryTentRowQuotientCoefficients N p a).comp (secondaryTentRowFixedNaturalPacketLinear p)

/-- Exact packet injection survives division and extraction of the actual
20N row coefficients on every constrained parameter family satisfying
the literal divisor and shared degree flags. -/
theorem secondaryTent_actual_row_injective_on_flags {K : Type*} [Field K]
    (h2 : (2:K)≠0) (hunit : (3445975817256960:K)≠0)
    (N p a g : ℕ) (hN : 0<N) (hp : 0<p) (hodd : Odd p)
    (hpN : 2*p≤24*N) (hag : a+g=p) (hgp : g+4*p=27*N)
    (c d : Fin p → (Fin 5 → K))
    (hc : (secondaryTentRowFixedNaturalPacket p c).natDegree+8*N+3≤10*p)
    (hd : (secondaryTentRowFixedNaturalPacket p d).natDegree+8*N+3≤10*p)
    (hdc : secondaryTentRowTotalDivisor N p a ∣ secondaryTentRowFixedNaturalPacket p c)
    (hdd : secondaryTentRowTotalDivisor N p a ∣ secondaryTentRowFixedNaturalPacket p d)
    (heq : secondaryTentActualRowLinear N p a c = secondaryTentActualRowLinear N p a d) : c=d := by
  apply secondaryTent_row_fixed_natural_packet_injective h2 hunit hp hodd
  apply secondaryTent_row_quotient_coefficients_injective N p a g _ _ hN hp hpN hag hgp hc hd hdc hdd
  exact heq

def secondaryTentRowActualSeedColumn {K : Type*} [Field K] (i : Fin 5) : Fin 7 → K :=
  (secondaryTentSeedCoefficients.map (Int.castRingHom K)).mulVec (Pi.single i 1)

theorem secondaryTent_row_seed_column_boundary {K : Type*} [Field K]
    (i : Fin 5) (hi : i≠4) : secondaryTentRowActualSeedColumn (K := K) i 6=0 := by
  classical
  fin_cases i <;> norm_num [secondaryTentRowActualSeedColumn,Matrix.mulVec_single_one,
    secondaryTentSeedCoefficients] at *

/-- The upper tent's small boundary input supplies the entire actual
lower endpoint divisor z^(24N-2p). -/
theorem secondaryTent_actual_row_positive_lower_flag {p : ℕ} [Fact p.Prime]
    (h2 : (2:ZMod p)≠0) (N δ m : ℕ) (c : Fin p → (Fin 5 → ZMod p))
    (hp : p=6*N+δ) (hm : m+1=4*δ) (hmp : m≤p-1) (hpN : 2*p≤24*N)
    (hI : (secondaryTentRowInputPolynomial p c 4).natDegree≤m) :
    X^(24*N-2*p) ∣ secondaryTentRowFixedNaturalPacket p c := by
  rw [secondaryTent_row_fixed_input_source_junction h2]
  have hz := secondaryTent_row_boundary_packet_zero_factor h2 (4 : Fin 5) p m
    (secondaryTentRowActualSeedColumn (K := ZMod p)) (secondaryTentRowInputPolynomial p c)
    hmp hI (secondaryTent_row_seed_column_boundary (K := ZMod p))
  have he : p+(p-1-m)=24*N-2*p := by omega
  simpa only [he,secondaryTentRowActualSeedColumn] using hz

/-- The lower tent's first4d K-coefficient flag supplies the lower endpoint
after the automatically paid ordinary z^(2p) factor. -/
theorem secondaryTent_actual_row_negative_lower_flag {p : ℕ} [Fact p.Prime]
    (h2 : (2:ZMod p)≠0) (N d : ℕ) (c : Fin p → (Fin 5 → ZMod p))
    (hp : p+d=6*N) (hIB : secondaryTentRowInputPolynomial p c 4=0)
    (hc : ∀ j : Fin (4*d), (secondaryTentRowFixedNaturalPacket p c).coeff (2*p+j.val)=0) :
    X^(24*N-2*p) ∣ secondaryTentRowFixedNaturalPacket p c := by
  have hz : X^(2*p) ∣ secondaryTentRowFixedNaturalPacket p c := by
    rw [secondaryTent_row_fixed_input_source_junction h2]
    apply secondaryTent_row_ordinary_packet_zero_factor
    intro i
    by_cases hi : i=4
    · exact Or.inr (hi ▸ hIB)
    · exact Or.inl (secondaryTent_row_seed_column_boundary i hi)
  have hh := secondaryTent_row_lower_coefficients_flag (2*p) (4*d) _ hz hc
  have he : 2*p+4*d=24*N-2*p := by omega
  simpa only [he] using hh

/-- The single shared top-input flag pays the actual row's entire upper
endpoint, including the boundary channel. -/
theorem secondaryTent_actual_row_shared_degree_flag {p : ℕ} [Fact p.Prime]
    (h2 : (2:ZMod p)≠0) (N m : ℕ) (c : Fin p → (Fin 5 → ZMod p))
    (hm : m≤p-1) (hcap : m+8*N+2=2*p)
    (hS : (secondaryTentRowTopInput (secondaryTentRowActualSeedColumn (K := ZMod p))
      (secondaryTentRowInputPolynomial p c)).natDegree≤m) :
    (secondaryTentRowFixedNaturalPacket p c).natDegree+8*N+3≤10*p := by
  rw [secondaryTent_row_fixed_input_source_junction h2]
  exact secondaryTent_row_direct_packet_degree h2 N (p-1) m _ _
    (by have hp := (Fact.out : p.Prime).pos; omega) hm hcap hS

end
end CatalanMeasure.Parametric
