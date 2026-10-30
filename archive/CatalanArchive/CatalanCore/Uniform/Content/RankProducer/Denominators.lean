import CatalanCore.Uniform.Content.RankProducer.Cert
set_option Elab.async false

namespace CatalanCore.Uniform.Content.RankProducer.FibreCert
open CatalanCore.Basic CatalanCore.Uniform.Content.Hybrid

/-- A fixed common multiple of all change-of-basis denominators. -/
def DenOk (c : FibreCert) (N : ℕ) : Prop :=
  (∀ d ∈ c.R, ∀ e ∈ c.R, (c.Lq d e).den ∣ N ∧ (c.Lq' d e).den ∣ N) ∧
  (∀ d ∈ c.C, ∀ e ∈ c.C, (c.Pq d e).den ∣ N ∧ (c.Pq' d e).den ∣ N)

/-- A local certificate is integral at every prime avoiding its fixed denominator.
Factoring that denominator is unnecessary. -/
theorem integral_of_denOk (c : FibreCert) (N p : ℕ) [Fact p.Prime]
    (h : c.DenOk N) (hp : ¬ p ∣ N) : c.Integral p := by
  have key : ∀ v : ℚ, v.den ∣ N → v ∈ S p := by
    intro v hv hd
    exact hp (hd.trans hv)
  exact ⟨fun d hd e he => ⟨key _ (h.1 d hd e he).1, key _ (h.1 d hd e he).2⟩,
    fun d hd e he => ⟨key _ (h.2 d hd e he).1, key _ (h.2 d hd e he).2⟩⟩

#print axioms integral_of_denOk
end CatalanCore.Uniform.Content.RankProducer.FibreCert
