import CatalanCore.Uniform.Content.RankProducer.Triv
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Lambda.RankTools
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.Hybrid
  CatalanCore.Uniform.Content.RankProducer

/-- Matrix denominators are kept as a fixed integer; factoring it is unnecessary. -/
def DenOk (c : FibreCert) (N : ℕ) : Prop :=
  (∀ d ∈ c.R, ∀ e ∈ c.R, (c.Lq d e).den ∣ N ∧ (c.Lq' d e).den ∣ N) ∧
  (∀ d ∈ c.C, ∀ e ∈ c.C, (c.Pq d e).den ∣ N ∧ (c.Pq' d e).den ∣ N)

theorem integral_of_denOk (c : FibreCert) (N p : ℕ) [Fact p.Prime]
    (h : DenOk c N) (hp : ¬ p ∣ N) : c.Integral p := by
  have key : ∀ v : ℚ, v.den ∣ N → v ∈ S p := by
    intro v hv hd
    exact hp (hd.trans hv)
  exact ⟨fun d hd e he => ⟨key _ (h.1 d hd e he).1, key _ (h.1 d hd e he).2⟩,
    fun d hd e he => ⟨key _ (h.2 d hd e he).1, key _ (h.2 d hd e he).2⟩⟩

/-- Rebalancing may discard killed coordinates without changing any local matrix. -/
def trim (c : FibreCert) (kr kc : Finset ℕ) : FibreCert := { c with kr := kr, kc := kc }

theorem trim_ok (c : FibreCert) (h : c.Ok) (kr kc : Finset ℕ)
    (hr : kr ⊆ c.kr) (hc : kc ⊆ c.kc) : (trim c kr kc).Ok := by
  refine ⟨h.hLL, h.hPP, hr.trans h.kr_sub, hc.trans h.kc_sub, ?_, ?_⟩
  · intro d hd e he
    exact h.hrow d (hr hd) e he
  · intro d hd e he
    exact h.hcol d hd e (hc he)

theorem trim_integral (c : FibreCert) (p : ℕ) [Fact p.Prime]
    (h : c.Integral p) (kr kc : Finset ℕ) : (trim c kr kc).Integral p := ⟨h.lq, h.pq⟩

theorem trim_realizes {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : ℕ} {f e : ℕ → ℚ} (PS : PoleSplit p B f e) (a b : ι → ℕ) (x : ZMod p)
    (c : FibreCert) (h : Realizes PS a b x c) (kr kc : Finset ℕ) :
    Realizes PS a b x (trim c kr kc) :=
  ⟨h.r_mem, h.r_cov, h.c_mem, h.c_cov, h.lf_r, h.lf_c, h.ee_r⟩

#print axioms integral_of_denOk
#print axioms trim_ok
end CatalanCore.Uniform.Bank.Lambda.RankTools

