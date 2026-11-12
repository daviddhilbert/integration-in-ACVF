import IntegrationSection6.GammaRawStandardContractions

/-! The raw contraction domain consists of exactly the actual final labels. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n a : ℕ} {U : DefSet (M := M) S n a} {σ : Equiv.Perm (Fin n)}

theorem rawContractionDomain_iff (C : StandardContraction U σ) (p : Point (M := M) 0 C.arity) :
    p.2 ∈ carrier (rvObjectDomain C.contractionObject) ↔ p ∈ carrier C.target := by
  constructor
  · rintro ⟨w,hw⟩
    have he : w.val = p := Prod.ext (funext fun i => Fin.elim0 i) hw
    exact he ▸ w.property
  · intro hp
    exact ⟨⟨p,hp⟩,rfl⟩

end IntegrationInACVF.Section6
