import IntegrationSection5.StandardContractionGammaNormalization
import IntegrationSection6.GammaRVGlobalRestriction

/-! Original-Gamma certificates for the unnormalized actual final RV
labels of a standard contraction. Its volume selector is explicit. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n a : ℕ}
variable {U : DefSet (M := M) S n a} {σ : Equiv.Perm (Fin n)}

theorem gamma_raw_contraction_domain (C : StandardContraction U σ)
    (hC : GammaSetDefinable B (carrier C.target)) :
    GammaSetDefinable B {p : Point (M := M) 0 C.arity | p.2 ∈ carrier (rvObjectDomain C.contractionObject)} := by
  convert hC using 1
  ext p
  constructor
  · rintro ⟨w,hw⟩
    have he : w.val = p := Prod.ext (funext fun i => Fin.elim0 i) hw
    exact he ▸ w.property
  · intro hp
    exact ⟨⟨p,hp⟩,rfl⟩

def gammaRawContractionObject (C : StandardContraction U σ) (hBS : B.real ⊆ S)
    (hC : GammaSetDefinable B (carrier C.target)) : GammaRVObject B n where
  codes := S
  real_contains := hBS
  object := C.contractionObject
  domain_graph := gamma_raw_contraction_domain C hC
  volume_graph := by
    let G := rvCoordinatePointMap C.volumeIndex B.real
    apply GammaGraphDefinable.congr ((gammaLogicInput B).restrict_graph
      (gamma_raw_contraction_domain C hC) ((gammaLogicInput B).real_map_graph G))
    intro p q
    constructor
    · rintro ⟨hp,z,hz,hq⟩
      refine ⟨⟨p.2,hp⟩,rfl,?_⟩
      exact (congrArg (fun z : Point (M := M) 0 C.arity => z.2 ∘ C.volumeIndex) hz).symm.trans (congrArg Prod.snd hq)
    · rintro ⟨u,hu,hq⟩
      have hp : p.2 ∈ carrier (rvObjectDomain C.contractionObject) := hu ▸ u.property
      refine ⟨hp,⟨p,Set.mem_univ _⟩,rfl,?_⟩
      exact Prod.ext (funext fun i => Fin.elim0 i)
        ((congrArg (fun r => r ∘ C.volumeIndex) hu).symm.trans hq)

end IntegrationInACVF.Section6
