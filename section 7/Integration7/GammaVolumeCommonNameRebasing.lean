module

public import Integration7.GammaRVCommonNameRebasing
public import Integration7.GammaVolumeParameterGeometry

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Rebase actual Gamma volume objects without changing any carrier,
coordinate, density or finite-fibre condition. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S T : Set M} {k : ℕ}

def GammaVolumeObjects.overCommonNames (hc : CanonicalStructure.IsCanonical (M := M))
    (hNames : commonRealNames G ⊆ T) (U : GammaVolumeObjects G S k) : GammaVolumeObjects G T k := by
  let X : PositiveRVVolumeObject (M := M) T k := {
    underlying := ⟨{
      arity := U.val.underlying.obj.arity
      domain := gammaRVMapDomainRebase hc hNames U.val.underlying.obj.volume U.property.coordinates
      volume := gammaRVMapRebase hc hNames U.val.underlying.obj.volume U.property.coordinates },
      fun t => U.val.underlying.property ⟨t.val,Set.mem_univ _⟩⟩
    form := {
      map := gammaRVMapRebase hc hNames U.val.form.map U.property.density
      nonzero := fun u => U.val.form.nonzero ⟨u.val,u.property⟩ } }
  exact ⟨X,⟨gamma_rv_map_rebase_graph hc hNames U.val.underlying.obj.volume U.property.coordinates,
    gamma_rv_map_rebase_graph hc hNames U.val.form.map U.property.density⟩⟩

theorem gamma_volume_common_names_extend (hc : CanonicalStructure.IsCanonical (M := M))
    (hNames : commonRealNames G ⊆ T) (hTS : T ⊆ S) (U : GammaVolumeObjects G S k) :
    (U.overCommonNames hc hNames).extend hTS = U := by
  rfl

end IntegrationInACVF.Section7
