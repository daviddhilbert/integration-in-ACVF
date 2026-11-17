module

public import Integration7.GammaRVCommonNames
public import Integration7.GammaVolumeObjectGraphs

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Reinterpret literal RV carriers and functions over any real base
containing the common names of their original Gamma graphs. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S T : Set M} {a b : ℕ}

def gammaRVMapDomainRebase (hc : CanonicalStructure.IsCanonical (M := M))
    (hNames : commonRealNames G ⊆ T)
    {A : DefSet (rawRVSpace (M := M) a) S} {B : DefSet (rawRVSpace (M := M) b) S}
    (f : Map A B) (hf : RVMapGamma f G) : DefSet (rawRVSpace (M := M) a) T := by
  let P := rawRVSpace (M := M) a
  let Q := rawRVSpace (M := M) b
  have h := gamma_raw_rv_relation_common_names hc hNames hf
  refine ⟨A.carrier,?_⟩
  convert h.exists_right P Q using 1
  ext x
  constructor
  · intro hx
    exact ⟨(f ⟨x,hx⟩).val,⟨x,hx⟩,rfl,rfl⟩
  · rintro ⟨y,u,rfl,_⟩
    exact u.property

def gammaRVMapRebase (hc : CanonicalStructure.IsCanonical (M := M))
    (hNames : commonRealNames G ⊆ T)
    {A : DefSet (rawRVSpace (M := M) a) S} {B : DefSet (rawRVSpace (M := M) b) S}
    (f : Map A B) (hf : RVMapGamma f G) :
    Map (gammaRVMapDomainRebase hc hNames f hf) (DefSet.univ (rawRVSpace (M := M) b) T) := by
  refine ⟨fun u => ⟨(f ⟨u.val,u.property⟩).val,Set.mem_univ _⟩,?_⟩
  exact gamma_raw_rv_relation_common_names hc hNames hf

theorem gamma_rv_map_rebase_graph (hc : CanonicalStructure.IsCanonical (M := M))
    (hNames : commonRealNames G ⊆ T)
    {A : DefSet (rawRVSpace (M := M) a) S} {B : DefSet (rawRVSpace (M := M) b) S}
    (f : Map A B) (hf : RVMapGamma f G) : RVMapGamma (gammaRVMapRebase hc hNames f hf) G := hf

end IntegrationInACVF.Section7
