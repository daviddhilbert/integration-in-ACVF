module

public import Integration7.GammaVolumeCommonNameRebasing
public import Integration7.RVVolumeIsomorphismDescent
public import Integration7.NondegenerateFiniteIso

@[expose] public section

/-! The original-Gamma essential bijection is defined over the common
names, and its two volume laws descend to that same real context. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {k : ℕ}

def gammaVolumeIsoOverCommonNames
    (hc : CanonicalStructure.IsCanonical (M := M)) (C D : BaseContext M)
    (hCD : (C.base : Set M) ⊆ (D.base : Set M))
    (hNames : commonRealNames G ⊆ (C.base : Set M))
    (U V : GammaVolumeObjects G (D.base : Set M) k)
    (f : RVVolumeIso U.val V.val) (hf : f.GammaDefinable G) :
    RVVolumeIso (U.overCommonNames hc hNames).val (V.overCommonNames hc hNames).val := by
  let UC := (U.overCommonNames hc hNames).val
  let VC := (V.overCommonNames hc hNames).val
  let F : Map UC.essential.obj.domain VC.essential.obj.domain :=
    ⟨fun u => ⟨(finiteIsoMap f.iso ⟨u.val,u.property⟩).val,
      (finiteIsoMap f.iso ⟨u.val,u.property⟩).property⟩,
      gamma_raw_rv_relation_common_names hc hNames hf⟩
  have hF : Function.Bijective F := finiteIsoMap_bijective f.iso
  let e := finiteIsoOfNondegenerateBijection F hF UC.essential_nonzero VC.essential_nonzero
  exact RVVolumeIso.descend hc C D hCD f e (fun _ => rfl)

theorem gamma_volume_iso_over_common_names_graph
    (hc : CanonicalStructure.IsCanonical (M := M)) (C D : BaseContext M)
    (hCD : (C.base : Set M) ⊆ (D.base : Set M))
    (hNames : commonRealNames G ⊆ (C.base : Set M))
    (U V : GammaVolumeObjects G (D.base : Set M) k)
    (f : RVVolumeIso U.val V.val) (hf : f.GammaDefinable G) :
    (gammaVolumeIsoOverCommonNames hc C D hCD hNames U V f hf).GammaDefinable G := hf

end IntegrationInACVF.Section7
