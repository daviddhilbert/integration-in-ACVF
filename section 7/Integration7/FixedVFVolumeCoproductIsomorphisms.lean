module

public import Integration7.FixedVFVolumeCoproductRestrictions
public import Integration7.FixedVFTagCofullDomains
public import Integration7.VFVolumeIsomorphisms

@[expose] public section

/-! Almost-everywhere volume isomorphisms are compatible with disjoint
unions in their original VF degree. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

def VFVolumeIso.coprod
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U U' V V' : PositiveVFVolumeObject (M := M) (C.base : Set M) k}
    (f : VFVolumeIso U U') (g : VFVolumeIso V V') :
    VFVolumeIso (U.coprod V) (U'.coprod V') := by
  let P := (U.restrict f.source f.source_subset).coprod (V.restrict g.source g.source_subset)
  let Q := (U'.restrict f.target f.target_subset).coprod (V'.restrict g.target g.target_subset)
  have hP := vf_volume_coprod_restrict_subset U V f.source g.source f.source_subset g.source_subset
  have hQ := vf_volume_coprod_restrict_subset U' V' f.target g.target f.target_subset g.target_subset
  have hPS : VFCofull (U.coprod V).domain P.domain :=
    (fixed_vf_left_tag_cofull (⟨f.source_subset,f.source_complement_small⟩ : VFCofull U.domain f.source)
      V.arity).union hc C
    (fixed_vf_right_tag_cofull (⟨g.source_subset,g.source_complement_small⟩ : VFCofull V.domain g.source)
      U.arity)
  have hQS : VFCofull (U'.coprod V').domain Q.domain :=
    (fixed_vf_left_tag_cofull (⟨f.target_subset,f.target_complement_small⟩ : VFCofull U'.domain f.target)
      V'.arity).union hc C
    (fixed_vf_right_tag_cofull (⟨g.target_subset,g.target_complement_small⟩ : VFCofull V'.domain g.target)
      U'.arity)
  refine ⟨P.domain,Q.domain,hP,hQ,hPS.small,hQS.small,?_⟩
  exact ((vfVolumeCoprodRestrictionBijection hc C U V f.source g.source
    f.source_subset g.source_subset).symm hc C).trans hc C
      ((f.bijection.coprod hc C g.bijection).trans hc C
        (vfVolumeCoprodRestrictionBijection hc C U' V' f.target g.target
          f.target_subset g.target_subset))

end IntegrationInACVF.Section7
