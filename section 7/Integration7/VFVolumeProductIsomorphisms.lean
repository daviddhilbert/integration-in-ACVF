module

public import Integration7.VFProductCofullDomains
public import Integration7.VFVolumeProductBijections
public import Integration7.VFVolumeIsomorphisms

@[expose] public section

/-! Actual almost-everywhere VF volume isomorphisms respect the genuine
Cartesian product, retaining both original product densities. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n m : ℕ}

def VFVolumeIso.prod
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U U' : PositiveVFVolumeObject (M := M) (C.base : Set M) n}
    {V V' : PositiveVFVolumeObject (M := M) (C.base : Set M) m}
    (f : VFVolumeIso U U') (g : VFVolumeIso V V') : VFVolumeIso (U.prod V) (U'.prod V') := by
  let P := (U.restrict f.source f.source_subset).prod (V.restrict g.source g.source_subset)
  let Q := (U'.restrict f.target f.target_subset).prod (V'.restrict g.target g.target_subset)
  have hP := mixed_product_domain_subset f.source_subset g.source_subset
  have hQ := mixed_product_domain_subset f.target_subset g.target_subset
  have hPS := vf_volume_product_cofull hc C U V
    (⟨f.source_subset,f.source_complement_small⟩ : VFCofull U.domain f.source)
    (⟨g.source_subset,g.source_complement_small⟩ : VFCofull V.domain g.source)
  have hQS := vf_volume_product_cofull hc C U' V'
    (⟨f.target_subset,f.target_complement_small⟩ : VFCofull U'.domain f.target)
    (⟨g.target_subset,g.target_complement_small⟩ : VFCofull V'.domain g.target)
  refine ⟨P.domain,Q.domain,hP,hQ,hPS.small,hQS.small,?_⟩
  exact ((vfVolumeProductRestrictionBijection hc C U V f.source g.source
    f.source_subset g.source_subset).symm hc C).trans hc C
      ((f.bijection.prod hc g.bijection).trans hc C
        (vfVolumeProductRestrictionBijection hc C U' V' f.target g.target
          f.target_subset g.target_subset))

end IntegrationInACVF.Section7
