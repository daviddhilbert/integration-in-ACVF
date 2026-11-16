module

public import Integration7.CanonicalFiniteRVObjects
public import Integration7.RVClassProductContractionValues
public import Section4.RVProductRestrictions

@[expose] public section

/-! The packed native unary head domains are exactly the product domain
of the actual canonical unary pullback objects. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point headImage pullbackObject rvObjectDomain)
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {a b : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)

theorem canonical_rv_product_domain_carrier (hc : CanonicalStructure.IsCanonical (M := M))
    (A : @DefSet LRV M N (@rawRVSpace M N a) S)
    (B : @DefSet LRV M N (@rawRVSpace M N b) S) :
    (canonicalRawRVDomain hc (@rvProductDomain M N S a b A B)).carrier =
      (rvProductDomain (canonicalRawRVDomain hc A) (canonicalRawRVDomain hc B)).carrier := by
  ext z
  constructor
  · intro hz
    obtain ⟨u,hu,v,hv,he⟩ := (@mem_rvProductDomain M N S a b A B z).mp hz
    exact (mem_rvProductDomain _ _ z).mpr ⟨u,hu,v,hv,he⟩
  · intro hz
    obtain ⟨u,hu,v,hv,he⟩ := (mem_rvProductDomain _ _ z).mp hz
    exact (@mem_rvProductDomain M N S a b A B z).mpr ⟨u,hu,v,hv,he⟩

theorem canonical_unary_head_product_domain (hc : CanonicalStructure.IsCanonical (M := M))
    (D : SpecialTransformations.Section5.DefSet (M := M) S 1 a)
    (E : SpecialTransformations.Section5.DefSet (M := M) S 1 b) :
    (canonicalRawRVDomain hc (@rvProductDomain M N S (1+a) (1+b)
      (SpecialTransformations.Section5.Map.image (rawLabelMap (headImage D)))
      (SpecialTransformations.Section5.Map.image (rawLabelMap (headImage E))))).carrier =
    (rvProductObject (canonicalRVObject hc (pullbackObject D))
      (canonicalRVObject hc (pullbackObject E))).domain.carrier := by
  ext z
  constructor
  · intro hz
    obtain ⟨u,hu,v,hv,he⟩ := (@mem_rvProductDomain M N S (1+a) (1+b) _ _ z).mp hz
    apply (mem_rvProductDomain _ _ z).mpr
    exact ⟨u,(unary_head_raw_label_image_eq_key_image D).le hu,
      v,(unary_head_raw_label_image_eq_key_image E).le hv,he⟩
  · intro hz
    obtain ⟨u,hu,v,hv,he⟩ := (mem_rvProductDomain _ _ z).mp hz
    apply (@mem_rvProductDomain M N S (1+a) (1+b) _ _ z).mpr
    exact ⟨u,(unary_head_raw_label_image_eq_key_image D).ge hu,
      v,(unary_head_raw_label_image_eq_key_image E).ge hv,he⟩

def canonicalUnaryHeadProductProjection (hc : CanonicalStructure.IsCanonical (M := M))
    (D : SpecialTransformations.Section5.DefSet (M := M) S 1 a)
    (E : SpecialTransformations.Section5.DefSet (M := M) S 1 b) :=
  Map.inclusion (canonical_unary_head_product_domain hc D E).le

theorem canonical_unary_head_product_projection_bijective (hc : CanonicalStructure.IsCanonical (M := M))
    (D : SpecialTransformations.Section5.DefSet (M := M) S 1 a)
    (E : SpecialTransformations.Section5.DefSet (M := M) S 1 b) :
    Function.Bijective (canonicalUnaryHeadProductProjection hc D E) := by
  constructor
  · intro u v he
    have hv := congrArg Subtype.val he
    exact Subtype.ext hv
  · intro v
    exact ⟨⟨v.val,(canonical_unary_head_product_domain hc D E).ge v.property⟩,Subtype.ext rfl⟩

end IntegrationInACVF.Section7
