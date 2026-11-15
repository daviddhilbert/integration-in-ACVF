import Integration7.RVParameterHeadProductBijections
import Integration7.RawRVProductTransfers
import Integration7.CanonicalVolumePresentations
import Integration7.GammaRVMapRestrictions

/-! The exact packed raw RV product bijection of a parameter-carrying
unary preparation, with a complete original-Gamma graph. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {S : Set M} {b l : ℕ}
variable {A : DefSet (M := M) S 1 0} {B : DefSet (M := M) S 1 b}
variable {T : SpecialBijection A B} {H : DefSet (M := M) S 1 l} {Q : DefSet (M := M) S 0 l}

namespace RVParameterSpecialPreparation

def rawHeadProductMap (L : RVParameterSpecialPreparation T H Q P) := rawRVProductTransfer L.headProductMap

theorem raw_head_product_map_bijective (L : RVParameterSpecialPreparation T H Q P) :
    Function.Bijective L.rawHeadProductMap := raw_rv_product_transfer_bijective _ L.head_product_map_bijective

theorem raw_head_product_map_value (L : RVParameterSpecialPreparation T H Q P)
    (u : Map.image (rawLabelMap (headImage L.target))) :
    (L.rawHeadProductMap u).val = Fin.append (u.val ∘ L.headParameters) (u.val ∘ L.headProjection) := by
  obtain ⟨p,hp⟩ := u.property
  have he : u = Map.toImage (rawLabelMap (headImage L.target)) p := Subtype.ext hp.symm
  subst u
  exact raw_rv_product_transfer_value L.headProductMap p

def canonicalRawHeadProductMap (hc : CanonicalStructure.IsCanonical (M := M))
    (L : RVParameterSpecialPreparation T H Q P) := canonicalRawRVMap hc L.rawHeadProductMap

theorem canonical_raw_head_product_map_bijective (hc : CanonicalStructure.IsCanonical (M := M))
    (L : RVParameterSpecialPreparation T H Q P) : Function.Bijective (L.canonicalRawHeadProductMap hc) := by
  constructor
  · intro u v he
    have h := L.raw_head_product_map_bijective.1 (Subtype.ext (congrArg Subtype.val he))
    have hv := congrArg Subtype.val h
    exact Subtype.ext hv
  · intro v
    obtain ⟨u,hu⟩ := L.raw_head_product_map_bijective.2 ⟨v.val,v.property⟩
    exact ⟨⟨u.val,u.property⟩,Subtype.ext (congrArg Subtype.val hu)⟩

theorem canonical_raw_head_product_map_gamma (hc : CanonicalStructure.IsCanonical (M := M))
    (L : RVParameterSpecialPreparation T H Q P) : RVMapGamma (L.canonicalRawHeadProductMap hc) P := by
  have hSource : GammaSetDefinable P {p : Point (M := M) 0 (1+L.arity) |
      p.2 ∈ (canonicalRawRVDomain hc (Map.image (rawLabelMap (headImage L.target)))).carrier} := by
    convert gamma_headImage L.target (L.gamma.target P L.special.chain) using 1
    ext p
    constructor
    · rintro ⟨q,hq⟩
      have he : q.val = p := Prod.ext (Subsingleton.elim _ _) hq
      exact (congrArg (fun z : Point (M := M) 0 (1+L.arity) => z ∈ carrier (headImage L.target)) he).mp q.property
    · intro hp
      exact ⟨⟨p,hp⟩,rfl⟩
  apply gamma_real_rv_map_graph hc P _
    (rvCoordinateSelectMap P.real (Fin.append L.headParameters L.headProjection)) hSource
  intro u
  have h := L.raw_head_product_map_value ⟨u.val,u.property⟩
  exact h.trans (by
    change Fin.append (u.val ∘ L.headParameters) (u.val ∘ L.headProjection) =
      u.val ∘ Fin.append L.headParameters L.headProjection
    funext j
    cases j using Fin.addCases <;> simp only [Function.comp_apply,Fin.append_left,Fin.append_right])

end RVParameterSpecialPreparation
end IntegrationInACVF.Section7
