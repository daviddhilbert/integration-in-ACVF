module

public import Integration7.GammaVolumeRestrictionIdentities
public import Integration7.VolumeEmbeddedImages
public import Integration7.EssentialVolumeRestriction

@[expose] public section

/-! Actual essential embeddings, tagged images and restrictions
containing the essential part retain their full original-Gamma charts. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaSetDefinable)

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ} {B : Base (M := M)}

theorem gamma_volume_essential_embedding_iso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (i : Map U.essential.obj.domain V.essential.obj.domain) (hi : Function.Injective i)
    (hcoord : ∀ u, V.essential.obj.value (i u) = U.essential.obj.value u)
    (hφ : ∀ u, V.essentialForm.value (i u) = U.essentialForm.value u)
    (hiΓ : RVMapGamma i B) :
    (volumeIsoOfEssentialEmbedding hc C i hi hcoord hφ).GammaDefinable B :=
  hiΓ.congr (fun _ => rfl)

theorem gamma_coprod_essential_left_map {S : Set M}
    (hc : CanonicalStructure.IsCanonical (M := M))
    (U V : PositiveRVVolumeObject (M := M) S k) (hU : VolumeObjectGamma U B) :
    RVMapGamma (coprodEssentialLeftMap U V) B :=
  (gamma_rv_left_tag_map hc _ V.underlying.obj.arity
    (gamma_essential_volume_domain U hU.coordinates)).congr (fun _ => rfl)

theorem gamma_coprod_essential_right_map {S : Set M}
    (hc : CanonicalStructure.IsCanonical (M := M))
    (U V : PositiveRVVolumeObject (M := M) S k) (hV : VolumeObjectGamma V B) :
    RVMapGamma (coprodEssentialRightMap U V) B :=
  (gamma_rv_right_tag_map hc _ U.underlying.obj.arity
    (gamma_essential_volume_domain V hV.coordinates)).congr (fun _ => rfl)

theorem RVMapGamma.image {S : Set M} {a b : ℕ}
    {A : DefSet (rawRVSpace (M := M) a) S} {D : DefSet (rawRVSpace (M := M) b) S}
    {f : Map A D} (hf : RVMapGamma f B) :
    GammaSetDefinable B {p : Point (M := M) 0 b | p.2 ∈ f.image.carrier} :=
  (hf.congr (g := f.toImage) (fun _ => rfl)).range (by rintro ⟨_,a,rfl⟩; exact ⟨a,rfl⟩)

theorem gamma_volume_coprod_left_image_iso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k) (hU : VolumeObjectGamma U B) :
    (volumeCoprodLeftImageIso hc C U V).GammaDefinable B :=
  (gamma_coprod_essential_left_map hc U V hU).congr (fun _ => rfl)

theorem gamma_volume_coprod_right_image_iso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k) (hV : VolumeObjectGamma V B) :
    (volumeCoprodRightImageIso hc C U V).GammaDefinable B :=
  (gamma_coprod_essential_right_map hc U V hV).congr (fun _ => rfl)

theorem gamma_containing_essential_restriction_iso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) (hU : VolumeObjectGamma U B)
    (A : DefSet (rawRVSpace (M := M) U.underlying.obj.arity) (C.base : Set M))
    (hA : A.carrier ⊆ U.underlying.obj.domain.carrier)
    (hess : U.essential.obj.domain.carrier ⊆ A.carrier)
    (hAΓ : GammaSetDefinable B {p : Point (M := M) 0 U.underlying.obj.arity | p.2 ∈ A.carrier}) :
    (volumeIsoOfContainingEssentialRestriction hc C U A hA hess).GammaDefinable B :=
  gamma_volume_iso_of_label_identity hc _ (hU.restrict A hA hAΓ) rfl (fun _ => rfl)

end IntegrationInACVF.Section7
