module

public import Integration7.GammaEssentialVolumeRestrictions
public import Integration7.IndexedVolumeRestrictions
public import Integration7.GammaVolumeIndexedPresentations
public import Integration7.GammaVolumePresentationGeometry

@[expose] public section

/-! An indexed volume object may discard every index with a zero base
volume coordinate. Its complete essential domain and its actual density
are preserved by an original-Gamma volume isomorphism. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.Section5 (RV)
open SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a d k : ℕ}
variable {T E : Set (Fin p → RV (M := M))}
variable {R S : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}

set_option maxHeartbeats 1600000 in
theorem indexed_volume_essential_index_restriction_iso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F : GammaRVVolumeSchema B p a k (fun _ => .rv))
    (BP : GammaFiniteGraphPresentation B p d T R) (BQ : GammaFiniteGraphPresentation B p d E S)
    (hET : E ⊆ T) (hVolume : ∀ t ∈ E, BQ.totalVolume t = BP.totalVolume t)
    (hContains : ∀ t ∈ T, (∀ i, (BP.totalVolume t i).val ≠ iRVZero) → t ∈ E)
    (hF : ∀ t ∈ T, F.valid (rvValues t))
    (P : F.IndexedPresentation BP) (Q : F.IndexedPresentation BQ)
    (hP : P.finite.codes ⊆ (C.base : Set M)) (hQ : Q.finite.codes ⊆ (C.base : Set M)) :
    ∃ e : RVVolumeIso (Q.inContext hc C hQ).toObject (P.inContext hc C hP).toObject,
      e.GammaDefinable B := by
  let U := (P.inContext hc C hP).toObject
  let V := (Q.inContext hc C hQ).toObject
  let A := V.underlying.obj.domain
  have hA : A.carrier = indexedDomain E (fun t => F.object.rowDomain (rvValues t)) :=
    GammaVolumeGraphPresentation.inContext_domain hc C Q hQ
  have hAU : A.carrier ⊆ U.underlying.obj.domain.carrier := by
    intro w hw
    obtain ⟨ht,hr⟩ := (indexedVolume_domain_iff hc C Q hQ w).mp hw
    exact (indexedVolume_domain_iff hc C P hP w).mpr ⟨hET ht,hr⟩
  have hess : U.essential.obj.domain.carrier ⊆ A.carrier := by
    intro w hw
    obtain ⟨ht,hNZ,hr⟩ := (indexedVolume_essential_domain_iff hc C P hP hF w).mp hw
    have hr' := (essentialFiniteVolumeSchema_rowDomain F.object _ _).mp hr
    exact (indexedVolume_domain_iff hc C Q hQ w).mpr
      ⟨hContains _ ht hNZ,(hF _ ht).1.2.2.1 _ _ hr'.choose_spec.1⟩
  let eR := indexedVolumeRestrictionIso hc C F BP BQ hET hVolume P Q hP hQ A hA hAU
  have heR : eR.GammaDefinable B :=
    gamma_volume_iso_of_label_identity hc eR (Q.gamma_object hc C hQ) rfl (fun _ => rfl)
  let eD := volumeIsoOfContainingEssentialRestriction hc C U A hAU hess
  have heD : eD.GammaDefinable B := gamma_volume_containing_essential_restriction_iso hc C U
    (P.gamma_object hc C hP) A hAU hess (Q.gamma_object hc C hQ).domain_graph
  exact ⟨eR.trans hc C eD,heR.trans hc C B heD⟩

end IntegrationInACVF.Section7
