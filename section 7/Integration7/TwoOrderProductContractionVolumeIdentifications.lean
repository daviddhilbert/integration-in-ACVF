module

public import Integration7.FixedLabelContractionVolumeObjects
public import Integration7.TwoOrderProductCommonNames
public import Integration7.TwoOrderProductNormalizedGammaObjects
public import Integration7.TwoOrderProductProgramCertificates

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The retained-density normalized objects used by arbitrary-contraction
comparison equal the actual normalized constant-density product objects. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.TwoOrderProductPreparations
set_option allowUnsafeReducibility true in
attribute [local reducible] PositiveRVVolumeObject.essential
  SpecialTransformations.Section9.rvFiniteEssential SpecialTransformations.Section9.rvEssential
  SpecialTransformations.Section4.RVObject.restrict headNormalizedVolumeObject tailNormalizedVolumeObject
  normalizedUnitVolumeContraction canonicalNormalizedFiniteContraction canonicalRVObject
  PositiveRVVolumeObject.rescale

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {S : Set M} {d : ℕ}
variable {X Y : DefSet (M := M) S 2 0} {D E : DefSet (M := M) S 1 0}
variable {r t : RV (M := M)} {z : Fin d → RV (M := M)} {hz : ∀ j, (z j).val ∈ S}

theorem head_fixed_label_contraction_object {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk P.real < κ)
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F : TwoOrderProductPreparations X Y D E r t z hz P)
    (hSC : S ⊆ (C.base : Set M)) (hNames : commonRealNames P ⊆ (C.base : Set M))
    (hPS : P.real ⊆ S) (hX : GammaSetDefinable P (carrier X))
    (hzΓ : DefinableOverBase P (fun _ : Fin d => .rv) {fun j => (z j).val})
    (hr : r.val ∈ S) (η : RV (M := M)) (hη : η.val ∈ S) (hη0 : η ≠ 0)
    (j : Fin d) (hj : z j = η) :
    let G := F.present hSC hNames
    fixedLabelContractionGammaObject hκ hs hsmall hc C (hPS.trans hSC)
      (extendBase X hSC) hX z (fun j => hSC (hz j)) hzΓ j η hj hη0
      G.headContraction (G.head_contraction_gamma hX hzΓ) =
    G.headNormalizedGammaObject hκ hs hsmall hc (hPS.trans hSC) (hSC hr) η (hSC hη) hη0 j hj := by
  intro G
  apply Subtype.ext
  obtain ⟨hε,heq⟩ := G.head_normalized_coordinate_density hκ hs hsmall hc (hSC hr) η (hSC hη) hη0 j hj
  exact heq

theorem tail_fixed_label_contraction_object {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk P.real < κ)
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F : TwoOrderProductPreparations X Y D E r t z hz P)
    (hSC : S ⊆ (C.base : Set M)) (hNames : commonRealNames P ⊆ (C.base : Set M))
    (hPS : P.real ⊆ S) (hY : GammaSetDefinable P (carrier Y))
    (hzΓ : DefinableOverBase P (fun _ : Fin d => .rv) {fun j => (z j).val})
    (ht : t.val ∈ S) (η : RV (M := M)) (hη : η.val ∈ S) (hη0 : η ≠ 0)
    (j : Fin d) (hj : z j = η) :
    let G := F.present hSC hNames
    fixedLabelContractionGammaObject hκ hs hsmall hc C (hPS.trans hSC)
      (extendBase Y hSC) hY z (fun j => hSC (hz j)) hzΓ j η hj hη0
      G.tailContraction (G.tail_contraction_gamma hY hzΓ) =
    G.tailNormalizedGammaObject hκ hs hsmall hc (hPS.trans hSC) (hSC ht) η (hSC hη) hη0 j hj := by
  intro G
  apply Subtype.ext
  obtain ⟨hε,heq⟩ := G.tail_normalized_coordinate_density hκ hs hsmall hc (hSC ht) η (hSC hη) hη0 j hj
  exact heq

end IntegrationInACVF.Section7.TwoOrderProductPreparations
