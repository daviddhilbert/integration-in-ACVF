import Integration7.ContractionParameterExtension
import Integration7.ContractionRetainedDensityLabels

/-! Enlarging parameters changes neither the normalized contraction
labels nor their actual carrier. Every chosen contraction coordinate is
retained, so later density and selected-volume transports are literal. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Section4.vfSpace
  SpecialTransformations.Section4.rvSpace SpecialTransformations.Milestone0.sortEval
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section5
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S R : Set M} {n a : ℕ} {A : DefSet (M := M) S n a} {σ : Equiv.Perm (Fin n)}

theorem StandardContraction.extendBase_normalized_value
    (T : StandardContraction A σ) (hSR : S ⊆ R) (p : SpecialTransformations.Section5.extendBase A hSR) :
    ((T.extendBase hSR).normalizedContractionMap p).val =
      (T.normalizedContractionMap ⟨p.val,p.property⟩).val := by
  have hv := congrArg (fun q : Point (M := M) 0 T.arity => q.2) (T.extendBase_value hSR p)
  funext j
  change ((T.extendBase hSR).toMap p).val.2 (prependVolumeIndex (T.extendBase hSR).volumeIndex j) =
    (T.toMap ⟨p.val,p.property⟩).val.2 (prependVolumeIndex T.volumeIndex j)
  have hi : (T.extendBase hSR).volumeIndex = T.volumeIndex :=
    funext (T.extendBase_volumeIndex hSR)
  have hidx := congrFun (congrArg (fun ρ : Fin n → Fin T.arity => prependVolumeIndex ρ) hi) j
  exact (congrArg ((T.extendBase hSR).toMap p).val.2 hidx).trans
    (congrFun hv (prependVolumeIndex T.volumeIndex j))

theorem StandardContraction.extendBase_normalized_domain
    (T : StandardContraction A σ) (hSR : S ⊆ R) :
    carrier (rvObjectDomain (T.extendBase hSR).normalizedObject) = carrier (rvObjectDomain T.normalizedObject) := by
  ext w
  constructor
  · intro hw
    obtain ⟨p,hp⟩ := IntegrationInACVF.Section7.standard_normalized_contraction_map_surjective
      (T.extendBase hSR) ⟨w,hw⟩
    have he := (T.extendBase_normalized_value hSR p).symm.trans (congrArg Subtype.val hp)
    exact (congrArg (fun r : Fin (n+T.arity) → RV (M := M) =>
      r ∈ carrier (rvObjectDomain T.normalizedObject)) he).mp
        (T.normalizedContractionMap ⟨p.val,p.property⟩).property
  · intro hw
    obtain ⟨p,hp⟩ := IntegrationInACVF.Section7.standard_normalized_contraction_map_surjective T ⟨w,hw⟩
    let p' : SpecialTransformations.Section5.extendBase A hSR := ⟨p.val,p.property⟩
    have he := (T.extendBase_normalized_value hSR p').trans (congrArg Subtype.val hp)
    exact (congrArg (fun r : Fin (n+T.arity) → RV (M := M) =>
      r ∈ carrier (rvObjectDomain (T.extendBase hSR).normalizedObject)) he).mp
        ((T.extendBase hSR).normalizedContractionMap p').property

end IntegrationInACVF.Section5
