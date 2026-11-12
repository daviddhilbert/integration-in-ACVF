import IntegrationSection6.GammaSelectedRVPresentations
import IntegrationSection5.StandardContractionNormalization

/-! Exact label bijections from a finite presentation of a contraction's
final pure-RV set to its native domain and its first-volume normalization. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n m k : ℕ}
variable {A : DefSet (M := M) S n m} {σ : Equiv.Perm (Fin n)}

def contractionPresentationLabelEquiv (C : StandardContraction A σ)
    (θ : Fin k → Fin C.arity) (P : GammaSelectedRVPresentation B C.target θ) :
    P.domain ≃ rvObjectDomain C.contractionObject where
  toFun u := ⟨u.val,⟨⟨(Fin.elim0,u.val),(Set.ext_iff.mp P.domain_eq u.val).mp u.property⟩,rfl⟩⟩
  invFun v := ⟨v.val,(Set.ext_iff.mp P.domain_eq v.val).mpr (by
    obtain ⟨w,hw⟩ := v.property
    have he : w.val = (Fin.elim0,v.val) := Prod.ext (Subsingleton.elim _ _) hw
    change (Fin.elim0,v.val) ∈ carrier C.target
    exact he ▸ w.property)⟩
  left_inv _ := rfl
  right_inv _ := rfl

def normalizedContractionPresentationEquiv (C : StandardContraction A σ)
    (θ : Fin k → Fin C.arity) (P : GammaSelectedRVPresentation B C.target θ) :
    P.domain ≃ rvObjectDomain C.normalizedObject :=
  (contractionPresentationLabelEquiv C θ P).trans
    (Equiv.ofBijective (toFirstVolume (Map.image (rawLabelMap C.target)) C.volumeIndex)
      (toFirstVolume_bijective _ _))

theorem normalizedContractionPresentationEquiv_value (C : StandardContraction A σ)
    (θ : Fin k → Fin C.arity) (P : GammaSelectedRVPresentation B C.target θ) (u : P.domain) :
    (normalizedContractionPresentationEquiv C θ P u).val = u.val ∘ prependVolumeIndex C.volumeIndex := rfl

end IntegrationInACVF.Section6
