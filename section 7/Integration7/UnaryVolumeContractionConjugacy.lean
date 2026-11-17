module

public import Integration7.UnaryContractionVolumeMaps
public import Integration7.RawVFVolumeComposition
public import IntegrationSection5.MapInverseBijection

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Conjugating a measure-preserving unary bijection by arbitrary chosen
standard contractions. The forms on the two normalized lifts are the
actual transported forms; no equality of pointwise Jacobian values on
exceptional fibres is used. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {a b : ℕ}

def unaryContractionConjugate
    {A : SpecialTransformations.Section5.DefSet (M := M) S 1 a}
    {B : SpecialTransformations.Section5.DefSet (M := M) S 1 b}
    (f : SpecialTransformations.Section5.Map A B)
    {σ τ : Equiv.Perm (Fin 1)} (T : StandardContraction A σ) (E : StandardContraction B τ) :
    SpecialTransformations.Section5.Map (typedLift T.normalizedObject) (typedLift E.normalizedObject) :=
  SpecialTransformations.Section5.Map.comp (typedContractionNaturalMap E)
    (SpecialTransformations.Section5.Map.comp f
      (SpecialTransformations.Section5.Map.inverse (typedContractionNaturalMap T)
        (typedContractionNaturalMap_bijective T)))

theorem unaryContractionConjugate_bijective
    {A : SpecialTransformations.Section5.DefSet (M := M) S 1 a}
    {B : SpecialTransformations.Section5.DefSet (M := M) S 1 b}
    (f : SpecialTransformations.Section5.Map A B) (hf : Function.Bijective f)
    {σ τ : Equiv.Perm (Fin 1)} (T : StandardContraction A σ) (E : StandardContraction B τ) :
    Function.Bijective (unaryContractionConjugate f T E) :=
  (typedContractionNaturalMap_bijective E).comp
    (hf.comp (inverse_map_bijective _ (typedContractionNaturalMap_bijective T)))

set_option maxHeartbeats 1600000 in
theorem unary_contraction_conjugate_preserves_volume
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 a}
    {B : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 b}
    (f : SpecialTransformations.Section5.Map A B) (hf : Function.Bijective f)
    (ω : VolumeForm (rawSpecialSet hc A)) (π : VolumeForm (rawSpecialSet hc B))
    (hm : PreservesVFVolume ω π (rawSpecialMap hc f))
    {σ τ : Equiv.Perm (Fin 1)} (T : StandardContraction A σ) (E : StandardContraction B τ) :
    PreservesVFVolume (unaryContractionLiftForm hc T ω) (unaryContractionLiftForm hc E π)
      (rawSpecialMap hc (unaryContractionConjugate f T E)) := by
  let t := typedContractionNaturalMap T
  let ti := SpecialTransformations.Section5.Map.inverse t (typedContractionNaturalMap_bijective T)
  let e := typedContractionNaturalMap E
  let tr := rawSpecialMap hc t
  let tir := rawSpecialMap hc ti
  let er := rawSpecialMap hc e
  have htbij : Function.Bijective tr := typedContractionNaturalMap_bijective T
  have htibij : Function.Bijective tir := inverse_map_bijective t (typedContractionNaturalMap_bijective T)
  have hi : tr.inverse htbij = tir := by
    apply SpecialTransformations.DefinableGeometry.Map.ext
    intro q
    apply htbij.1
    have hleft := Map.apply_inverse tr htbij q
    have hright : tr (tir q) = q := Map.apply_inverse t (typedContractionNaturalMap_bijective T) q
    exact hleft.trans hright.symm
  have ht := unary_contraction_natural_preserves_volume hc C T ω
  have he := unary_contraction_natural_preserves_volume hc C E π
  have hti := preservesVFVolume_inverse hc C Nat.one_pos ω (unaryContractionLiftForm hc T ω)
    tr htbij ht
  rw [hi] at hti
  have hmiddle := preservesVFVolume_comp hc C Nat.one_pos (unaryContractionLiftForm hc T ω) ω π
    tir (rawSpecialMap hc f) htibij.1 hti hm
  change PreservesVFVolume (unaryContractionLiftForm hc T ω) (unaryContractionLiftForm hc E π)
    (er.comp ((rawSpecialMap hc f).comp tir))
  exact preservesVFVolume_comp hc C Nat.one_pos (unaryContractionLiftForm hc T ω) π
    (unaryContractionLiftForm hc E π) ((rawSpecialMap hc f).comp tir) er
    (hf.1.comp htibij.1) hmiddle he

end IntegrationInACVF.Section7
