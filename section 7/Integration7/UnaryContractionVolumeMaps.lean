import Integration7.UnaryNaturalVolumeJacobians
import Integration7.VolumeForms
import IntegrationSection6.ContractionNaturalContractibility

/-! An arbitrary unary standard contraction is an actual
volume-preserving bijection to its normalized lift with transported form.
Retained density labels agree with the original old-label coordinates. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {a : ℕ}

theorem standard_unary_typed_natural_jacobian_one
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 a}
    {σ : Equiv.Perm (Fin 1)} (T : StandardContraction A σ) :
    VFAlmostEverywhere (rawSpecialSet hc A)
      (fun p => HasMixedVFJacobianAt (rawSpecialMap hc (typedContractionNaturalMap T)) p 1) :=
  vfJacobianOne_of_same_vf hc C Nat.one_pos (rawSpecialMap hc T.naturalMap) _ (fun _ => rfl)
    (standard_unary_natural_jacobian_one hc C T)

def unaryContractionLiftForm
    (hc : CanonicalStructure.IsCanonical (M := M))
    {A : SpecialTransformations.Section5.DefSet (M := M) S 1 a}
    {σ : Equiv.Perm (Fin 1)} (T : StandardContraction A σ) (ω : VolumeForm (rawSpecialSet hc A)) :
    VolumeForm (rawSpecialSet hc (typedLift T.normalizedObject)) :=
  ω.pullback ((rawSpecialMap hc (typedContractionNaturalMap T)).inverse
    (typedContractionNaturalMap_bijective T))

theorem unaryContractionLiftForm_density
    (hc : CanonicalStructure.IsCanonical (M := M))
    {A : SpecialTransformations.Section5.DefSet (M := M) S 1 a}
    {σ : Equiv.Perm (Fin 1)} (T : StandardContraction A σ) (ω : VolumeForm (rawSpecialSet hc A))
    (δ : Fin a) (hDensity : ∀ p, ω.value p = p.val.2 δ)
    (q : rawSpecialSet hc (typedLift T.normalizedObject)) :
    (unaryContractionLiftForm hc T ω).value q = q.val.2 (FiniteRV.contractionOldLabelIndex T δ) := by
  let f := rawSpecialMap hc (typedContractionNaturalMap T)
  let hf := typedContractionNaturalMap_bijective T
  let p := f.inverse hf q
  have hOld : (f p).val.2 (FiniteRV.contractionOldLabelIndex T δ) = p.val.2 δ :=
    (congrArg (fun r => r (FiniteRV.contractionOldLabelIndex T δ)) (T.normalizedNaturalLiftMap_square p)).trans
      (FiniteRV.contraction_oldLabels T p δ)
  change ω.value p = q.val.2 (FiniteRV.contractionOldLabelIndex T δ)
  exact (hDensity p).trans (hOld.symm.trans
    (congrArg (fun z => z.val.2 (FiniteRV.contractionOldLabelIndex T δ)) (Map.apply_inverse f hf q)))

theorem unary_contraction_natural_preserves_volume
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 a}
    {σ : Equiv.Perm (Fin 1)} (T : StandardContraction A σ) (ω : VolumeForm (rawSpecialSet hc A)) :
    PreservesVFVolume ω (unaryContractionLiftForm hc T ω) (rawSpecialMap hc (typedContractionNaturalMap T)) := by
  apply (standard_unary_typed_natural_jacobian_one hc C T).mono
  intro p hJ
  refine ⟨1,hJ,?_⟩
  rw [RVOperations.rv_one,mul_one]
  change ω.value p = ω.value (((rawSpecialMap hc (typedContractionNaturalMap T)).inverse
    (typedContractionNaturalMap_bijective T)) ((rawSpecialMap hc (typedContractionNaturalMap T)) p))
  rw [SpecialTransformations.DefinableGeometry.Map.inverse_apply]

end IntegrationInACVF.Section7
