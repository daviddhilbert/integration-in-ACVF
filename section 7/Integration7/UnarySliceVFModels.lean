import Integration7.UnaryContractionVolumeMaps
import Integration7.FiniteVFBaseProjection
import Integration7.VFVolumeParameterExtension

/-! Actual Jacobian-one VF models for the two selected slice charts:
the restricted contraction natural map and the prepared VF-base map. -/

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
variable {S R : Set M} {a l : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)

def unarySliceContractionVFModel
    {U : SpecialTransformations.Section5.DefSet (M := M) S 1 a}
    {σ : Equiv.Perm (Fin 1)} (T : StandardContraction U σ) (hSR : S ⊆ R)
    (L : SpecialTransformations.Section5.DefSet (M := M) R 1 a) (hL : carrier L ⊆ carrier U) :
    SpecialTransformations.Section5.Map L (extendBase (typedLift T.normalizedObject) hSR) :=
  @Map.comp LRV M N _ _ _ R L (extendBase U hSR) _
    (@Map.extend LRV M N _ _ S R _ _ (typedContractionNaturalMap T) hSR)
    (@Map.inclusion LRV M N _ R (extendBase U hSR) L hL)

theorem unarySliceContractionVFModel_value
    {U : SpecialTransformations.Section5.DefSet (M := M) S 1 a}
    {σ : Equiv.Perm (Fin 1)} (T : StandardContraction U σ) (hSR : S ⊆ R)
    (L : SpecialTransformations.Section5.DefSet (M := M) R 1 a) (hL : carrier L ⊆ carrier U) (p : L) :
    (unarySliceContractionVFModel T hSR L hL p).val =
      (T.normalizedNaturalLiftMap ⟨p.val,hL p.property⟩).val := rfl

theorem unarySliceContractionVFModel_jacobian_one
    (hc : CanonicalStructure.IsCanonical (M := M)) (C D : BaseContext M)
    {U : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 a}
    {σ : Equiv.Perm (Fin 1)} (T : StandardContraction U σ)
    (hCD : (C.base : Set M) ⊆ (D.base : Set M))
    (L : SpecialTransformations.Section5.DefSet (M := M) (D.base : Set M) 1 a)
    (hL : carrier L ⊆ carrier U) :
    VFAlmostEverywhere (rawSpecialSet hc L)
      (fun p => HasMixedVFJacobianAt (rawSpecialMap hc (unarySliceContractionVFModel T hCD L hL)) p 1) := by
  let i := @Map.inclusion LRV M N _ (D.base : Set M) (extendBase U hCD) L hL
  let g := @Map.extend LRV M N _ _ (C.base : Set M) (D.base : Set M) _ _ (typedContractionNaturalMap T) hCD
  have hi : Function.Injective i := by
    intro p q he
    exact Subtype.ext (congrArg (fun z => z.val) he)
  exact vfJacobianOne_comp hc D Nat.one_pos (rawSpecialMap hc i) (rawSpecialMap hc g) hi
    (vfJacobianOne_of_preservesVF hc D Nat.one_pos (rawSpecialMap hc i) (fun _ => rfl))
    ((standard_unary_typed_natural_jacobian_one hc C T).extend hCD)

def unarySlicePreparedVFModel
    {A : SpecialTransformations.Section5.DefSet (M := M) S 1 0}
    {Z : SpecialTransformations.Section5.DefSet (M := M) S 1 l}
    (K : SpecialBijection A Z) (hSR : S ⊆ R)
    (L : SpecialTransformations.Section5.DefSet (M := M) R 1 a)
    (hBase : ∀ p : L, (p.val.1,Fin.elim0) ∈ carrier A) :
    SpecialTransformations.Section5.Map L (extendBase Z hSR) :=
  @Map.comp LRV M N _ _ _ R L (extendBase A hSR) (extendBase Z hSR)
    (@Map.extend LRV M N _ _ S R A Z K.toMap hSR)
    (vfBaseProjection L (extendBase A hSR) hBase)

theorem unarySlicePreparedVFModel_value
    {A : SpecialTransformations.Section5.DefSet (M := M) S 1 0}
    {Z : SpecialTransformations.Section5.DefSet (M := M) S 1 l}
    (K : SpecialBijection A Z) (hSR : S ⊆ R)
    (L : SpecialTransformations.Section5.DefSet (M := M) R 1 a)
    (hBase : ∀ p : L, (p.val.1,Fin.elim0) ∈ carrier A) (p : L) :
    (unarySlicePreparedVFModel K hSR L hBase p).val =
      (K.toMap ⟨(p.val.1,Fin.elim0),hBase p⟩).val := by
  apply congrArg (fun q : A => (K.toMap q).val)
  exact Subtype.ext (vfBaseProjection_value L (extendBase A hSR) hBase p)

theorem unarySlicePreparedVFModel_jacobian_one
    (hc : CanonicalStructure.IsCanonical (M := M)) (C D : BaseContext M)
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 0}
    {Z : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 l}
    (K : SpecialBijection A Z) (hCD : (C.base : Set M) ⊆ (D.base : Set M))
    (L : SpecialTransformations.Section5.DefSet (M := M) (D.base : Set M) 1 a)
    (hBase : ∀ p : L, (p.val.1,Fin.elim0) ∈ carrier A)
    (hfin : ∀ x : Fin 1 → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier L}.Finite) :
    VFAlmostEverywhere (rawSpecialSet hc L)
      (fun p => HasMixedVFJacobianAt (rawSpecialMap hc (unarySlicePreparedVFModel K hCD L hBase)) p 1) :=
  vfJacobianOne_comp_finiteFibres hc D Nat.one_pos
    (rawSpecialMap hc (vfBaseProjection L (extendBase A hCD) hBase))
    (rawSpecialMap hc (@Map.extend LRV M N _ _ (C.base : Set M) (D.base : Set M) A Z K.toMap hCD))
    (vfBaseProjection_finiteFibres L (extendBase A hCD) hBase hfin)
    (vfJacobianOne_of_preservesVF hc D Nat.one_pos
      (rawSpecialMap hc (vfBaseProjection L (extendBase A hCD) hBase)) (fun _ => rfl))
    (((special_vf_jacobian_one hc C Nat.one_pos K).1).extend hCD)

end IntegrationInACVF.Section7
