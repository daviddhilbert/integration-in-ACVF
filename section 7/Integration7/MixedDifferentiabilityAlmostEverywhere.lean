module

public import Integration7.MixedBijectiveJacobianNonzero
public import Section9.MixedDerivativeFormula

@[expose] public section

/-! Full mixed differentiability holds away from a definable set of
smaller VF dimension, over the original real parameter base. -/
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b : ℕ}

theorem mixed_differentiability_almost_everywhere
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (hn : 0 < n)
    {A : DefSet (rawMixedSpace (M := M) n a) (C.base : Set M)}
    {B : DefSet (rawMixedSpace (M := M) n b) (C.base : Set M)} (f : Map A B) :
    VFAlmostEverywhere A (fun p => ∃ L, HasMixedVFDerivativeAt f p L) := by
  letI : CharZero (VFType (M := M)) := Section6.vfCharZero_of_model00 C.model00
  letI : Valued (VFType (M := M)) (Values.presentationType (M := M)) :=
    Valued.mk' Values.presentationValuation
  let D : DefSet (rawMixedSpace (M := M) n a) (C.base : Set M) :=
    ⟨{x | ∃ p : A, p.val = x ∧ ∃ L, HasMixedVFDerivativeAt f p L},
      mixedDifferentiabilityLocus_definable hn f⟩
  let E := A.sdiff D
  refine ⟨E,Set.sdiff_subset,?_,?_⟩
  · apply mixed_vfDim_lt_of_no_independent hc C.saturated C.small _ (rawRVSpace_rvCoded 1) hn
    intro p hp
    let q : A := ⟨p.val,p.property.1⟩
    obtain ⟨L,hL⟩ := mixedDifferentiableAt_of_independent hc C.uncountable.le C.saturated C.small
      Values.presentation_compatible f q hp
    exact p.property.2 ⟨q,rfl,L,hL⟩
  · intro p hp
    have hD : p.val ∈ D.carrier := by
      by_contra h
      exact hp ⟨p.property,h⟩
    obtain ⟨q,hq,L,hL⟩ := hD
    have he : q = p := Subtype.ext hq
    exact ⟨L,he ▸ hL⟩

end IntegrationInACVF.Section7
