import Integration7.GammaNativeCommonNames
import IntegrationSection4.DefinableDescent
import Section5.GammaInvariantLogic

/-! Full original-Gamma graphs descend through actual definable maps
when the scalar map is constant on fibres. Representative choices remain
internal to the checked definable descent construction. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section4

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S : Set M} {n m u w : ℕ}
variable {A : DefSet (M := M) S n m} {B : DefSet (M := M) S u w}

def nativeScalarDescent (q : Map A B)
    (f : Map A (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) S))
    (hf : ∀ a b, q a = q b → f a = f b) :
    Map (Map.image q) (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) S) :=
  @DefinableDescent.descendMap LRV M (CanonicalStructure.normalize (M := M)) _ _ _ S _ _ _ q f hf

theorem native_scalar_descent_value (q : Map A B)
    (f : Map A (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) S))
    (hf : ∀ a b, q a = q b → f a = f b) (a : A) :
    nativeScalarDescent q f hf (Map.toImage q a) = f a :=
  @DefinableDescent.descendMap_spec LRV M (CanonicalStructure.normalize (M := M)) _ _ _ S _ _ _ q f hf a

theorem gamma_native_scalar_descent_graph (q : Map A B)
    (f : Map A (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) S))
    (hf : ∀ a b, q a = q b → f a = f b)
    (hqΓ : GammaGraphDefinable G (pointMapGraph q))
    (hfΓ : GammaScalarGraphDefinable G (fun p z => ∃ a : A, a.val = p ∧ (f a).val 0 = z)) :
    GammaScalarGraphDefinable G (fun p z => ∃ b : Map.image q,
      b.val = p ∧ (nativeScalarDescent q f hf b).val 0 = z) := by
  have h := (gammaLogicInput G).comp_graph ((gammaLogicInput G).swap_graph hqΓ) hfΓ
  apply GammaGraphDefinable.congr h
  intro p z
  constructor
  · rintro ⟨x,⟨a,ha,hqa⟩,b,hb,hfb⟩
    have hab : a = b := Subtype.ext (ha.trans hb.symm)
    subst b
    refine ⟨Map.toImage q a,hqa,?_⟩
    rw [native_scalar_descent_value]
    exact hfb
  · rintro ⟨b,hb,hv⟩
    obtain ⟨a,ha⟩ := b.property
    have he : b = Map.toImage q a := Subtype.ext ha.symm
    subst b
    rw [native_scalar_descent_value] at hv
    exact ⟨a.val,⟨a,rfl,hb⟩,a,rfl,hv⟩

end IntegrationInACVF.Section7
