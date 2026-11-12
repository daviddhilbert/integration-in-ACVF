import IntegrationSection6.FiniteGammaRestrictions
import Section7.GammaScissors

/-! Companion graphs retain literal volume information when comparing
actual finite subobjects. This exposes the inherited scissor presentation
without changing its objects or relations. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {k : ℕ}

abbrev GammaCompanionPoint (M : Type) [LRV.Structure M] (k : ℕ) :=
  Option (Σ a : ℕ, (Fin a → RV (M := M)) × (Fin k → RV (M := M)))

def gammaCompanionLabel (U : GammaRVObject B k) (u : rvObjectDomain U.object) : GammaCompanionPoint M k :=
  some ⟨rvObjectArity U.object,u.val,gammaVolumeValue U u⟩

def gammaCompanionSet (U : GammaRVObject B k) : Set (GammaCompanionPoint M k) :=
  Set.range (gammaCompanionLabel U)

theorem gammaCompanionLabel_injective (U : GammaRVObject B k) : Function.Injective (gammaCompanionLabel U) := by
  intro u v h
  apply Subtype.ext
  have hp := eq_of_heq (Sigma.mk.inj_iff.mp (Option.some.inj h)).2
  exact congrArg Prod.fst hp

theorem gammaRVScissor_iff_companions (U V W X : GammaRVObject B k) :
    GammaRVScissor U V W X ↔
      rvObjectArity U.object = rvObjectArity V.object ∧
      rvObjectArity U.object = rvObjectArity W.object ∧
      rvObjectArity U.object = rvObjectArity X.object ∧
      gammaCompanionSet W = gammaCompanionSet U ∪ gammaCompanionSet V ∧
      gammaCompanionSet X = gammaCompanionSet U ∩ gammaCompanionSet V := Iff.rfl

end IntegrationInACVF.Section6
