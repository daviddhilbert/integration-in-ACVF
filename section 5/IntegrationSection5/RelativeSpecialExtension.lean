import IntegrationSection5.RelativeSpecialBoundary
import Section5.ParameterExtension
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S R : Set M} {n m l : ℕ} {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l}

def extendPointMap (f : Map A B) (hSR : S ⊆ R) : Map (extendBase A hSR) (extendBase B hSR) :=
  @SpecialTransformations.DefinableGeometry.Map.extend LRV M (@CanonicalStructure.normalize M sM)
    (pointSpace n m) (pointSpace n l) S R A B f hSR

theorem coordinateFibre_extendBase_eq (hSR : S ⊆ R) (i : Fin n) (u : Fin n → VF (M := M)) :
    coordinateFibre (extendBase A hSR) i u =
      extendBase (coordinateFibre A i u) (Set.union_subset_union hSR (Set.Subset.refl _)) := rfl

theorem specialRelativeBoundary_extendBase (f : Map A B) (hSR : S ⊆ R) {i : Fin n}
    {previous ending : Option Bool} (hf : SpecialRelativeBoundary f i previous ending) :
    SpecialRelativeBoundary (extendPointMap f hSR) i previous ending := by
  obtain ⟨hi,hT⟩ := hf
  have hiR : UnaryRelative (extendPointMap f hSR) i := fun a j hj => hi ⟨a.val,a.property⟩ j hj
  refine ⟨hiR,?_⟩
  intro u
  obtain ⟨T,hTa,hTe,hT⟩ := hT u
  let hAug : coordinateFibreBase S i u ⊆ coordinateFibreBase R i u :=
    Set.union_subset_union hSR (Set.Subset.refl _)
  refine ⟨T.extendBase hAug,T.chain.extendBase_alternating hAug previous hTa,?_,?_⟩
  · change (T.chain.extendBase hAug).lastKind previous = ending
    rw [Chain.extendBase_lastKind]
    exact hTe
  · intro p
    apply Subtype.ext
    have hval := T.chain.extendBase_apply hAug p
    have he := congrArg (fun q : coordinateFibre B i u => q.val) (hT ⟨p.val,p.property⟩)
    exact hval.trans he
end IntegrationInACVF.Section5
