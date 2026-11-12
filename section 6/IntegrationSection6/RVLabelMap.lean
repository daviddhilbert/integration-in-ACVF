import IntegrationSection6.LiftPresentations

/-! A real-definable RV-label map extends to mixed points by identity
on all VF coordinates, with its complete graph and the same real base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section4.rawVFSpace SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.Section4.rawMixedSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
local notation "N" => (@CanonicalStructure.normalize M sM)

def mapRVLabels (n : ℕ) {d e : ℕ} (S : Set M)
    (F : @SpecialTransformations.DefinableGeometry.Map LRV M N
      (@SpecialTransformations.Section4.rawRVSpace M N d)
      (@SpecialTransformations.Section4.rawRVSpace M N e) S
      (@SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N _ S)
      (@SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N _ S)) :
    Map (PresentedSet.univ (pointSpace n d) S) (PresentedSet.univ (pointSpace n e) S) := by
  let A := PresentedSet.univ (pointSpace (M := M) n d) S
  let P := PresentedSet.univ (rawPointSpace (M := M) n d) S
  let R := rawPointMap A
  let fv := @SpecialTransformations.DefinableGeometry.Map.fst LRV M N
    (@SpecialTransformations.Section4.rawVFSpace M N n)
    (@SpecialTransformations.Section4.rawRVSpace M N d) S P
  let fr := @SpecialTransformations.DefinableGeometry.Map.snd LRV M N
    (@SpecialTransformations.Section4.rawVFSpace M N n)
    (@SpecialTransformations.Section4.rawRVSpace M N d) S P
  let G := Map.pair (Map.comp fv R) (Map.comp F (Map.comp fr R))
  exact Map.comp (fromRawPointMap (PresentedSet.univ (rawPointSpace n e) S))
    (@SpecialTransformations.DefinableGeometry.Map.toUniv LRV M N _ _ S _ _ G)

@[simp] theorem mapRVLabels_value (n : ℕ) {d e : ℕ} (S : Set M)
    (F : @SpecialTransformations.DefinableGeometry.Map LRV M N
      (@SpecialTransformations.Section4.rawRVSpace M N d)
      (@SpecialTransformations.Section4.rawRVSpace M N e) S
      (@SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N _ S)
      (@SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N _ S))
    (a : PresentedSet.univ (pointSpace (M := M) n d) S) :
    (mapRVLabels n S F a).val = (a.val.1,(F ⟨a.val.2,Set.mem_univ _⟩).val) := rfl

end IntegrationInACVF.Section6
