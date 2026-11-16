module

public import Integration7.SelectedVolumeFamilyLabelCuts
public import Section4.RVLabelCompression

@[expose] public section

/-! The definable zero tag distinguishes the two actual family
coproduct summands; its complement is defined over the same real base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaSetDefinable carrier)
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def selectedSumTagIndex (a b k : ℕ) : Fin 1 → Fin ((1+(a+b))+(k+1)) :=
  fun _ => Fin.castAdd (k+1) (0 : Fin (1+(a+b)))

def selectedSumLeftTagPredicate (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
    Set (Point (M := M) 0 1) :=
  carrier (nativeMixedVolumeDomain hc ((DefSet.univ (rawVFSpace (M := M) 0) (C.base : Set M)).prod
    (zeroLabelsAt (C.base : Set M) (k := 0) 0)))

theorem selected_sum_left_tag_mem (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (p : Point (M := M) 0 1) :
    p ∈ selectedSumLeftTagPredicate hc C ↔ (p.2 0).val=iRVZero := by
  change (p.1 ∈ Set.univ ∧ (p.2 0).val=iRVZero) ↔ _
  exact and_iff_right (Set.mem_univ _)

theorem selected_sum_left_tag_gamma (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) :
    GammaSetDefinable (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) (selectedSumLeftTagPredicate hc C) :=
  (SpecialTransformations.Section5.gammaLogicInput (⟨(C.base : Set M),Ξ⟩ : Base (M := M))).real_set _
    (SpecialTransformations.Section5.setDefinable _)

theorem selected_sum_right_tag_gamma (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) :
    GammaSetDefinable (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) (Set.univ \ selectedSumLeftTagPredicate hc C) := by
  let G : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
  have hAll : GammaSetDefinable G (Set.univ : Set (Point (M := M) 0 1)) :=
    (SpecialTransformations.Section5.gammaLogicInput G).real_set _
      (SpecialTransformations.Section5.setDefinable
        (SpecialTransformations.Section5.PresentedSet.univ (SpecialTransformations.Section5.pointSpace (M := M) 0 1)
          (C.base : Set M)))
  exact (SpecialTransformations.Section5.gammaLogicInput G).sdiff hAll (selected_sum_left_tag_gamma hc C Ξ)
end IntegrationInACVF.Section7
