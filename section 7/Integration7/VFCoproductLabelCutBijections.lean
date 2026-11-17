module

public import Integration7.VFVolumeObjectLabelCuts
public import Integration7.SelectedSumTagPredicates
public import Integration7.FixedVFVolumeCoproducts

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Complementary old-tag cuts of a VF volume coproduct are genuinely
volume-bijective to its summands, preserving every VF coordinate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

def vfCoprodLeftCut (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (U V : PositiveVFVolumeObject (M := M) (C.base : Set M) k) :=
  (U.coprod V).onRVLabels hc C Ξ (fun _ : Fin 1 => (0 : Fin (1+(U.arity+V.arity))))
    (selectedSumLeftTagPredicate hc C) (selected_sum_left_tag_gamma hc C Ξ) hNames

def vfCoprodRightCut (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (U V : PositiveVFVolumeObject (M := M) (C.base : Set M) k) :=
  (U.coprod V).onRVLabels hc C Ξ (fun _ : Fin 1 => (0 : Fin (1+(U.arity+V.arity))))
    (Set.univ \ selectedSumLeftTagPredicate hc C) (selected_sum_right_tag_gamma hc C Ξ) hNames

def vfCoprodLeftCutBijection (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (U V : PositiveVFVolumeObject (M := M) (C.base : Set M) k) :
    VFVolumeBijection U (vfCoprodLeftCut hc C Ξ hNames U V) := by
  let L := vfCoprodLeftCut hc C Ξ hNames U V
  have hTag (u : U.domain) :
      (Fin.elim0,fun _ : Fin 1 => (vfVolumeCoprodLeftMap U V u).val.2 (0 : Fin (1+(U.arity+V.arity)))) ∈ selectedSumLeftTagPredicate hc C :=
    (selected_sum_left_tag_mem hc C _).mpr rfl
  let f : Map U.domain L.domain := (vfVolumeCoprodLeftMap U V).corestrict (fun u =>
    ⟨(vfVolumeCoprodLeftMap U V u).property,hTag u⟩)
  have hf : Function.Bijective f := by
    constructor
    · intro u v h
      exact fixed_vf_left_tag_injective U.domain V.arity
        (Subtype.ext (congrArg (fun q : L.domain => q.val) h))
    · intro q
      let qH : (U.coprod V).domain := ⟨q.val,q.property.1⟩
      rcases vf_volume_coprod_cases U V qH with ⟨u,hu⟩ | ⟨v,hv⟩
      · exact ⟨u,Subtype.ext (congrArg (fun p : (U.coprod V).domain => p.val) hu)⟩
      · have hz := (selected_sum_left_tag_mem hc C _).mp q.property.2
        have he := congrArg (fun p : (U.coprod V).domain => (p.val.2 (0 : Fin (1+(U.arity+V.arity)))).val) hv
        exact (RVCalc.rv_one_ne_zero (M := M) inferInstance (he.trans hz)).elim
  exact VFVolumeBijection.of_preserving_vf_and_density hc C f hf (fun _ => rfl)
    (fun u => (vf_volume_coprod_density_left U V u).symm)

def vfCoprodRightCutBijection (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (U V : PositiveVFVolumeObject (M := M) (C.base : Set M) k) :
    VFVolumeBijection V (vfCoprodRightCut hc C Ξ hNames U V) := by
  let R := vfCoprodRightCut hc C Ξ hNames U V
  have hTag (v : V.domain) :
      (Fin.elim0,fun _ : Fin 1 => (vfVolumeCoprodRightMap U V v).val.2 (0 : Fin (1+(U.arity+V.arity)))) ∉ selectedSumLeftTagPredicate hc C := by
    intro h
    exact RVCalc.rv_one_ne_zero (M := M) inferInstance ((selected_sum_left_tag_mem hc C _).mp h)
  let f : Map V.domain R.domain := (vfVolumeCoprodRightMap U V).corestrict (fun v =>
    ⟨(vfVolumeCoprodRightMap U V v).property,Set.mem_univ _,hTag v⟩)
  have hf : Function.Bijective f := by
    constructor
    · intro u v h
      exact fixed_vf_right_tag_injective V.domain U.arity
        (Subtype.ext (congrArg (fun q : R.domain => q.val) h))
    · intro q
      let qH : (U.coprod V).domain := ⟨q.val,q.property.1⟩
      rcases vf_volume_coprod_cases U V qH with ⟨u,hu⟩ | ⟨v,hv⟩
      · have hz : (q.val.2 (0 : Fin (1+(U.arity+V.arity)))).val=iRVZero := by
          have he := congrArg (fun p : (U.coprod V).domain => (p.val.2 (0 : Fin (1+(U.arity+V.arity)))).val) hu
          exact he.symm
        exact (q.property.2.2 ((selected_sum_left_tag_mem hc C _).mpr hz)).elim
      · exact ⟨v,Subtype.ext (congrArg (fun p : (U.coprod V).domain => p.val) hv)⟩
  exact VFVolumeBijection.of_preserving_vf_and_density hc C f hf (fun _ => rfl)
    (fun v => (vf_volume_coprod_density_right U V v).symm)
end IntegrationInACVF.Section7
