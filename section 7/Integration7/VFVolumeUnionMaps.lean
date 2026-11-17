module

public import Integration7.MixedJacobianRestriction
public import Integration7.VolumeFormGluing

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Volume equations glue over disjoint definable domains. Differentiability
of the glued map is supplied independently outside a smaller VF set. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b : ℕ}

theorem preservesVFVolume_union
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (hn : 0 < n)
    {A B : DefSet (rawMixedSpace (M := M) n a) (C.base : Set M)}
    {D : DefSet (rawMixedSpace (M := M) n b) (C.base : Set M)}
    (hAB : Disjoint A.carrier B.carrier) (f : Map A D) (g : Map B D)
    (ω : VolumeForm A) (η : VolumeForm B) (π : VolumeForm D)
    (hf : PreservesVFVolume ω π f) (hg : PreservesVFVolume η π g) :
    PreservesVFVolume (ω.union η) π (f.union g) := by
  letI : CharZero (VFType (M := M)) := Section6.vfCharZero_of_model00 C.model00
  obtain ⟨E,hEA,hdE,hE⟩ := hf
  obtain ⟨F,hFB,hdF,hF⟩ := hg
  have hEquation : VFAlmostEverywhere (A.union B) (fun p =>
      ∀ J : VFType (M := M), HasMixedVFJacobianAt (f.union g) p J →
        (ω.union η).value p = π.value ((f.union g) p) * CanonicalRV.encodedRv J) := by
    refine ⟨E.union F, Set.union_subset_union hEA hFB, ?_, ?_⟩
    · rw [vfDim_union hc C.saturated C.small _ (rawRVSpace_rvCoded 1)]
      exact max_lt hdE hdF
    · intro p hp J hJ
      rcases p.property with hpA | hpB
      · let q : A := ⟨p.val,hpA⟩
        obtain ⟨K,hK,hω⟩ := hE q (fun he => hp (Or.inl he))
        have he := mixedVFJacobian_eq_of_restriction Set.subset_union_left (f.union g) f
          (fun u => congrArg Subtype.val (Map.union_on_left f g u)) q hJ hK
        change (ω.union η).value ⟨q.val,Or.inl q.property⟩ =
          π.value ((f.union g) ⟨q.val,Or.inl q.property⟩) * CanonicalRV.encodedRv J
        rw [VolumeForm.union_value_left, Map.union_on_left, he]
        exact hω
      · let q : B := ⟨p.val,hpB⟩
        obtain ⟨K,hK,hω⟩ := hF q (fun he => hp (Or.inr he))
        have he := mixedVFJacobian_eq_of_restriction Set.subset_union_right (f.union g) g
          (fun u => congrArg Subtype.val (Map.union_on_right f g hAB u)) q hJ hK
        change (ω.union η).value ⟨q.val,Or.inr q.property⟩ =
          π.value ((f.union g) ⟨q.val,Or.inr q.property⟩) * CanonicalRV.encodedRv J
        rw [VolumeForm.union_value_right ω η hAB, Map.union_on_right f g hAB, he]
        exact hω
  obtain ⟨D,hD,hd,hJac⟩ := lemma_9_12_ae hc C.uncountable.le C.saturated C.small hn
    (Map.id (A.union B)) (f.union g) (Map.finiteFibres_of_injective Function.injective_id)
  have hDiff : VFAlmostEverywhere (A.union B) (fun p => ∃ J : VFType (M := M),
      HasMixedVFJacobianAt (f.union g) p J) := by
    refine ⟨D,hD,hd,?_⟩
    intro p hp
    obtain ⟨_,J,_,hJ,_⟩ := hJac p hp
    exact ⟨J,hJ⟩
  apply (vfAlmostEverywhere_and hc C hEquation hDiff).mono
  rintro p ⟨hEq,J,hJ⟩
  exact ⟨J,hJ,hEq J hJ⟩

end IntegrationInACVF.Section7
