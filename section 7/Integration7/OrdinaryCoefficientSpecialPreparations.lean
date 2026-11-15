import Integration7.OrdinaryRVNativePresentations
import Integration7.IndependentRVSpecialSources
import Integration7.SelectedVolumeFamilyZeroProducts

/-! An ordinary finite coefficient can be retained through a specified
unary special preparation on the original family product, without a
second density graph or any extra volume coordinate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {a b k : ℕ}

theorem ordinary_coefficient_special_preparation_exists
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (F : SelectedVFVolumeFamily C 1 a k) (Z : SpecialTransformations.Section4.RVFiniteObject (M := M) (C.base : Set M) 0)
    {B : DefSet (M := M) (C.base : Set M) 1 b}
    (T : SpecialBijection (nativeMixedVolumeDomain hc F.domain) B)
    (hT : GammaChainDefinable (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) T.chain)
    (hB : IsRVPullback (carrier B)) :
    Nonempty (RVLabelConstraintSpecialPreparation T (nativeMixedVolumeDomain hc (F.prodZero Z).domain)
      (independentRVLabelConstraint C Ξ hNames a (ordinaryRVNativeDomain hc C Z))
      (Fin.castAdd Z.obj.arity) (⟨(C.base : Set M),Ξ⟩ : Base (M := M))) := by
  let P : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
  let H := nativeMixedVolumeDomain hc (F.prodZero Z).domain
  apply gamma_rv_label_constraint_special_preparation_exists T hT hB H
    ((gammaLogicInput P).real_set _ (setDefinable H)) _ (Fin.castAdd Z.obj.arity)
  intro p
  change (p.1,p.2) ∈ (mixedRVFactorDomain F.domain Z.obj.domain).carrier ↔ _
  rw [mem_mixed_rv_factor_domain,independent_rv_label_constraint_mem]
  apply and_congr Iff.rfl
  exact (Set.ext_iff.mp (ordinary_rv_native_labels_carrier hc C Z) _).symm.trans
    (mem_rawVolumeContractionLabels hc (ordinaryRVNativeDomain hc C Z) _)
end IntegrationInACVF.Section7
