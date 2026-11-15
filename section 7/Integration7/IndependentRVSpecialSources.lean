import Integration7.IndependentRVConstraintHeadMaps
import Integration7.GammaRVLabelCuts
import Integration7.MixedRVFactorDomains
import Integration7.NativeVolumeDomains

/-! Actual original-base product sources and RV constraints for carrying
an independent coefficient through a unary special preparation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5 SpecialTransformations.Section9
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {a b d : ℕ}

def independentRVLabelConstraint (C : BaseContext M) (Ξ : Set (Values.Gamma (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (a : ℕ) (R : DefSet (M := M) (C.base : Set M) 0 d) :
    DefSet (M := M) (C.base : Set M) 0 (a+d) :=
  let P : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
  let U := PresentedSet.univ (pointSpace (M := M) 0 (a+d)) (C.base : Set M)
  rvLabelCut U ((gammaLogicInput P).real_set _ (setDefinable U)) (Fin.natAdd a)
    (carrier R) ((gammaLogicInput P).real_set _ (setDefinable R)) hNames

theorem independent_rv_label_constraint_mem (C : BaseContext M) (Ξ : Set (Values.Gamma (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (a : ℕ) (R : DefSet (M := M) (C.base : Set M) 0 d) (q : Point (M := M) 0 (a+d)) :
    q ∈ carrier (independentRVLabelConstraint C Ξ hNames a R) ↔
      (Fin.elim0,q.2 ∘ Fin.natAdd a) ∈ carrier R := by
  change (q ∈ Set.univ ∧ _) ↔ _
  exact and_iff_right (Set.mem_univ q)

def independentRVProductSource (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M) (A : DefSet (M := M) (C.base : Set M) 1 a)
    (R : DefSet (M := M) (C.base : Set M) 0 d) : DefSet (M := M) (C.base : Set M) 1 (a+d) :=
  nativeMixedVolumeDomain hc (mixedRVFactorDomain (rawSpecialSet hc A) (rawVolumeContractionLabels hc R))

theorem independent_rv_product_source_mem (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M) (A : DefSet (M := M) (C.base : Set M) 1 a)
    (R : DefSet (M := M) (C.base : Set M) 0 d) (p : Point (M := M) 1 (a+d)) :
    p ∈ carrier (independentRVProductSource hc C A R) ↔
      retainVFLabels (Fin.castAdd d) p ∈ carrier A ∧ (Fin.elim0,p.2 ∘ Fin.natAdd a) ∈ carrier R := by
  exact (mem_mixed_rv_factor_domain (rawSpecialSet hc A) (rawVolumeContractionLabels hc R) p.1 p.2).trans
    (and_congr Iff.rfl (mem_rawVolumeContractionLabels hc R _))

theorem independent_rv_special_preparation_exists
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (Ξ : Set (Values.Gamma (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    {A : DefSet (M := M) (C.base : Set M) 1 a} {B : DefSet (M := M) (C.base : Set M) 1 b}
    (T : SpecialBijection A B) (hT : GammaChainDefinable (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) T.chain)
    (hB : IsRVPullback (carrier B)) (R : DefSet (M := M) (C.base : Set M) 0 d) :
    Nonempty (RVLabelConstraintSpecialPreparation T (independentRVProductSource hc C A R)
      (independentRVLabelConstraint C Ξ hNames a R) (Fin.castAdd d) (⟨(C.base : Set M),Ξ⟩ : Base (M := M))) := by
  let P : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
  let H := independentRVProductSource hc C A R
  apply gamma_rv_label_constraint_special_preparation_exists T hT hB H
    ((gammaLogicInput P).real_set _ (setDefinable H)) _ (Fin.castAdd d)
  intro p
  rw [independent_rv_product_source_mem,independent_rv_label_constraint_mem]
end IntegrationInACVF.Section7
