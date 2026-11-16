module

public import Integration7.GammaNativeCommonNames
public import IntegrationSection5.GammaUnaryChain

@[expose] public section

/-! Relatively unary Gamma factorizations are realized over any fixed
real base containing the original common names. Their maps and Gamma
certificates are retained, and no further real context is introduced. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S : Set M} {n a b : ℕ}
variable {A : Set (Point (M := M) n a)} {B : Set (Point (M := M) n b)}

theorem unary_chain_realize_common_names (T : GammaUnaryChain G n A B)
    (hNames : commonRealNames G ⊆ S) :
    ∃ hA : SetDefinable (pointSpace n a) S A,
    ∃ hB : SetDefinable (pointSpace n b) S B,
    ∃ t : UnaryChain S n (PresentedSet.mk A hA) (PresentedSet.mk B hB),
      GammaUnaryChainDefinable G t ∧
        ∀ p : A, (t.toMap p).val = (T.toIso.equiv p).val := by
  induction T with
  | nil A hA =>
    let hAr := SetDefinable.mono _ (gamma_native_set_common_names hA) hNames
    exact ⟨hAr,hAr,.nil _,hA,fun _ => rfl⟩
  | @cons a c b A W B i e hi tail ih =>
    obtain ⟨hW,hB,t,ht,hval⟩ := ih
    let hAΓ := (e.symm (gammaLogicInput G)).target_definable (gammaLogicInput G)
    let hAr := SetDefinable.mono _ (gamma_native_set_common_names hAΓ) hNames
    let f : Map (PresentedSet.mk A hAr) (PresentedSet.mk W hW) :=
      @SpecialTransformations.DefinableGeometry.Map.mk LRV M (@CanonicalStructure.normalize M sM)
        _ _ S _ _ e.equiv
        (RelationDefinable.mono _ _ (gamma_native_graph_common_names e.graph) hNames)
    refine ⟨hAr,hB,.cons i f e.equiv.bijective hi t,⟨e.graph,ht⟩,?_⟩
    intro p
    exact hval (e.equiv p)

end IntegrationInACVF.Section7
