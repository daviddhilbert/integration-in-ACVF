import Integration7.UniformPreparedKeyFibres
import Integration7.NativeRectangleFamilyStandardContractions
import Integration7.RectangleFamilyAllOrderComparisons

/-! The different-ball part is an actual original-Gamma rectangle
family after recording the two prepared keys. Its specified contractions
therefore have the proved full volume comparison in either VF order. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section4 IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)}

theorem gamma_rv_graph_refinement_rectangular {S : Set M} {m d : ℕ}
    (A : DefSet (M := M) S 2 m) (P : GammaRVMap G (carrier A) d)
    (hNames : commonRealNames G ⊆ S)
    (hReflect : ∀ a b : A, P.toFun a = P.toFun b → a.val.2 = b.val.2)
    (hRect : ∀ a : A, mixedPairFibre P a = Cells.first (mixedPairFibre P a) ×ˢ
      Cells.second (mixedPairFibre P a)) :
    RectangularRVFibres (carrier (gammaRVGraphRefinement A P hNames)) := by
  apply rectangular_rv_fibres_of_mix
  intro p q hRV
  obtain ⟨a,rfl⟩ := (gamma_rv_graph_refinement_bijective A P hNames).2 p
  obtain ⟨b,rfl⟩ := (gamma_rv_graph_refinement_bijective A P hNames).2 q
  have hP : P.toFun b = P.toFun a := by
    funext i
    have hi := congrFun hRV (Fin.natAdd m i)
    change Fin.append a.val.2 (P.toFun a) (Fin.natAdd m i) =
      Fin.append b.val.2 (P.toFun b) (Fin.natAdd m i) at hi
    simpa only [Fin.append_right] using hi.symm
  have own (c : A) (hc : P.toFun c = P.toFun a) :
      (vfAt c.val 1,vfAt c.val 0) ∈ mixedPairFibre P a := by
    refine ⟨c,?_,hc⟩
    funext i
    fin_cases i <;> rfl
  have hMix := (relation_eq_projection_product_iff _).mp (hRect a)
    _ (own b hP) _ (own a rfl)
  obtain ⟨c,hVF,hPc⟩ := hMix
  refine ⟨c,?_⟩
  apply Prod.ext
  · exact hVF
  · exact congrArg₂ Fin.append (hReflect c a hPc) hPc

namespace UniformBalancedPositionPreparation
variable {m : ℕ} {C : BaseContext M} {A : DefSet (M := M) (C.base : Set M) 2 m}
variable {F : UniformMixedCellPresentation G (carrier A)} {hBalanced : F.BalancedRows}
variable {hNames : commonRealNames G ⊆ (C.base : Set M)}

def differentNative (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    DefSet (M := M) (C.base : Set M) 2 (m+F.arity) :=
  PresentedSet.mk P.differentPart (SetDefinable.mono _
    (gamma_native_set_common_names P.different_part_gamma) hNames)

def differentPreparedFamily (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    DefSet (M := M) (C.base : Set M) 2
      ((m+F.arity)+((1+P.sourceArity)+(1+P.targetArity))) :=
  gammaRVGraphRefinement P.differentNative P.differentKeyLabels hNames

theorem different_prepared_family_gamma (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    GammaSetDefinable G (carrier P.differentPreparedFamily) :=
  gamma_rv_graph_refinement_target_gamma P.differentNative P.differentKeyLabels hNames

theorem different_prepared_family_finite_labels
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (hfin : ∀ x : Fin 2 → VF (M := M), {r : Fin m → RV (M := M) | (x,r) ∈ carrier A}.Finite) :
    ∀ x : Fin 2 → VF (M := M),
      {r | (x,r) ∈ carrier P.differentPreparedFamily}.Finite := by
  apply gamma_rv_graph_refinement_finite_labels
  intro x
  exact (gamma_rv_graph_refinement_finite_labels A hfin F.parameters hNames x).subset
    (fun r hr => hr.1)

theorem different_prepared_family_rectangular
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    RectangularRVFibres (carrier P.differentPreparedFamily) := by
  apply gamma_rv_graph_refinement_rectangular
  · intro a b he
    exact ((P.pair_key_labels_iff_bodies ⟨b.val,b.property.1⟩ ⟨a.val,a.property.1⟩).mp he).1
  · exact P.different_key_fibre_rectangular

theorem different_prepared_family_contractions_compare
    (hc : CanonicalStructure.IsCanonical (M := M))
    (hgamma : Cardinal.mk G.gamma < C.κ)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ G.gamma) (hγ1 : 1 < γ)
    (hGC : G.real ⊆ (C.base : Set M))
    (hGeneric : ∀ {p : ℕ} (x : Fin p → VF (M := M)), AlgebraicIndependent (vfParameterField G.real) x →
      AlgebraicIndependent (vfParameterField (C.base : Set M)) x)
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (hfin : ∀ x : Fin 2 → VF (M := M), {r : Fin m → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (δ : Fin ((m+F.arity)+((1+P.sourceArity)+(1+P.targetArity))))
    (hδ : ∀ p : P.differentPreparedFamily, (p.val.2 δ).val ≠ iRVZero)
    {σ τ : Equiv.Perm (Fin 2)}
    (T : StandardContraction P.differentPreparedFamily σ) (W : StandardContraction P.differentPreparedFamily τ)
    (hT : GammaProgramDefinable G T.program) (hW : GammaProgramDefinable G W.program) :
    let hreal : Cardinal.mk G.real < C.κ := (Cardinal.mk_le_mk_of_subset hGC).trans_lt C.small
    let Z := P.differentPreparedFamily
    let hZ := P.different_prepared_family_gamma
    let hfinZ := P.different_prepared_family_finite_labels hfin
    ∃ D : BaseContext M, ∃ hCD : (C.base : Set M) ⊆ (D.base : Set M),
      GammaVolumeBlowupEquivalent G (D.base : Set M) 1
        ((retainedDensityContractionGammaObject C.uncountable.le C.saturated hreal hc C hGC Z hZ hfinZ δ hδ T hT).extend hCD)
        ((retainedDensityContractionGammaObject C.uncountable.le C.saturated hreal hc C hGC Z hZ hfinZ δ hδ W hW).extend hCD) :=
  rectangle_family_contractions_compare hc C hgamma γ hγ hγ1 hGC hNames hGeneric _
    P.different_prepared_family_gamma (P.different_prepared_family_finite_labels hfin)
    P.different_prepared_family_rectangular δ hδ T W hT hW

end UniformBalancedPositionPreparation
end IntegrationInACVF.Section7
