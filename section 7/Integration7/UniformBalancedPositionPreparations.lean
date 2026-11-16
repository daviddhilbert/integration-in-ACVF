module

public import Integration7.UniformBalancedPositionMaps
public import Integration7.UnarySmallContextPreparationWithoutField

@[expose] public section

/-! Compatible special preparation of the actual mixed positioning
bijection of a balanced family. The checked unary construction acts on
the whole labelled family in one genuine small containing context. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section4 IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S : Set M} {m : ℕ}

private theorem gamma_native_image {n a u b : ℕ} {A : DefSet (M := M) S n a}
    {B : DefSet (M := M) S u b} (f : Map A B)
    (hf : GammaGraphDefinable G (pointMapGraph f)) :
    GammaSetDefinable G (carrier (Map.image f)) := by
  have h := (gammaLogicInput G).image_graph hf
  convert h using 1
  ext q
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨a.val,a,rfl,ha⟩
  · rintro ⟨p,a,rfl,ha⟩
    exact ⟨a,ha⟩

namespace UniformMixedCellPresentation
variable {A : DefSet (M := M) S 2 m}

theorem tail_key_image_gamma (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) :
    GammaSetDefinable G (carrier (VerticalOffsets.keyImage (gammaRVGraphRefinement A F.parameters hNames))) :=
  gamma_native_image _ (gamma_native_tail_key_graph _ (gamma_rv_graph_refinement_target_gamma A F.parameters hNames))

theorem position_image_gamma (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) : GammaSetDefinable G (carrier (F.positionImage hNames)) :=
  gamma_native_image _ (F.position_map_gamma hNames)

theorem position_compatible_preparation_exists (C : BaseContext M)
    (hGC : G.real ⊆ (C.base : Set M)) (hNames : commonRealNames G ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ G.gamma) (hγ1 : 1 < γ)
    {A : DefSet (M := M) (C.base : Set M) 2 m} (F : UniformMixedCellPresentation G (carrier A))
    (hBalanced : F.BalancedRows) :
    let K := VerticalOffsets.keyImage (gammaRVGraphRefinement A F.parameters hNames)
    let E := F.positionImage hNames
    let f := Map.toImage (F.positionMap hNames)
    ∃ D : BaseContext M, ∃ hCD : (C.base : Set M) ⊆ (D.base : Set M),
    ∃ r s : ℕ, ∃ K' : DefSet (M := M) (D.base : Set M) 1 r,
      ∃ E' : DefSet (M := M) (D.base : Set M) 1 s,
      ∃ TK : SpecialBijection (extendBase K hCD) K',
      ∃ TE : SpecialBijection (extendBase E hCD) E',
        let fD := @SpecialTransformations.DefinableGeometry.Map.extend LRV M
          (@CanonicalStructure.normalize M sM) (pointSpace 1 (m+F.arity)) (pointSpace 1 (m+F.arity))
          (C.base : Set M) (D.base : Set M) K E f hCD
        GammaChainDefinable G TK.chain ∧ GammaChainDefinable G TE.chain ∧
        IsRVPullback (carrier K') ∧ IsRVPullback (carrier E') ∧
        Contractible (unaryConjugate TK TE fD) ∧
        Contractible (Map.inverse (unaryConjugate TK TE fD)
          (unaryConjugate_bijective TK TE fD (F.position_to_image_bijective hBalanced hNames))) ∧
        GammaGraphDefinable G (pointMapGraph (unaryConjugate TK TE fD)) ∧
        ∃! g : Map (keyImage K') (keyImage E'), Function.Bijective g ∧
          ∀ a : K', g (toKeyImage K' a) = toKeyImage E' (unaryConjugate TK TE fD a) := by
  intro K E f
  exact unary_bijection_preparation_in_context_without_field C G hGC γ hγ hγ1 f
    (F.position_to_image_bijective hBalanced hNames) (F.tail_key_image_gamma hNames)
    (F.position_image_gamma hNames) (F.position_map_gamma hNames)

end UniformMixedCellPresentation
end IntegrationInACVF.Section7
