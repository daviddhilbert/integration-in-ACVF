module

public import Integration7.NativeRectangleFamilyHeadPreparations
public import Integration7.GammaNativeUnaryProductMaps
public import Integration7.UnaryPullbackCommonNamePreparations

@[expose] public section

/-! The rectangle-family head preparation has its complete original-
Gamma graph, with actual unary preparations over the fixed common names. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S : Set M} {m r : ℕ}

theorem gamma_native_head_projection (H : DefSet (M := M) S 2 m) (hH : GammaSetDefinable G (carrier H)) :
    GammaSetDefinable G (carrier (Map.image (coordinateProjectMap 0 H))) := by
  have h := (gammaLogicInput G).image_graph (gamma_native_coordinate_project_graph H hH 0)
  convert h using 1
  ext q
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨a.val,a,rfl,ha⟩
  · rintro ⟨p,a,rfl,ha⟩
    exact ⟨a,ha⟩

theorem rectangle_family_head_preparation_map_gamma
    (H : DefSet (M := M) S 2 m) (hH : GammaSetDefinable G (carrier H)) (hRect : RectangularRVFibres (carrier H))
    {D : DefSet (M := M) S 1 r} (T : SpecialBijection (Map.image (coordinateProjectMap 0 H)) D)
    (hT : GammaChainDefinable G T.chain) (hD : IsRVPullback (carrier D)) :
    GammaGraphDefinable G (pointMapGraph (rectangleFamilyHeadPreparation H hRect T hD).map) := by
  let U := PresentedSet.univ (pointSpace (M := M) 1 0) S
  have hU : GammaSetDefinable G (carrier U) :=
    (gammaLogicInput G).real_set _ (setDefinable (PresentedSet.univ (pointSpace (M := M) 1 0) G.real))
  let g := nativeUnaryProductMap T.toMap U
  have hg := gamma_native_unary_product_map T.toMap U (gamma_native_head_projection H hH) hU
    (GammaChainDefinable.graph (gammaLogicInput G) T.chain hT)
  apply GammaGraphDefinable.congr ((gammaLogicInput G).restrict_graph hH hg)
  intro p q
  constructor
  · rintro ⟨hp,a,ha,hq⟩
    have he : (⟨p,rectangle_family_ambient_source_subset H hp⟩ : nativeUnaryProductDomain (Map.image (coordinateProjectMap 0 H)) U) = a :=
      Subtype.ext ha.symm
    exact ⟨⟨p,hp⟩,rfl,(congrArg (fun a => (g a).val) he).trans hq⟩
  · rintro ⟨a,rfl,ha⟩
    exact ⟨a.property,⟨a.val,rectangle_family_ambient_source_subset H a.property⟩,rfl,ha⟩

theorem rectangle_family_head_preparation_target_gamma
    (H : DefSet (M := M) S 2 m) (hH : GammaSetDefinable G (carrier H)) (hRect : RectangularRVFibres (carrier H))
    {D : DefSet (M := M) S 1 r} (T : SpecialBijection (Map.image (coordinateProjectMap 0 H)) D)
    (hT : GammaChainDefinable G T.chain) (hD : IsRVPullback (carrier D)) :
    GammaSetDefinable G (carrier (rectangleFamilyHeadPreparation H hRect T hD).target) := by
  have h := (gammaLogicInput G).image_graph (rectangle_family_head_preparation_map_gamma H hH hRect T hT hD)
  convert h using 1
  ext q
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨a.val,a,rfl,ha⟩
  · rintro ⟨p,a,rfl,ha⟩
    exact ⟨a,ha⟩

theorem gamma_rectangle_family_head_preparation_exists (C : BaseContext M)
    (hNames : commonRealNames G ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ G.gamma) (hγ1 : 1 < γ)
    (H : DefSet (M := M) (C.base : Set M) 2 m) (hH : GammaSetDefinable G (carrier H))
    (hRect : RectangularRVFibres (carrier H)) :
    ∃ P : HeadPreparation H, GammaGraphDefinable G (pointMapGraph P.map) ∧ GammaSetDefinable G (carrier P.target) := by
  obtain ⟨r,D,T,hT,hD⟩ := gamma_unary_pullback_preparation_over_common_names C hNames γ hγ hγ1
    (Map.image (coordinateProjectMap 0 H)) (gamma_native_head_projection H hH)
  exact ⟨rectangleFamilyHeadPreparation H hRect T hD,
    rectangle_family_head_preparation_map_gamma H hH hRect T hT hD,
    rectangle_family_head_preparation_target_gamma H hH hRect T hT hD⟩

end IntegrationInACVF.Section7
