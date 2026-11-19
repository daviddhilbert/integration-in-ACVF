import Integration7.GammaFunAppendedAdditivity
import Integration7.SmallDimensionVolumeContractions
import Integration7.EmptyPullbackVolumeObjects

/-! The Gamma-named integrals of positive almost-everywhere functions are additive monoid
homomorphisms: the empty presentation has integral zero, and integrals of sums are sums. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput carrier)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.GammaFun
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n k : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (gammaNamedBase C Ξ))

set_option quotPrecheck false
local notation "𝔅" => gammaNamedBase C Ξ
local notation "𝔇" => gammaNamedCodeContext C Ξ hΞ
local notation "𝔖" => ((gammaNamedCodeContext C Ξ hΞ).base : Set M)

variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

set_option maxHeartbeats 2400000 in
include hγ hγ1 in
/-- **The empty presentation has Gamma-named integral zero.** -/
theorem presentation_integral_zero (n k : ℕ) :
    (Presentation.zero C Ξ hΞ n k).integral hc C Ξ hΞ hGenerated = 0 := by
  let F := Presentation.zero C Ξ hΞ n k
  let A := nativeMixedVolumeDomain hc F.family.densityGraph.domain
  have hA : GammaSetDefinable 𝔅 (carrier A) := F.gamma.native_domain hc
  have hW := realization_gamma hc C Ξ hΞ A hA F.family.densityGraph.selected F.family.densityGraph.finite_selected
    (Fin.last F.arity) F.family.densityGraph_label_nonzero
  let W := selectedCoordinateVolumeRealization hc A F.family.densityGraph.selected
    F.family.densityGraph.finite_selected (Fin.last F.arity) F.family.densityGraph_label_nonzero
  have hBC := gamma_named_code_context_base C Ξ hΞ
  have hreal := small_gamma_named_real C Ξ hΞ
  obtain ⟨EW,hEW,_,_,_⟩ := generated_base_standard_contraction_exists (B := 𝔅) (𝔇).saturated (𝔇).model00
    hreal hGenerated hBC (nativeMixedVolumeDomain hc W.densityGraph.domain) hW.densityGraph (Equiv.refl _)
  have hNames := gamma_named_code_context_names C Ξ hΞ
  have hGeneric : ∀ {p : ℕ} (x : Fin p → SpecialTransformations.Section5.VF (M := M)),
      AlgebraicIndependent (vfParameterField (𝔅).real) x → AlgebraicIndependent (vfParameterField 𝔖) x :=
    fun x hx => gamma_named_code_context_generic C Ξ hΞ hc x hx
  have h1 := GammaNamed.gamma_selected_realization_contraction hc 𝔇 𝔅 hBC hΞ hGenerated hNames hGeneric γ hγ hγ1
    A hA F.family.densityGraph.selected F.family.densityGraph.finite_selected (Fin.last F.arity)
    F.family.densityGraph_label_nonzero
    (F.contraction hc C Ξ hΞ hGenerated) (F.contraction_gamma hc C Ξ hΞ hGenerated) hW EW hEW
  have hEmpty : W.domain = SpecialTransformations.DefinableGeometry.DefSet.empty _ _ := by
    apply SpecialTransformations.DefinableGeometry.DefSet.eq_of_carrier_eq
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro p hp
    have h := ((GammaNamed.selected_realization_mem hc A F.family.densityGraph.selected
      F.family.densityGraph.finite_selected (Fin.last F.arity) F.family.densityGraph_label_nonzero p).mp hp).1
    change _ ∈ carrier (nativeMixedVolumeDomain hc F.family.densityGraph.domain) at h
    rw [nativeMixedVolumeDomain_carrier] at h
    exact ((mem_volumeDensityGraph_iff _ _).mp h).1
  have hSmall : SpecialTransformations.Section4.vfDim (SpecialTransformations.Section4.rawRVSpace (M := M) 1)
      W.domain < ((k+1)+n)+1 := by
    rw [hEmpty]
    exact (SpecialTransformations.DefinableGeometry.Dimension.dim_empty SpecialTransformations.Section4.rawVFSpace
      (SpecialTransformations.Section4.AuxiliaryCoordinates.space (SpecialTransformations.Section4.rawRVSpace (M := M) 1))
      (.rv W.arity)).trans_lt (Nat.zero_lt_succ _)
  have hEss := standard_volume_contraction_essential_empty_of_small_dimension hc 𝔇 (𝔅).gamma W hSmall EW
  have hE0 : (GammaVolumeObjects.empty 𝔅 𝔖 ((k+1)+n)).val.essential.obj.domain.carrier = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro r hr
    obtain ⟨p,_⟩ := rvEssentialLabels_subset _ hr
  have h2 := CommonContextVolumeEquivalent.of_empty_essential hc 𝔇
    ⟨W.standardContractionObject hc 𝔇 (𝔅).gamma EW,GammaNamed.standard_contraction_object_gamma hc 𝔇 𝔅 hBC _ hW EW hEW⟩
    (GammaVolumeObjects.empty 𝔅 𝔖 ((k+1)+n)) hEss hE0
  exact (gammaVolumeBlowupClass_eq_iff hc 𝔇 𝔅).mpr ((h1.trans hc h2).descend hc 𝔇 hNames)

include hγ hγ1 in
theorem presentation_appended_integral_zero (n k : ℕ) :
    (Presentation.zero C Ξ hΞ n k).appendedIntegral hc C Ξ hΞ hGenerated = 0 := by
  rw [presentation_appended_integral_eq_permute,presentation_integral_zero hc C Ξ hΞ hGenerated γ hγ hγ1]
  let X := ((GammaVolumeObjects.empty 𝔅 𝔖 ((k+1)+n)).reindexDegree (selected_append_degree_eq n k)).permuteVolume
    hc 𝔇 (appendedToOriginalVolumePermutation (n+1) k).symm
  change gammaVolumeBlowupClass hc 𝔇 𝔅 X = gammaVolumeBlowupClass hc 𝔇 𝔅 (GammaVolumeObjects.empty 𝔅 𝔖 _)
  have hX : X.val.essential.obj.domain.carrier = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro r hr
    obtain ⟨p,_⟩ := rvEssentialLabels_subset _ hr
  have hE0 : (GammaVolumeObjects.empty 𝔅 𝔖 (appendVolumeDegree (n+1) k)).val.essential.obj.domain.carrier = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro r hr
    obtain ⟨p,_⟩ := rvEssentialLabels_subset _ hr
  exact (gammaVolumeBlowupClass_eq_iff hc 𝔇 𝔅).mpr
    ((CommonContextVolumeEquivalent.of_empty_essential hc 𝔇 _ _ hX hE0).descend hc 𝔇
      (gamma_named_code_context_names C Ξ hΞ))

/-- **The Gamma-named integral as an additive monoid homomorphism.** -/
def aeIntegralAddHom (n k : ℕ) : AEFunction hc C Ξ hΞ n k →+ HK.GammaNamedRVClasses hc C Ξ hΞ (((k+1)+n)+1) where
  toFun := aeIntegral hc C Ξ hΞ hGenerated γ hγ hγ1
  map_zero' := presentation_integral_zero hc C Ξ hΞ hGenerated γ hγ hγ1 n k
  map_add' f g := Quotient.inductionOn₂ f g (fun F H => presentation_integral_add hc C Ξ hΞ hGenerated γ hγ hγ1 F H)

theorem ae_integral_add_hom_apply (f : AEFunction hc C Ξ hΞ n k) :
    aeIntegralAddHom hc C Ξ hΞ hGenerated γ hγ hγ1 n k f = aeIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 f := rfl

/-- **The appended Gamma-named integral as an additive monoid homomorphism.** -/
def aeAppendedIntegralAddHom (n k : ℕ) :
    AEFunction hc C Ξ hΞ n k →+ GammaVolumeBlowupClasses hc 𝔇 𝔅 (appendVolumeDegree (n+1) k) where
  toFun := aeAppendedIntegral hc C Ξ hΞ hGenerated γ hγ hγ1
  map_zero' := presentation_appended_integral_zero hc C Ξ hΞ hGenerated γ hγ hγ1 n k
  map_add' f g := Quotient.inductionOn₂ f g
    (fun F H => presentation_appended_integral_add hc C Ξ hΞ hGenerated γ hγ hγ1 F H)

theorem ae_appended_integral_add_hom_apply (f : AEFunction hc C Ξ hΞ n k) :
    aeAppendedIntegralAddHom hc C Ξ hΞ hGenerated γ hγ hγ1 n k f =
      aeAppendedIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 f := rfl

/-- **The semiring-valued Gamma-named integral as an additive monoid homomorphism.** -/
def gammaSemiringIntegralAddHom (n k : ℕ) : AEFunction hc C Ξ hΞ n k →+ HK.GammaNamedRVSemiring hc C Ξ hΞ :=
  (DirectSum.of (HK.GammaNamedRVClasses hc C Ξ hΞ) (appendVolumeDegree (n+1) k + 1)).comp
    (aeAppendedIntegralAddHom hc C Ξ hΞ hGenerated γ hγ hγ1 n k)

theorem gamma_semiring_integral_add_hom_apply (f : AEFunction hc C Ξ hΞ n k) :
    gammaSemiringIntegralAddHom hc C Ξ hΞ hGenerated γ hγ hγ1 n k f =
      gammaSemiringIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 f := rfl

theorem gamma_semiring_integral_add (f g : AEFunction hc C Ξ hΞ n k) :
    gammaSemiringIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 (f+g) =
      gammaSemiringIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 f + gammaSemiringIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 g :=
  (gammaSemiringIntegralAddHom hc C Ξ hΞ hGenerated γ hγ hγ1 n k).map_add f g

theorem gamma_semiring_integral_zero (n k : ℕ) :
    gammaSemiringIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 (0 : AEFunction hc C Ξ hΞ n k) = 0 :=
  (gammaSemiringIntegralAddHom hc C Ξ hΞ hGenerated γ hγ hγ1 n k).map_zero

end IntegrationInACVF.Section7.GammaFun
