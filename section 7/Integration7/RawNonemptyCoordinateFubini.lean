import Integration7.StrictGradedVolumeFubini

/-! Raw Fubini on all finite graded functions for each nonempty coordinate
set. The full coordinate set uses its original coordinate order and the
identity operator; a proper subset uses the specified retained enumeration
and the signed geometric coordinate integral. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language Classical
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open scoped DirectSum
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

def rawNonemptyVolumeCoordinateDimension (E : Set (Fin (n+1))) : ℕ :=
  if E=Set.univ then n else (Fintype.card E).pred

theorem proper_nonempty_volume_projection_discards (E : Set (Fin (n+1)))
    (hE : E.Nonempty) (hProper : E≠Set.univ) :
    0<(nonemptyVolumeCoordinateProjection E hE).discarded := by
  change 0<Fintype.card (Eᶜ : Set (Fin (n+1)))
  have h : (Eᶜ : Set (Fin (n+1))).Nonempty := by
    by_contra h
    apply hProper
    apply Set.eq_univ_of_forall
    intro i
    by_contra hi
    exact h ⟨i,hi⟩
  obtain ⟨i,hi⟩ := h
  letI : Nonempty (Eᶜ : Set (Fin (n+1))) := ⟨⟨i,hi⟩⟩
  exact Fintype.card_pos

variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

def rawNonemptyVolumeCoordinatePushforward (E : Set (Fin (n+1))) (hE : E.Nonempty) :
    GradedAEVolumeFunction hc C n →ₗ[RVVolumeBlowupSemiring hc C]
      GradedAEVolumeFunction hc C (rawNonemptyVolumeCoordinateDimension E) := by
  by_cases h : E=Set.univ
  · exact (gradedAEVolumeBaseEquiv hc C (show rawNonemptyVolumeCoordinateDimension E=n by
      simp [rawNonemptyVolumeCoordinateDimension,h])).toLinearMap
  · exact (gradedAEVolumeBaseEquiv hc C (show rawNonemptyVolumeCoordinateDimension E=(Fintype.card E).pred by
      simp [rawNonemptyVolumeCoordinateDimension,h])).toLinearMap.comp
      ((positiveGradedAEVolumeInclusion hc C _).comp
        (strictGradedAEVolumeSignedCoordinatePushforward hc C Ξ hΞ hGenerated hNames γ hγ hγ1
          (nonemptyVolumeCoordinateProjection E hE) (proper_nonempty_volume_projection_discards E hE h)))

theorem raw_nonempty_coordinate_integral_eq_total
    (E : Set (Fin (n+1))) (hE : E.Nonempty) (f : GradedAEVolumeFunction hc C n) :
    gradedAEVolumeIntegralLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 _
      (rawNonemptyVolumeCoordinatePushforward hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E hE f) =
      gradedAEVolumeIntegralLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n f := by
  by_cases h : E=Set.univ
  · simp only [rawNonemptyVolumeCoordinatePushforward,dif_pos h]
    exact graded_ae_volume_integral_base_equiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1 _ f
  · simp only [rawNonemptyVolumeCoordinatePushforward,dif_neg h,LinearMap.comp_apply]
    exact (graded_ae_volume_integral_base_equiv hc C Ξ hΞ hGenerated hNames γ hγ hγ1
      (show rawNonemptyVolumeCoordinateDimension E=(Fintype.card E).pred by
        simp [rawNonemptyVolumeCoordinateDimension,h]) _).trans
      (strict_graded_signed_coordinate_integral_eq_total hc C Ξ hΞ hGenerated hNames γ hγ hγ1
        (nonemptyVolumeCoordinateProjection E hE) (proper_nonempty_volume_projection_discards E hE h) f)

theorem raw_nonempty_coordinate_volume_fubini
    (E D : Set (Fin (n+1))) (hE : E.Nonempty) (hD : D.Nonempty) (f : GradedAEVolumeFunction hc C n) :
    gradedAEVolumeIntegralLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 _
      (rawNonemptyVolumeCoordinatePushforward hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E hE f) =
    gradedAEVolumeIntegralLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 _
      (rawNonemptyVolumeCoordinatePushforward hc C Ξ hΞ hGenerated hNames γ hγ hγ1 D hD f) :=
  (raw_nonempty_coordinate_integral_eq_total hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E hE f).trans
    (raw_nonempty_coordinate_integral_eq_total hc C Ξ hΞ hGenerated hNames γ hγ hγ1 D hD f).symm
end IntegrationInACVF.Section7
