module

public import Integration7.HKGradedAEVolumeJacobians
public import Integration7.HKGradedAEVolumePrefixFubini
public import Integration7.VolumeCoordinateProjectionOrders
public import Integration7.NonemptyVolumeCoordinateProjections

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Actual integration over any discarded coordinate set, with a
nonempty retained base. A global Jacobian permutation places the discarded
coordinates first; genuine head integrals then integrate that prefix. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n p q : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

def gradedAEVolumeBaseEquiv {a b : ℕ} (h : a=b) :
    GradedAEVolumeFunction hc C b ≃+ GradedAEVolumeFunction hc C a := by
  cases h
  exact AddEquiv.refl _

variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

theorem graded_ae_volume_integral_base_equiv {a b : ℕ} (h : a=b)
    (f : GradedAEVolumeFunction hc C b) :
    gradedAEVolumeIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 a
      (gradedAEVolumeBaseEquiv hc C h f) =
      gradedAEVolumeIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 b f := by
  cases h
  rfl

def gradedAEVolumeCoordinateIntegralAddHom (E : VFCoordinateProjection (n+1) (p+1)) :
    GradedAEVolumeFunction hc C n →+ GradedAEVolumeFunction hc C p :=
  (gradedAEVolumePrefixIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E.discarded p).comp
    ((gradedAEVolumeCoordinatePermutationAddHom hc C (volumeProjectionFibreOrder E)).comp
      (gradedAEVolumeBaseEquiv hc C (volume_projection_index_eq E)).toAddMonoidHom)

theorem graded_coordinate_integral_eq_total
    (E : VFCoordinateProjection (n+1) (p+1)) (f : GradedAEVolumeFunction hc C n) :
    gradedAEVolumeIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 p
      (gradedAEVolumeCoordinateIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E f) =
      gradedAEVolumeIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n f := by
  change gradedAEVolumeIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 p
    (gradedAEVolumePrefixIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E.discarded p
      (gradedAEVolumeCoordinatePermutationAddHom hc C (volumeProjectionFibreOrder E)
        (gradedAEVolumeBaseEquiv hc C (volume_projection_index_eq E) f))) = _
  rw [graded_ae_volume_prefix_fubini,graded_ae_volume_coordinate_permutation_integral,
    graded_ae_volume_integral_base_equiv]

theorem graded_volume_fubini
    (E : VFCoordinateProjection (n+1) (p+1)) (D : VFCoordinateProjection (n+1) (q+1))
    (f : GradedAEVolumeFunction hc C n) :
    gradedAEVolumeIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 p
      (gradedAEVolumeCoordinateIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E f) =
    gradedAEVolumeIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 q
      (gradedAEVolumeCoordinateIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 D f) :=
  (graded_coordinate_integral_eq_total hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E f).trans
    (graded_coordinate_integral_eq_total hc C Ξ hΞ hGenerated hNames γ hγ hγ1 D f).symm

theorem graded_nonempty_coordinate_integral
    (E : Set (Fin (n+1))) (hE : E.Nonempty) (f : GradedAEVolumeFunction hc C n) :
    gradedAEVolumeIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 ((Fintype.card E).pred)
      (gradedAEVolumeCoordinateIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1
        (nonemptyVolumeCoordinateProjection E hE) f) =
      gradedAEVolumeIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n f :=
  graded_coordinate_integral_eq_total hc C Ξ hΞ hGenerated hNames γ hγ hγ1 _ f

end IntegrationInACVF.Section7.HK
